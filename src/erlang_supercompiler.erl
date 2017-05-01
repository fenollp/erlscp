%% -*- coding: utf-8; mode: erlang -*-

%% Copyright (C) 2012-2013, 2017 Göran Weinholt <goran@weinholt.se>

%% Permission is hereby granted, free of charge, to any person obtaining a
%% copy of this software and associated documentation files (the "Software"),
%% to deal in the Software without restriction, including without limitation
%% the rights to use, copy, modify, merge, publish, distribute, sublicense,
%% and/or sell copies of the Software, and to permit persons to whom the
%% Software is furnished to do so, subject to the following conditions:

%% The above copyright notice and this permission notice shall be included in
%% all copies or substantial portions of the Software.

%% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
%% IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
%% FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
%% THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
%% LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
%% FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
%% DEALINGS IN THE SOFTWARE.

-module(erlang_supercompiler).
-export([parse_transform/2]).
-ignore_xref([parse_transform/2]).

-include("scp.hrl").

stdfuns() ->
    [%% Used for list comprehensions.
     "flat1map(_,[]) -> [];\n"
     "flat1map(F,[X|Xs]) -> F(X) ++ flat1map(F, Xs)."
     %% Used for L ++ R.
    ,"append([],Ys) -> Ys;\n"
     "append([X|Xs],Ys) -> [X|append(Xs,Ys)]."
     %% Inlining of lists:foldl/3.
    ,"foldl(F, Acc, List) ->\n"
     "    case List of\n"
     "        [] when is_function(F, 2) -> Acc;\n"
     "        [Hd|Tail] ->\n"
     "            foldl(F, F(Hd, Acc), Tail)\n"
     "    end."
     ].

inlined_module_funs() ->
    dict:from_list([{{lists, foldl}, foldl}
                   ]).

parse_transform(Forms0, _Options) ->
    ?DEBUG("Before: ~p~n", [Forms0]),
    {Libnames,Stdforms} = get_stdfuns(#env{seen_vars = function_names(Forms0)}),
    Records = extract_records(Forms0),
    Forms = scp_desugar:forms(Forms0 ++ Stdforms, Libnames, Records, inlined_module_funs()),
    Global = extract_functions(Forms),
    NoWhistling = attrs(no_whistle, Forms),
    Env1 = #env{global = Global
               ,seen_vars = function_names(Forms)
               ,no_whistling = sets:from_list(NoWhistling)
               ,libnames = Libnames
               ,records = Records
               },
    Ret0 = forms(Forms, Env1),
    ?DEBUG("After: ~p~n", [Ret0]),
    Ret = lists:takewhile(fun ({eof,_}) -> false; (_) -> true end, Ret0),
    %%FIXME: do not generate forms after emitting eof in the first place.
    %%Note: this does not happen on R15B03.
    ?DEBUG("Really after: ~p~n", [Ret]),
    Ret.

forms(Forms0, Env) ->
    {Forms, _Env0} = lists:mapfoldl(fun form/2, Env, Forms0),
    lists:flatten(Forms).

form(F={function,_,Name,Arity,_Clauses0}, Env0) ->
    %% TODO: first check if the function is exported (or if all
    %% functions are exported)?
    ?DEBUG("~n~nLooking at function: ~w/~w~n", [Name, Arity]),
    Expr0 = scp_expr:function_to_fun(F),
    Seen = sets:union(Env0#env.seen_vars, erl_syntax_lib:variables(Expr0)),
    Env1 = Env0#env{bound = sets:new()
                   ,seen_vars = Seen
                   ,w=[], ls=[], found=[]
                   ,name = atom_to_list(Name)
                   ,whistle_enabled = not sets:is_element({Name,Arity}, Env0#env.no_whistling)
                   },
    {Env2,Expr1} = scp_expr:alpha_convert(Env1, Expr0),
    {Env,Expr2} = scp_main:drive(Env2, Expr1, []),
    {Expr,Letrecs} = scp_expr:extract_letrecs(Expr2),
    Functions = [scp_expr:fun_to_function(scp_tidy:function(Ex), Na, Ar)
                 || {Na, Ar, Ex} <- Letrecs
                ],
    Function = scp_expr:fun_to_function(scp_tidy:function(Expr), Name, Arity),
    {[Function|Functions],Env};
form(X, Env) ->
    {[X],Env}.

attrs(Name, [{attribute,_,compile,{Name,[X|Xs]}}|Fs]) ->
    [X|Xs] ++ attrs(Name, Fs);
attrs(Name, [{attribute,_,compile,{Name,X}}|Fs]) ->
    [X|attrs(Name, Fs)];
attrs(Name, [_|Fs]) ->
    attrs(Name, Fs);
attrs(_, []) ->
    [].

%% Go over the forms and extract the top-level functions.
extract_functions(Forms) ->
    extract_functions(Forms, dict:new()).
extract_functions([F={function,_,Name,Arity,_}|Fs], Global) ->
    Fun = scp_expr:function_to_fun(F),
    extract_functions(Fs, dict:store({Name,Arity}, Fun, Global));
extract_functions([_|Fs], Global) ->
    extract_functions(Fs, Global);
extract_functions([], Global) ->
    Global.

function_names(Fs) ->
    sets:from_list(function_names1(Fs)).
function_names1([{function,_,Name,_,_}|Fs]) ->
    [Name|function_names1(Fs)];
function_names1([_|Fs]) ->
    function_names1(Fs);
function_names1([]) ->
    [].

%% Go over the forms and extract record definitions.
extract_records(Forms) ->
    extract_records(Forms, dict:new()).

extract_records([F|Fs], Records) ->
    case attribute =:= erl_syntax:type(F)
        andalso record =:= erl_syntax:atom_value(erl_syntax:attribute_name(F))
    of
        false ->
            extract_records(Fs, Records);
        true ->
            [NameTree, FieldsTree] = erl_syntax:attribute_arguments(F),
            Name = erl_syntax:atom_value(NameTree),
            Fields = erl_syntax:tuple_elements(FieldsTree),
            extract_records(Fs, dict:store(Name, Fields, Records))
    end;
extract_records([], Records) ->
    Records.

%% Defines a set of standard functions that are called by the
%% supercompiled code. Returns a dict and a list of forms.
get_stdfuns(Env0) ->
    {Fs, _} =
        lists:mapfoldl(fun (Str, Env1) ->
                               %% Parse the string and make a unique
                               %% name for the function.
                               {function,L,N0,A,Cs} = parse(Str),
                               {Env2,N1} = scp_expr:gensym(Env1, N0),
                               F = {function,L,N1,A,Cs},
                               {{{N0,N1},F},Env2}
                       end, Env0, stdfuns()),
    {Libnames0,Stdforms0} = lists:unzip(Fs),
    Libnames = dict:from_list(Libnames0),
    Stdforms = [atom_subst(Libnames, E) || E <- Stdforms0],
    {Libnames, [{attribute,0,file,{atom_to_list(?MODULE)++".erl",0}}|Stdforms]}.

parse(Str) ->
    {ok, Tokens, _} = erl_scan:string(Str),
    {ok, Function} = erl_parse:parse_form(Tokens),
    Function.

atom_subst(S, E0) ->
    F = fun (Node) -> atom_subst_map(Node, S) end,
    erl_syntax:revert(erl_syntax_lib:map(F, E0)).

atom_subst_map(Node, S) ->
    case atom =:= erl_syntax:type(Node)
        andalso dict:find(erl_syntax:atom_value(Node), S)
    of
        {ok, New} ->
            E = erl_syntax:atom(New),
            erl_syntax:copy_attrs(Node, E);
        _ ->
            Node
    end.
