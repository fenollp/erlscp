%% -*- coding: utf-8; mode: erlang -*-
%% @copyright 2012 Göran Weinholt
%% @author Göran Weinholt <goran@weinholt.se>
%% @doc The driving algorithm in the supercompiler.

-module(scp_main).
-export([drive/3]).

-include("scp.hrl").

lookup_function(Env, K={Name,Arity}) ->
    case dict:find(K, Env#env.global) of
        {ok,Fun} ->
            {ok,Fun};
        _ ->
            dict:find(K, Env#env.global)
    end.

%% The driving algorithm. The environment is used to pass information
%% downwards and upwards the stack. R is the current context.

%% Evaluation rules.
%% drive(Env0, {'integer',L0,C}, [Ctxt=#case_ctxt{}|R]) ->  %R1
%%     ;

drive(Env0, E={'atom',L0,G}, R=[#call_ctxt{args=Args}|_]) -> %R3
    %% This is a function call to a local function or a BIF. The
    %% function name is an atom, so the only way the arity can be
    %% found is by looking at the context.
    Arity = length(Args),
    case lookup_function(Env0, {G, Arity}) of
        {ok,Fun} -> drive_call(Env0, E, L0, G, Arity, Fun, R);
        _ -> build(Env0, E, R)
    end;
%% TODO: R3 for 'fun' references in any context

drive(Env0, {'fun',Line,{clauses,Cs0}}, R) ->   %R6
    {Env,Cs} = drive_clauses(Env0, Cs0),
    build(Env, {'fun',Line,{clauses,Cs}}, R);

%% drive(Env0, {'block',Lb,[{'match',Lm,P0,E0},Rest0]}, R) ->
%%     ;
drive(Env0, {'block',Line,[A0,B0]}, R) ->
    {Env1, A} = drive(Env0, A0, []),
    {Env, B} = drive(Env1, B0, R),
    {Env, scp_term:make_block(Line, A, B)};
drive(Env0, {'block',Line,Es}, R) ->
    %% XXX: this shouldn't be in the input language anymore
    drive(Env0, scp_term:list_to_block(Line, Es), R);

%% Focusing rules.
drive(Env0, {'call',L,F,Args}, R) ->            %R12
    drive(Env0, F, [#call_ctxt{line=L, args=Args}|R]);

%% Fallthrough.
drive(Env0, Expr, R) ->                         %R14
    io:fwrite("~n%% Fallthrough!~n", []),
    io:fwrite("%% Env: ~p~n%% Expr: ~p~n%% R: ~p~n",
              [Env0#env{forms=x,
                        global=dict:fetch_keys(Env0#env.global),
                        local=dict:fetch_keys(Env0#env.local)},
               Expr, R]),
    build(Env0, Expr, R).

%% Rebuilding expressions.
build(Env0, Expr, [#call_ctxt{line=Line, args=Args0}|R]) -> %R17
    {Env, Args} = drive_list(Env0, fun drive/3, Args0),
    build(Env, {call,Line,Expr,Args}, R);
build(Env, Expr, []) ->                         %R20
    {Env, Expr}.



%% Driving of function clauses (always in the empty context).
drive_list(Env0, Fun, [C0|Cs0]) ->
    {Env1,C1} = Fun(Env0, C0, []),
    {Env,Cs} = drive_list(Env1, Fun, Cs0),
    {Env,[C1 | Cs]};
drive_list(Env, _, []) ->
    {Env,[]}.
drive_clauses(Env, Cs) ->
    drive_list(Env, fun drive_clause/3, Cs).
drive_clause(Env0, {clause,L,Head,Guard,Body0}, _) ->
    Vars = lists:flatmap(fun scp_pattern:pattern_variables/1, Head),
    Env1 = Env0#env{bound=sets:union(Env0#env.bound, sets:from_list(Vars))},
    %% XXX: list_to_block shouldn't be needed after simplify
    {Env,Body} = drive(Env1, scp_term:list_to_block(L, Body0), []),
    {Env,{clause,L,Head,Guard,[Body]}}.

%% Driving of function calls.
drive_call(Env0, Funterm, Line, Name, Arity, Fun0, R) ->
    %% It is safe to return {Env0,L} if things become difficult.
    io:fwrite("Call: ~p, ~w/~w, R: ~p~n", [Funterm,Name,Arity,R]),
    io:fwrite("Fun: ~p~n", [Fun0]),
    L = plug(Funterm, R),
    FV = scp_term:free_variables(Env0#env.bound, L),
    io:fwrite("Free variables in ~p: ~w~n", [L,FV]),
    %% TODO: first try to find a renaming
    %% TODO: second try to find a homeomorphic embedding

    begin
        {Env1,Fname} = scp_term:gensym(Env0,"h"),
        %%{Env2,Fun} = scp_term:alpha_convert(Env1, Fun0),
        {Env1,{integer,Line,3}}
    end.


%% Plug an expression into a context.
plug(Expr, []) ->
    Expr;
plug(Expr, [#call_ctxt{line=Line, args=Args}|R]) ->
    plug({call,Line,Expr,Args}, R).
% TODO:

%% EUnit tests.

build_test() ->
    {_,{integer,0,123}} = drive(#env{}, {integer,0,123}, []),
    Fun = {'fun',1, {clauses, [{clause,1,[{var,1,'X'}], [], [{var,2,'X'}]}]}},
    drive(#env{}, Fun, []).
