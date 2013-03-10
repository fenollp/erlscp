%% -*- coding: utf-8; mode: erlang -*-

%% Copyright (C) 2012-2013 Göran Weinholt <goran@weinholt.se>

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

%% Miscellaneous tools for working with Erlang expressions.

-module(scp_expr).
-export([read/1,
         list_to_block/2, make_block/3, result_exp/1,
         make_case/3, make_if/2, make_call/3, make_let/4,
         function_to_fun/1, fun_to_function/3,
         delete_duplicates/1,
         variables/1, free_variables/2, subst/2,
         matches/1,
         fresh_variables/3, gensym/2, gensym_name/1,
         alpha_convert/2,
         make_letrec/3, extract_letrecs/1, letrec_destruct/1,
         find_renaming/2,
         terminates/2, is_linear/2, is_strict/2,
         apply_op/4, apply_op/3]).
-include("scp.hrl").

read(S) ->
    %% Too useful to not have around...
    {ok, Tokens, _} = erl_scan:string("x()->"++S++"."),
    {ok, {function,_,_,_,[{clause,L,[],[],B}]}} = erl_parse:parse_form(Tokens),
    list_to_block(L,B).

%% Convert a list of expressions (such as in a function body) into
%% nested blocks.
list_to_block(_Line,[X]) ->
    X;
list_to_block(Line,[X|Xs]) ->
    make_block(Line, X, list_to_block(Line, Xs)).

%% From Oscar Waddell's dissertation. The return expression for whole
%% the block becomes the second expression of the block.

%% TODO: this should instead create a structure where matches in E1
%% become structured like let.
make_block(L0, E1, E2) ->
    case is_simple(E1) of
        true -> E2;
        false ->
            E1n = case E1 of
                      {'block',_,[E1a,E1b]} ->
                          case is_simple(E1b) of
                              true -> E1a;
                              _ -> E1
                          end;
                      _ -> E1
                  end,
            case E2 of
                {'block',L1,[E3,E4]} ->
                    {'block',L1,[{'block',L0,[E1n,E3]},E4]};
                _ ->
                    {'block',L0,[E1n,E2]}
            end
    end.
is_simple({var,_,_}) -> true;
is_simple({integer,_,_}) -> true;
is_simple({float,_,_}) -> true;
is_simple({atom,_,_}) -> true;
is_simple({string,_,_}) -> true;
is_simple({char,_,_}) -> true;
is_simple({nil,_}) -> true;
is_simple({'fun',_,_}) -> true;
is_simple(_) -> false.
result_exp({'block',_,_E0,E1}) -> E1;
result_exp(E) -> E.

%% Construct a case expression. R5 is simplified by not having to
%% check for this simple case.
make_case(Line, {nil,_}, [{clause,_,[{nil,_}],[],Body}]) ->
    list_to_block(Line, Body);
make_case(Line, E, Cs0) ->
    {'case',Line,E,Cs0}.

make_if(Line, Cs0) ->
    {'if',Line,Cs0}.

make_let(Line, [Lhs|Lhss], [Rhs|Rhss], Body0) ->
    %% XXX: this assumes that the left hand sides do not contain
    %% repeated variables.
    Body = make_let(Line, Lhss, Rhss, Body0),
    Fun = {'fun',Line,{clauses,[{clause,Line,[Lhs],[],[Body]}]}},
    {call,Line,Fun,[Rhs]};
make_let(Line, [], [], Body) when is_list(Body) ->
    list_to_block(Line, Body).

%% Make a function call, but handle the artificial constructor
%% expressions and try some simplifications first.
make_call(Line, {constructor,_,cons}, [H,T]) ->
    {cons,Line,H,T};
make_call(Line, {constructor,_,tuple}, As) ->
    {tuple,Line,As};
make_call(Line, {'fun',Lf,{function,F,A}}, As) when A == length(As) ->
    make_call(Line, {atom,Lf,F}, As);
make_call(Line, {'atom',_,element}, [{integer,_,I},{tuple,_,Es}])
  when I > 0, I =< length(Es) ->
    %% Need to residualize the rest of Es for effect.
    Rest = lists:sublist(Es, 1, I - 1) ++
        lists:sublist(Es, I + 1, length(Es)),
    list_to_block(Line, Rest ++ [lists:nth(I, Es)]);
make_call(Line, {'atom',_,hd}, [{cons,_,H,T}]) ->
    %% Residualize T for effect.
    make_block(Line, T, H);
make_call(Line,Expr,Args) ->
    {call,Line,Expr,Args}.


%% Conversion between global and local functions.
function_to_fun({function,Line,_Name,_Arity,Clauses}) ->
    {'fun',Line,{clauses,Clauses}}.
fun_to_function({'fun',Line,{clauses,Clauses}},Name,Arity) ->
    {function,Line,Name,Arity,Clauses}.

delete_duplicates([X|Xs]) -> [X|delete_duplicates([Y || Y <- Xs, X =/= Y])];
delete_duplicates([]) -> [].

%% Find the free variables of an expression, in a stable order.
free_variables(Bound, Expr) ->
    %% Find free variables that are also bound outside the expression.
    [ V || V <- free_variables(Expr), sets:is_element(V, Bound) ].
free_variables(Expr) ->
    Tree = erl_syntax_lib:annotate_bindings(Expr, ordsets:new()),
    Vars = delete_duplicates(variables(Expr)),
    Ann = erl_syntax:get_ann(Tree),
    case lists:keyfind(free, 1, Ann) of
        {_,Free} ->
            [V || V <- Vars, ordsets:is_element(V,Free)];
        _ -> []
    end.

%% The variables of the expression, in a stable order.
variables(Expr) -> lists:flatten(variables0(Expr)).
variables0(Expr) ->
    case erl_syntax:type(Expr) of
        variable ->
            [erl_syntax:variable_name(Expr)];
        _ ->
            lists:map(fun (Es) -> lists:map(fun variables0/1, Es) end,
                      erl_syntax:subtrees(Expr))
    end.

%% The matches contained in the expression.
matches(Expr) -> lists:flatten(matches0(Expr)).
matches0(Expr) ->
    case erl_syntax:type(Expr) of
        match ->
            [Expr];
        _ ->
            lists:map(fun (Es) -> lists:map(fun matches0/1, Es) end,
                      erl_syntax:subtrees(Expr))
    end.

%% Generate a fresh variable.
gensym(Env0, Prefix) ->
    F = fun (N) ->
                X = gensym_name(Prefix) ++ "@" ++ integer_to_list(N),
                list_to_atom(X)
        end,
    Name = erl_syntax_lib:new_variable_name(F, Env0#env.seen_vars),
    Env = Env0#env{seen_vars=sets:add_element(Name, Env0#env.seen_vars)},
    {Env,Name}.

%% Get the name part of a gensym variable (or the whole variable if
%% it's just a variable).
gensym_name(V) when is_list(V) ->
    lists:takewhile(fun (C) -> C =/= $@ end, V);
gensym_name(V) when is_atom(V) ->
    gensym_name(atom_to_list(V)).

fresh_variables(Env0,S0,Names) ->
    %% Updates the substitution dict S0 with fresh variables for Names.
    lists:foldl(fun (V, {Env0,S0}) ->
                        {Env,GV} = gensym(Env0, atom_to_list(V)),
                        S = dict:store(V, {var,1,GV}, S0),
                        {Env,S}
                end,
                {Env0,S0},
                Names).

%% Variable substitution. S is a dictionary that maps variable names
%% to some replacement expression.
subst(S, E) ->
    Fun = subst_fun(S),
    erl_syntax:revert(Fun(E)).
subst_1(S, E) ->
    Fun = subst_fun(S),
    erl_syntax_lib:map_subtrees(Fun, E).
subst_fun(S) ->
    fun
        (E={var,_,'_'}) ->
            E;
        (E={var,L,V}) ->
            case dict:find(V, S) of
                %% XXX: discards line info if the replacement is not a
                %% variable.
                {ok,{var,_,V1}} -> {var,L,V1};
                {ok,V1} -> V1;
                _ -> E
            end;
        (E={'fun',L,{clauses,Cs0}}) ->
            Cs = lists:map(fun (C={clause,Lc,H,G,B}) ->
                                   Vars = lists:flatmap(fun scp_pattern:pattern_variables/1, H),
                                   %% Remove shadowed variables from
                                   %% the substitution.
                                   S1 = dict:filter(fun (N,_) ->
                                                            not lists:member(N, Vars)
                                                    end,
                                                    S),
                                   subst(S1,C)
                           end,
                           Cs0),
            {'fun',L,{clauses,Cs}};
        %% TODO: other places where shadowing takes place
        (E) ->
            subst_1(S, E)
    end.

%% Alpha conversion. Generates fresh names for all variables
%% introduced in the expression.
alpha_convert(Env0, Expr0) ->
    {Env1,_S,Expr} = ac(Env0,dict:new(),Expr0),
    Env = Env0#env{seen_vars = Env1#env.seen_vars},
    {Env, Expr}.

ac(Env,S,E={var,L,'_'}) -> {Env,S,E};
ac(Env,S,E={var,L,V}) ->
    %% Look up V in the substitution environment.
    case dict:find(V, S) of
        {ok,{var,_,V1}} -> {Env,S,{var,L,V1}};
        _ -> {Env,S,E}
    end;
ac(Env,S,E={integer,_,_}) -> {Env,S,E};
ac(Env,S,E={float,_,_}) -> {Env,S,E};
ac(Env,S,E={atom,_,_}) -> {Env,S,E};
ac(Env,S,E={string,_,_}) -> {Env,S,E};
ac(Env,S,E={char,_,_}) -> {Env,S,E};
ac(Env,S,E={nil,_}) -> {Env,S,E};
ac(Env0,S0,{call,L,F0,Es0}) ->
    {Env,S,[F|Es]} = ac_list(Env0,S0,[F0|Es0]),
    {Env,S,{call,L,F,Es}};
ac(Env0,S0,{op,L,Op,A0}) ->
    {Env,S,A} = ac(Env0,S0,A0),
    {Env,S,{op,L,Op,A}};
ac(Env0,S0,{op,L,Op,A0,B0}) ->
    {Env,S,[A,B]} = ac_list(Env0,S0,[A0,B0]),
    {Env,S,{op,L,Op,A,B}};
ac(Env0,S0,{cons,L,A0,B0}) ->
    {Env,S,[A,B]} = ac_list(Env0,S0,[A0,B0]),
    {Env,S,{cons,L,A,B}};
ac(Env0,S0,{tuple,L,Es0}) ->
    {Env,S,Es} = ac_list(Env0,S0,Es0),
    {Env,S,{tuple,L,Es}};

ac(Env0,S0,{record_field,L,R0,F0}) ->
    {Env,S,[R,F]} = ac_list(Env0,S0,[R0,F0]),
    {Env,S,{record_field,L,R,F}};

ac(Env0,S0,{remote,L,M0,F0}) ->
    {Env,S,[M,F]} = ac_list(Env0,S0,[M0,F0]),
    {Env,S,{remote,L,M,F}};
ac(Env0,S0,{'fun',L,{clauses,Cs0}}) ->
    {Env,S,Cs} = ac_fun_clauses(Env0,S0,Cs0),
    {Env,S,{'fun',L,{clauses,Cs}}};
ac(Env,S,E={'fun',L,{function,_,_}}) ->
    {Env,S,E};
ac(Env,S,E={'fun',L,{function,M,F,A}}) when is_atom(M), is_atom(F), is_integer(A) ->
    {Env,S,E};
ac(Env0,S0,{'fun',L,{function,M0,F0,A0}}) ->
    {Env,S,[M,F,A]} = ac_list(Env0,S0,[M0,F0,A0]),
    {Env,S,{'fun',L,{function,M,F,A}}};

ac(Env0,S0,{'case',L,E0,Cs0}) ->
    {Env1,S1,E} = ac(Env0, S0, E0),
    {Env,S,Cs} = ac_icr_clauses(Env1, S1, Cs0, 'case'),
    {Env,S,{'case',L,E,Cs}};

ac(Env0,S0,{'if',L,Cs0}) ->
    %% Like a case, except there are no patterns and no scrutinee.
    %% Only the bodies can introduce new variables.
    {Env,S,Cs} = ac_icr_clauses(Env0, S0, Cs0, 'if'),
    {Env,S,{'if',L,Cs}};

ac(Env0,S0,{match,L,P0,E0}) ->
    %% An unbound variable defined in P0 may already have been seen in
    %% a different pattern but not yet been bound. It'll be in S then,
    %% and it should not receive a new name.
    Names0 = lists:filter(fun (Name) -> not dict:is_key(Name, S0) end,
                          scp_pattern:pattern_variables(P0)),
    %% Pattern variables also in Env0#env.in_set are not shadowed.
    Names = sets:subtract(sets:from_list(Names0), Env0#env.bound),
    {Env1,S1} = fresh_variables(Env0, S0, sets:to_list(Names)),
    %% Variables defined in P0 are visible after this expression.
    Env2 = Env1#env{bound = sets:union(Env0#env.bound, Names)},
    {Env3,S2,P} = ac(Env2,S1,P0),
    {Env,S,E} = ac(Env3,S2,E0),
    {Env,S,{match,L,P,E}};

ac(Env0,S0,{block,L,[A0,B0]}) ->
    %% Variables defined in A are bound in B.
    {Env1,S1,A} = ac(Env0,S0,A0),
    {Env,S,B} = ac(Env1,S1,B0),
    {Env,S,{block,L,[A,B]}}.

ac_list(Env0,S0,[E0|Es0]) ->
    %% The rule here is that definitions made in expressions are
    %% visible only after the expressions, but different definitions
    %% can refer to the same unbound variable.
    {Env1,S1,E} = ac(Env0, S0, E0),
    %% The rest of the expressions have the same set of bound
    %% variables as E0.
    {Env2,S2,Es} = ac_list(Env1#env{bound=Env0#env.bound}, S1, Es0),
    %% The variables visible afterwards is the union of the variables
    %% bound by the expressions.
    Env = Env2#env{bound = sets:union(Env1#env.bound, Env2#env.bound)},
    {Env,S2,[E|Es]};
ac_list(Env,S,[]) ->
    {Env,S,[]}.

ac_fun_clauses(Env0,S0,[{clause,L,H0,G0,B0}|Cs0]) ->
    %% Variables defined in head shadow those which have already been
    %% bound, so their substitutions are removed here.
    Shadowing = lists:flatmap(fun scp_pattern:pattern_variables/1, H0),
    S1 = dict:filter(fun (Name,_) -> not lists:member(Name,Shadowing) end,
                     S0),
    {Env1,S2,H} = ac_head(Env0, S1, H0),
    {Env2,S3,G} = ac_guard(Env1, S2, G0),
    {Env3,S4,B} = ac_list(Env2, S3, B0),
    C = {clause,L,H,G,B},
    {Env4,S,Cs} = ac_fun_clauses(Env3, S4, Cs0),
    %% Freshly bound variables are not visible outside the clause.
    Env = Env4#env{bound=Env0#env.bound},
    {Env,S0,[C|Cs]};
ac_fun_clauses(Env,S,[]) ->
    {Env,S,[]}.

ac_head(Env0,S0,[P0|Ps0]) ->
    %% The pattern variables that need fresh names are those which
    %% have not yet been given a fresh name.
    Names = lists:filter(fun (Name) -> not dict:is_key(Name, S0) end,
                         scp_pattern:pattern_variables(P0)),
    %% The names defined in a head are bound in guard and body.
    Env1 = Env0#env{bound = sets:union(Env0#env.bound,
                                       sets:from_list(Names))},
    {Env2,S1} = fresh_variables(Env1, S0, Names),
    {Env3,S2,P} = ac(Env2, S1, P0),
    {Env,S,Ps} = ac_head(Env3, S2, Ps0),
    {Env,S,[P|Ps]};
ac_head(Env0,S0,[]) ->
    {Env0,S0,[]}.

ac_guard(Env0,S0,G0) ->
    %% Guards are lists of lists of guard expressions. These
    %% expressions can't introduce new names.
    G = lists:map(fun (Gexprs) ->
                          lists:map(fun (Gexpr) ->
                                            subst(S0, Gexpr)
                                    end,
                                    Gexprs)
                  end,
                  G0),
    {Env0,S0,G}.

ac_icr_clauses(Env0,S0,[{clause,L,P0,G0,B0}|Cs0],ExprType) ->
    Vars0 = sets:from_list(lists:flatmap(fun scp_pattern:pattern_variables/1, P0)),
    Vars1 = sets:subtract(Vars0, Env0#env.bound),
    Vars2 = sets:filter(fun (Name) -> not dict:is_key(Name,S0) end,
                        Vars1),
    {Env1,S1} = fresh_variables(Env0, S0, sets:to_list(Vars2)),
    P = [ subst(S1, X) || X <- P0 ],
    %% The new variables are bound in the guard and in the body.
    {Env3,S3,G} = ac_guard(Env1#env{bound=sets:union(Env1#env.bound, Vars1)},
                           S1, G0),
    %% Variables can become bound in the body.
    {Env4,S4,B} = ac_list(Env3, S3, B0),
    case Cs0 of
        [] ->
            %% To make sets:union work properly down below.
            {Env5,S5,Cs} = {Env4,S4,Cs0};
        _ ->
            {Env5,S5,Cs} = ac_icr_clauses(Env4#env{bound = Env0#env.bound},
                                          S4, Cs0, ExprType)
    end,
    case ExprType of
        'try' ->
            %% No new variables escape.
            Env = Env5#env{bound = Env0#env.bound};
        _ ->
            %% Variables that escape are those bound in all clauses.
            Env = Env5#env{bound = sets:union(Env4#env.bound, Env5#env.bound)}
    end,
    {Env,S5,[{clause,L,P,G,B}|Cs]};

ac_icr_clauses(Env0,S0,[],ExprType) ->
    {Env0,S0,[]}.


%% The supercompiler creates letrecs. These do not exist in Erlang,
%% but since the names are unique they can be implemented by placing
%% the funs at the top level instead. The letrecs masquerade as
%% function calls.

make_letrec(Line, [{Name,Arity,Fun}], Body) ->
    Fakefun = {'fun',1,{function,scp_expr,letrec,1}},
    Bs0 = [{tuple,2,[{atom,3,Name},{integer,4,Arity},Fun]}],
    Arg = {cons,5,{tuple,6,Bs0},
           {tuple,7,Body}},
    {'call',Line,Fakefun,[Arg]}.

extract_letrecs(E) -> extract_letrecs(E,[]).
extract_letrecs(E0,Ls) ->
    {E1,Ls0} = extrecs_1(E0,Ls),
    E = erl_syntax:revert(E1),
    {E,Ls0}.
extrecs_1(E={'call',Line,{'fun',1,{function,scp_expr,letrec,1}},[Arg]}, Ls0) ->
    {Bs1,Body0} = letrec_destruct(E),
    %% Extract letrecs from the funs
    {Bs,Ls1} = lists:mapfoldl(fun ({Name,Arity,Fun0},Ls00) ->
                                      {Fun,Ls01} = extract_letrecs(Fun0,Ls00),
                                      {{Name,Arity,Fun},Ls01}
                              end,
                              Ls0, Bs1),
    %% And now from the body
    {Body,Ls2} = lists:mapfoldl(fun extract_letrecs/2, Ls1, Body0),
    E1 = list_to_block(Line,Body),
    {E1,Bs++Ls2};
extrecs_1(E,Ls) ->
    erl_syntax_lib:mapfold_subtrees(fun extrecs_1/2, Ls, E).

%% Returns the bindings and the body a letrec.
letrec_destruct({'call',Line,{'fun',1,{function,scp_expr,letrec,1}},[Arg]}) ->
    {cons,_,{tuple,_,Bs0},{tuple,_,Body}} = Arg,
    %% Bs1 = [{Name,Arity,Fun} || {tuple,_,[{atom,_,Name},{integer,_,Arity},Fun]} <- Bs0],
    Bs1 = lists:map(fun ({tuple,_,[{atom,_,Name},{integer,_,Arity},Fun]}) ->
                            {Name,Arity,Fun}
                    end, Bs0),
    {Bs1,Body}.

%% Renamings.

find_renaming(Env, Expr) ->
    %% TODO: check if it's necessary to know which names are bound
    ?DEBUG("Is ~p a renaming of something in~n ~p?~n",[Expr,Env#env.ls]),
    find_renaming_1(sets:new(), Env#env.ls, Expr).

find_renaming_1(B, [{Fname,E}|Es], Expr) ->
    %% Find out if the old expression E is a renaming of Expr.
    case is_renaming(B, E, Expr) of
        true -> {ok,Fname};
        false -> find_renaming_1(B, Es, Expr)
    end;
find_renaming_1(_B, [], Expr) ->
    false.

%% Is E1 the same as E2 up to variable renaming? The expressions must
%% have been alpha converted first.
is_renaming(B, E1, E2) ->
    case find_var_subst(B, [{E1,E2}]) of
        {ok,S} ->
            ?DEBUG("is_renaming.~nE1: ~p~nE2: ~p~n", [E1,E2]),
            ?DEBUG("S: ~p~n",[S]),
            %% FIXME: for 'fun' to work, does this need to use a
            %% subst() that does not check the scoping rules?
            ?DEBUG("Afterwards: ~p~n", [subst(dict:from_list(S), E2)]),
            subst(dict:from_list(S), E2) == E2;
        _ ->
            false
    end.

%% This takes a worklist with expressions on the form [{E1,E2}|Rest].
%% It then finds a substitution that when applied to E1 would return
%% E2 (and so on for the rest of the list). It will only create
%% variable to variable substitions, everything else must be the same.
find_var_subst(B, []) -> {ok,[]};
find_var_subst(B, [{{integer,_,V},{integer,_,V}}|T]) -> find_var_subst(B, T);
find_var_subst(B, [{{float,_,V},{float,_,V}}|T]) -> find_var_subst(B, T);
find_var_subst(B, [{{atom,_,V},{atom,_,V}}|T]) -> find_var_subst(B, T);
find_var_subst(B, [{{string,_,V},{string,_,V}}|T]) -> find_var_subst(B, T);
find_var_subst(B, [{{char,_,V},{char,_,V}}|T]) -> find_var_subst(B, T);
find_var_subst(B, [{{nil,_},{nil,_}}|T]) -> find_var_subst(B, T);
find_var_subst(B, [{{'fun',_,{function,F,A}},{'fun',_,{function,F,A}}}|T])  ->
    find_var_subst(B, T);
find_var_subst(B, [{{'fun',_,{function,M,F,A}},{'fun',_,{function,M,F,A}}}|T])  ->
    find_var_subst(B, T);
find_var_subst(B, [{{var,_,N},{var,_,N}}|T]) ->
    %% The same variable in both expressions. No need for a
    %% substitution.
    find_var_subst(B, T);
find_var_subst(B, [{{var,_,_},{var,_,'_'}}|T]) -> false;
find_var_subst(B, [{{var,_,'_'},{var,_,_}}|T]) -> false;
find_var_subst(B, [{{var,_,N1},E2={var,_,N2}}|T]) ->
    case sets:is_element(N1, B) orelse sets:is_element(N2, B) of
        true ->
            %% The variables are different and one of them is bound. A
            %% renaming is not possible.
            false;
        false ->
            %% Make a substitution from N1 to E2.
            Sd = dict:from_list([{N1,E2}]),
            find_var_subst(B, [{subst(Sd, A),subst(Sd, B)} || {A,B} <- T],
                           [{N1,E2}])
    end;
find_var_subst(B, [{{call,_,F1,As1},{call,_,F2,As2}}|T])
  when length(As1) == length(As2) ->
    find_var_subst(B, [{F1,F2} | lists:zip(As1,As2)] ++ T);
find_var_subst(B, [{{tuple,_,Es1},{tuple,_,Es2}}|T])
  when length(Es1) == length(Es2) ->
    find_var_subst(B, lists:zip(Es1,Es2) ++ T);
find_var_subst(B, [{{cons,_,H1,T1},{cons,_,H2,T2}}|T]) ->
    find_var_subst(B, [{H1,H2}, {T1,T2} | T]);
find_var_subst(B, [{{op,_,Op,L1,R1},{op,_,Op,L2,R2}}|T]) ->
    find_var_subst(B, [{L1,L2}, {R1,R2} | T]);
find_var_subst(B, [{{op,_,Op,A1},{op,_,Op,A2}}|T]) ->
    find_var_subst(B, [{A1,A2} | T]);
find_var_subst(B, [{{remote,_,M1,F1},{remote,_,M2,F2}}|T]) ->
    find_var_subst(B, [{M1,M2},{F1,F2}|T]);
find_var_subst(B, [{{block,_,Es1},{block,_,Es2}}|T])
  when length(Es1) == length(Es2) ->
    find_var_subst(B, lists:zip(Es1,Es2) ++ T);
find_var_subst(B0, [{{'if',_,Cs1},{'if',_,Cs2}}|T])
  when length(Cs1) == length(Cs2) ->
    %% Pair up all the expressions from the guards and the bodies.
    %% There are no patterns and thus no new variables.
    {_,Gs1,Bs1} = unzip_clauses(Cs1),
    {_,Gs2,Bs2} = unzip_clauses(Cs2),
    [Es1,Es2] = lists:map(fun lists:flatten/1, [Gs1 ++ Bs1, Gs2 ++ Bs2]),
    if length(Es1) == length(Es2) ->
            find_var_subst(B0, lists:zip(Es1, Es2) ++ T);
       true ->
            false
    end;
find_var_subst(B0, [{{'case',_,E1,Cs1},{'case',_,E2,Cs2}}|T])
  when length(Cs1) == length(Cs2) ->
    {Ps10,Gs10,Bs1} = unzip_clauses(Cs1),
    {Ps20,Gs20,Bs2} = unzip_clauses(Cs2),
    [Ps1,Ps2,Gs1,Gs2] = lists:map(fun lists:flatten/1, [Ps10,Ps20,Gs10,Gs20]),
    if length(Ps1) == length(Ps2) andalso
       length(Gs1) == length(Gs2) andalso
       length(Bs1) == length(Bs2) ->
            %% Extract new bindings from the patterns and add them to B0.
            %% ?DEBUG("Ps1=~p~nPs2=~p~n",[Ps1,Ps2]),
            %% ?DEBUG("Work=~p~n",[[{E1,E2}] ++ lists:zip(Ps1,Ps2)]),
            case find_var_subst(B0, [{E1,E2}] ++ lists:zip(Ps1,Ps2)) of
                {ok,Ss} ->
                    %%?DEBUG("Ss=~p~n",[Ss]),
                    %% The variables from Ps1 and Ps2 are bound in the
                    %% rest of the work. This is imprecise, but alpha
                    %% conversion should make it work.
                    Vars = lists:flatmap(fun scp_pattern:pattern_variables/1,
                                         Ps1 ++ Ps2),
                    %%?DEBUG("Vars=~p~n",[Vars]),
                    B = sets:union(sets:from_list(Vars), B0),
                    Bodies = lists:flatmap(fun ({Body1,Body2}) ->
                                               lists:zip(Body1,Body2)
                                           end,
                                           lists:zip(Bs1, Bs2)),
                    %% ?DEBUG("new work=~p~n", [lists:zip(Gs1, Gs2) ++
                    %%                                 Bodies ++ T]),
                    %% Processing the patterns may have resulted in
                    %% new variable substitutions. Apply these to the
                    %% rest of the work.
                    Sd = dict:from_list(Ss),
                    NewT = [{subst(Sd, X),subst(Sd, Y)} ||
                               {X,Y} <- lists:zip(Gs1, Gs2) ++ Bodies ++ T],
                    find_var_subst(B, NewT, Ss);
                false -> false
            end;
       true ->
            false
    end;
find_var_subst(B0, [{{'fun',_,{clauses,Cs1}},{'fun',_,{clauses,Cs2}}}|T])
  when length(Cs1) == length(Cs2) ->
    {Ps10,Gs10,Bs1} = unzip_clauses(Cs1),
    {Ps20,Gs20,Bs2} = unzip_clauses(Cs2),
    [Ps1,Ps2,Gs1,Gs2] = lists:map(fun lists:flatten/1, [Ps10,Ps20,Gs10,Gs20]),
    if length(Ps1) == length(Ps2) andalso
       length(Gs1) == length(Gs2) andalso
       length(Bs1) == length(Bs2) ->
            %% Same as 'case', except there's no E1, E2. This also
            %% depends quite a bit on alpha conversion.
            case find_var_subst(B0, lists:zip(Ps1,Ps2)) of
                {ok,Ss} ->
                    Vars = lists:flatmap(fun scp_pattern:pattern_variables/1,
                                         Ps1 ++ Ps2),
                    B = sets:union(sets:from_list(Vars), B0),
                    Bodies = lists:flatmap(fun ({Body1,Body2}) ->
                                               lists:zip(Body1,Body2)
                                           end,
                                           lists:zip(Bs1, Bs2)),
                    Sd = dict:from_list(Ss),
                    NewT = [{subst(Sd, X),subst(Sd, Y)} ||
                               {X,Y} <- lists:zip(Gs1, Gs2) ++ Bodies ++ T],
                    find_var_subst(B, NewT, Ss);
                false -> false
            end;
       true ->
            false
    end;
%% TODO: more stuff
find_var_subst(B, [{E1,E2}|T]) ->
    %% If two expressions have different types then there can't be a
    %% renaming.
    T1 = erl_syntax:type(E1),
    T2 = erl_syntax:type(E2),
    ?DEBUG("r fallthrough: ~p,~p~n",[T1,T2]),
    case T1 == T2 of
        true ->
            %% XXX: Fill in all supported expression types here. This
            %% is here because the function is not completed yet.
            true = lists:member(T1,
                                [integer,float,atom,string,char,nil,
                                 variable,underscore,application,case_expr,
                                 list,infix_expr,prefix_expr,tuple,
                                 implicit_fun,if_expr,fun_expr
                                ]),
            false;
        _ ->
            %% Different types. There can't possibly be a renaming.
            false
    end.

find_var_subst(B, T, NewSubst) ->
    %% Appends a substitution list to the substitution that results
    %% from the unprocessed work T0.
    case find_var_subst(B, T) of
        {ok,Substs} ->
            {ok,NewSubst++Substs};
        false ->
            false
    end.

unzip_clauses(Cs) ->
    lists:unzip3(lists:map(fun ({clause,_,P,G,B}) -> {P,G,B} end,
                           Cs)).

%% Does the expression always terminate (and is free of side-effects)?
terminates(Env, {var,_,N}) ->
    %% If a variable is in split_vars it could represent any kind of
    %% expression whatsoever. This would represent the guard in R8.
    not lists:member(N, Env#env.split_vars);
terminates(Env, E) when ?IS_CONST_EXPR(E) -> true;
terminates(Env, {'fun',_,_}) -> true;
terminates(Env, {cons,_,H,T}) ->
    terminates(Env, H) andalso terminates(Env, T);
terminates(Env, {tuple,_,Es}) ->
    lists:all(fun (E) -> terminates(Env, E) end, Es);
%% TODO: make this stronger
terminates(Env, _E) ->
    ?DEBUG("does not terminate? ~p~n", [_E]),
    false.

%% Is the variable N linear in E? It is if it's guaranteed that N will
%% be evaluated at most once in E. It's alright if E doesn't terminate
%% before coming to N. E must have been alpha converted.
is_linear('_', _) ->
    true;
is_linear(N, E) ->
    ?DEBUG("is_linear ~p ~p~n",[N,E]),
    lin(N, E) =< 1.

lin(N, E) ->
    case erl_syntax:type(E) of
        variable ->
            case erl_syntax:variable_name(E) of
                N -> 1;
                _ -> 0
            end;
        application ->
            Op = erl_syntax:application_operator(E),
            Args = erl_syntax:application_arguments(E),
            ArgC = lists:sum(linlist(N, Args)),
            case erl_syntax:type(Op) of
                fun_expr ->
                    %% This is a let, so the check for linearity in
                    %% the Rhs and the body (or bodies, if it's not
                    %% really a let).
                    Cs = erl_syntax:fun_expr_clauses(Op),
                    ArgC + lists:max(linlist(N, Cs));
                _ ->
                    ArgC + lin(N, Op)
            end;
        if_expr ->
            Cs = erl_syntax:if_expr_clauses(E),
            lists:max(linlist(N, Cs));
        case_expr ->
            Arg = erl_syntax:case_expr_argument(E),
            Cs = erl_syntax:case_expr_clauses(E),
            lin(N, Arg) + lists:max(linlist(N, Cs));
        clause ->
            %% XXX: Ignores the pattern and guard. If N appears in
            %% those then there's a different check that needs to
            %% happen anyway.
            lists:sum(linlist(N, erl_syntax:clause_body(E)));
        match_expr ->
            %% XXX: ignores the pattern
            lin(N, erl_syntax:match_expr_body(E));
        fun_expr ->
            %% If the variable is in one of the clauses then it's
            %% difficult to say statically if it's linear.
            Cs = erl_syntax:fun_expr_clauses(E),
            2 * lists:max(linlist(N, Cs));
        T when T==list; T==tuple; T==infix_expr;
               T==prefix_expr; T==block_expr;
               T==module_qualifier ->
            lists:sum(linlist(N, lists:flatten(erl_syntax:subtrees(E))));
        T when ?IS_CONST_TYPE(T); T==implicit_fun;
               T==operator ->
            0
    end.

linlist(N, Es) ->
    [lin(N, E) || E <- Es].

%% Is the variable N strict in E? In other words, is it guaranteed
%% that N will be evaluated in E? It's alright if E doesn't terminate
%% before coming to N. E must have been alpha converted.
is_strict('_', _) ->
    false;
is_strict(N, E) ->
    F = fun (E1) -> is_strict(N, E1) end,
    case erl_syntax:type(E) of
        variable ->
            erl_syntax:variable_name(E) == N;
        application ->
            Op = erl_syntax:application_operator(E),
            Args = erl_syntax:application_arguments(E),
            case erl_syntax:type(Op) of
                fun_expr ->
                    %% If a function is in the operator position then
                    %% this is similar to let, except the fun expr
                    %% might have multiple clauses.
                    lists:all(F, erl_syntax:fun_expr_clauses(Op))
                        orelse lists:any(F, Args);
                _ ->
                    lists:any(F, [Op|Args])
            end;
        if_expr ->
            lists:all(F, erl_syntax:if_expr_clauses(E));
        case_expr ->
            Arg = erl_syntax:case_expr_argument(E),
            Cs = erl_syntax:case_expr_clauses(E),
            is_strict(N, Arg) orelse lists:all(F, Cs);
        clause ->
            %% XXX: ignores the guard and the pattern
            lists:any(F, erl_syntax:clause_body(E));
        match_expr ->
            %% XXX: ignores the pattern
            is_strict(N, erl_syntax:match_expr_body(E));
        T when T==list; T==tuple; T==infix_expr;
               T==prefix_expr; T==block_expr;
               T==module_qualifier ->
            lists:any(F, lists:flatten(erl_syntax:subtrees(E)));
        T when ?IS_CONST_TYPE(T); T==implicit_fun; T==fun_expr;
               T==operator ->
            false
    end.

%% Constant folding.
apply_op(L, '+', {integer,_,I1}, {integer,_,I2}) ->
    {ok,{integer,L,I1+I2}};
apply_op(L, '-', {integer,_,I1}, {integer,_,I2}) ->
    {ok,{integer,L,I1-I2}};
apply_op(L, '*', {integer,_,I1}, {integer,_,I2}) ->
    {ok,{integer,L,I1*I2}};
apply_op(L, '/', {integer,_,I1}, {integer,_,I2}) when I2 =/= 0 ->
    {ok,{integer,L,I1/I2}};
apply_op(L, '==', {integer,_,I1}, {integer,_,I2}) ->
    {ok,{atom,L,I1==I2}};
apply_op(L, '>=', {integer,_,I1}, {integer,_,I2}) ->
    {ok,{atom,L,I1>=I2}};
apply_op(L, '>', {integer,_,I1}, {integer,_,I2}) ->
    {ok,{atom,L,I1>I2}};
%% TODO: more operators
apply_op(_,_,_,_) ->
    false.

apply_op(L, '-', {integer,_,I}) ->
    {ok,{integer,L,-I}};
apply_op(_,_,_) ->
    false.

%% EUnit tests.


fv0_test() ->
    ['Y'] = free_variables({match,1,{var,1,'X'},{var,1,'Y'}}).
fv1_test() ->
    Bs = sets:new(),
    [] = free_variables(Bs,{match,1,{var,1,'X'},{var,1,'Y'}}).
fv2_test() ->
    ['X'] = free_variables({call,43,
                            {atom,43,foo},
                            [{op,43,'+',{var,43,'X'},{integer,43,1}}]}).
fv3_test() ->
    ['Y'] = free_variables({block,1,[{match,1,{var,1,'X'},{var,1,'Y'}},
                                     {var,1,'X'}]}).
fv4_test() ->
    ['Y','X'] = free_variables({block,1,[{match,1,{var,1,'Z'},{var,1,'Y'}},
                                         {var,1,'X'}]}).
fv5_test() ->
    ['X','Y'] = free_variables({block,1,[{match,1,{var,1,'Z'},{var,1,'X'}},
                                         {var,1,'Y'}]}).

check_ac(E0) ->
    Vars0 = erl_syntax_lib:variables(E0),
    {Env,E1} = alpha_convert(#env{seen_vars=Vars0}, E0),
    io:fwrite("Result: ~p~n",[E1]),
    io:fwrite("Env: ~p~n",[Env]),
    %% TODO: check that E1 is a renaming
    true = E1 =/= E0,
    Vars1 = erl_syntax_lib:variables(E1).

ac0_test() ->
    E0 = {'fun',43,
          {clauses,
           [{clause,43,
             [{var,43,'X'}],
             [],
             [{op,44,'+',{var,44,'X'},{integer,44,1}}]}]}},
    check_ac(E0).

ac1_test() ->
    E0 = {'fun',43,
          {clauses,
           [{clause,43,
             [{var,43,'X'}],
             [],
             [{block,43,
               [{match,44,{var,44,'X'},{integer,44,0}},
                {var,45,'X'}]}]}]}},
    check_ac(E0).

ac2_test() ->
    E0 = {'fun',43,
          {clauses,
           [{clause,43,
             [{var,43,'X'}],
             [],
             [{block,43,
               [{match,44,
                 {tuple,44,[{var,44,'X'},{var,44,'Y'}]},
                 {tuple,44,[{var,44,'X'},{integer,44,1}]}},
                {var,45,'X'}]}]}]}},
    check_ac(E0).

ac3_test() ->
    E0 = {'fun',43,
          {clauses,
           [{clause,43,
             [{var,43,'X'},{var,43,'X'}],
             [],
             [{block,43,
               [{match,44,
                 {tuple,44,[{var,44,'X'},{var,44,'Y'}]},
                 {tuple,44,[{var,44,'X'},{integer,44,1}]}},
                {var,45,'X'}]}]}]}},
    check_ac(E0).

ac4_test() ->
    E0 = {'fun',47,
          {clauses,
           [{clause,47,[],[],
             [{op,48,'+',
               {match,48,{var,48,'X'},{integer,48,1}},
               {match,48,{var,48,'X'},{integer,48,1}}}]}]}},
    check_ac(E0).

ac5_test() ->
    E0 = {'fun',47,
          {clauses,
           [{clause,47,[],[],
             [{call,48,{atom,48,'foo'},
               [{match,48,{var,48,'X'},{integer,48,1}},
                {match,48,{var,48,'X'},{integer,48,1}}]}]}]}},
    check_ac(E0).

ac6_test() ->
    E0 = {'case',46,{var,46,'Xs'},
          [{clause,47,[{nil,47}],[],[{var,47,'Ys'}]},
           {clause,48,
            [{cons,48,{var,48,'X'},{var,48,'Xs'}}],
            [],
            [{cons,48,
              {var,48,'X'},
              {call,48,{atom,48,ap},[{var,48,'Xs'},{var,48,'Ys'}]}}]}]},
    check_ac(E0).

ac7_test() ->
    E0 = {'block',66,
          [{'case',66,
            {var,66,'X'},
            [{clause,67,
              [{cons,67,{var,67,'A'},{var,67,'B'}}],
              [],
              [{atom,67,ok}]},
             {clause,68,
              [{var,68,'_'}],
              [],
              [{match,68,{var,68,'B'},{var,68,'X'}}]}]},
           {var,69,'B'}]},
    check_ac(E0).

ac8_test() ->
    E0 = read("case X of [dit|Xs] -> 0; [dat|Xs] -> 1 end, Xs"),
    check_ac(E0).

%% ac9_test() ->
%%     %% TODO: because X is not used after the expression it would be
%%     %% better if the two clauses were given different names for it,
%%     %% but it might not really matter. If it matters it is because
%%     %% it adds an additional constraint on renamings.
%%     E0 = read("case 1 of X -> X; X -> X end"),
%%     check_ac(E0),
%%     E = alpha_convert(#env{}, E0),
%%     {'case',_,_,[Clause1,Clause2]} = E,
%%     true = Clause1 =/= Clause2.

ac10_test() ->
    %% The case scrutinee introduces new variables and they are
    %% visible after the case, so all occurences of X and Y here must
    %% use the new names.
    E0 = read("case X=Y=1 of X=1 -> Y; X=2 -> X+Y end, X+Y"),
    {_,E1} = alpha_convert(#env{}, E0),
    {block,1,
     [{'case',1,
       {match,1,{var,1,Xnew},{match,1,{var,1,Ynew},{integer,1,1}}},
       [{clause,1,
         [{match,1,{var,1,Xnew},{integer,1,1}}],[],[{var,1,Ynew}]},
        {clause,1,
         [{match,1,{var,1,Xnew},{integer,1,2}}],[],
         [{op,1,'+',{var,1,Xnew},{var,1,Ynew}}]}]},
      {op,1,'+',{var,1,Xnew},{var,1,Ynew}}]} = E1.

ac11_test() ->
    %% New variables in guards.
    E0 = read("case X of Y when X==1,Y==1 -> X+Y end, X+Y"),
    {_,E1} = alpha_convert(#env{}, E0),
    {block,1,
     [{'case',1,
       {var,1,'X'},
       [{clause,1,
         [{var,1,Ynew}],
         [[{op,1,'==',{var,1,'X'},{integer,1,1}},
           {op,1,'==',{var,1,Ynew},{integer,1,1}}]],
         [{op,1,'+',{var,1,'X'},{var,1,Ynew}}]}]},
      {op,1,'+',{var,1,'X'},{var,1,Ynew}}]} = E1.

vars_test() ->
    E0 = {op,48,'+',
          {match,48,{var,48,'X'},{integer,48,1}},
          {match,48,{var,48,'Y'},{integer,48,1}}},
    ['X','Y'] = variables(E0),
    E1 = {op,48,'+',
          {match,48,{var,48,'Y'},{integer,48,1}},
          {match,48,{var,48,'X'},{integer,48,1}}},
    ['Y','X'] = variables(E1).



subst0_test() ->
    S0 = dict:from_list([{'X',{var,0,'Y'}}]),
    E0 = {var,1,'X'},
    {var,1,'Y'} = subst(S0,E0).

subst1_test() ->
    %% Test shadowing
    S0 = dict:from_list([{'X',{var,1,'Y'}},{'P',{var,1,'Q'}}]),
    E0 = {'fun',43,
          {clauses,
           [{clause,43,
             [{var,43,'X'},{var,43,'X'}],
             [],
             [{block,43,
               [{match,44,
                 {tuple,44,[{var,44,'X'},{var,44,'P'}]},
                 {tuple,44,[{var,44,'X'},{integer,44,1}]}},
                {var,45,'X'}]}]}]}},
    E1 = {'fun',43,
          {clauses,
           [{clause,43,
             [{var,43,'X'},{var,43,'X'}],
             [],
             [{block,43,
               [{match,44,
                 {tuple,44,[{var,44,'X'},{var,44,'Q'}]},
                 {tuple,44,[{var,44,'X'},{integer,44,1}]}},
                {var,45,'X'}]}]}]}},
    E1 = subst(S0, E0).

letrec_test() ->
    Fname = h,
    Arity = 3,
    Fun = {'fun',59,
           {clauses,
            [{clause,59,
              [{var,59,'Xs'},{var,59,'Ys'},{var,59,'Zs'}],
              [],
              [{var,50,'Xs'}]}]}},
    Call = {call,59,
            {var,59,h267},
            [{var,59,'Xs'},{var,59,'Ys'},{var,59,'Zs'}]},
    LR = make_letrec(0, [{Fname,Arity,Fun}], [Call]),
    {E,Funs} = extract_letrecs(LR),
    io:fwrite("E: ~p~nFuns: ~p~n", [E,Funs]),
    E = Call,
    [{Fname,Arity,Fun}] = Funs.

renaming0_test() ->
    true = is_renaming(sets:new(),
                       read("append(Xs,Xs)"),
                       read("append(Xs,Xs)")).

renaming1_test() ->
    true = is_renaming(sets:new(),
                       read("append(Xs,Xs)"),
                       read("append(Ys,Ys)")).

renaming2_test() ->
    true = is_renaming(sets:new(),
                       read("case 1 of X -> X end"),
                       read("case 1 of Y -> Y end")).

renaming3_test() ->
    true = is_renaming(sets:new(),
                       read("case 1 of X -> X end, X"),
                       read("case 1 of Y -> Y end, Y")).

renaming4_test() ->
    false = is_renaming(sets:new(),
                        read("case 1 of X -> X end, X"),
                        read("case 1 of Y -> Y end, X")).

renaming5_test() ->
    false = is_renaming(sets:new(),
                        read("case 1 of X -> X end, X"),
                        read("case 1 of Y -> X end, Y")).

renaming6_test() ->
    false = is_renaming(sets:new(),
                        read("append(Xs,Xs)"),
                        read("append(append(Xs,Ys),Zs)")).

renaming7_test() ->
    true = is_renaming(sets:new(), read("[X|Xs]"), read("[Y|Ys]")).

renaming8_test() ->
    false = is_renaming(sets:new(), read("[X,X|Xs]"), read("[X,Y|Ys]")).

renaming9_test() ->
    true = is_renaming(sets:new(), read("X+(-X)"), read("Y+(-Y)")).

renaming10_test() ->
    false = is_renaming(sets:new(), read("X+(-X)"), read("Y-(-Y)")).

renaming11_test() ->
    true = is_renaming(sets:new(), read("{X,Y,Z}"), read("{A,B,C}")).

renaming12_test() ->
    false = is_renaming(sets:new(), read("{X,Y,Z}"), read("{Z,Y,X}")).

renaming13_test() ->
    true = is_renaming(sets:new(),
                       read("fun (X) -> X * 100 end"),
                       read("fun (Y) -> Y * 100 end")).

renaming14_test() ->
    true = is_renaming(sets:new(),
                       read("fun (X0,Y0) -> X0+Y0 end"),
                       read("fun (Y1,X1) -> Y1+X1 end")).

renaming15_test() ->
    false = is_renaming(sets:new(),
                        read("fun (X,Y) -> [X|Y] end"),
                        read("fun (B,A) -> [A|B] end")).

linear0_test() ->
    true = is_linear('X', read("1+X")).

linear1_test() ->
    true = is_linear('X', read("Y=X+Z, Y")).

linear2_test() ->
    false = is_linear('X', read("Y=X+X, Y")).
