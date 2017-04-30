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

%% Pattern matching and guard utilities.

-module(scp_pattern).
-export([pattern_variables/1,
         find_constructor_clause/3,
         partition/3,
         find_matching_const/2,
         simplify_guard_seq/1,
         guard_seq_eval/1]).

-include("scp.hrl").
-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

%% List the variables used in a pattern.
pattern_variables(Expr) ->
    sets:to_list(erl_syntax_lib:variables(Expr)).

guard_variables(G) ->
    erl_syntax_lib:variables({clause,1,[],G,[{nil,1}]}).

%% E is a constructor and Cs0 is clauses from a case expression. The
%% job is to find the clause that matches E and return the bindings
%% needed for that clause. If it finds a matching clause it returns
%% {ok,Lhss,Rhss,Body}. It must completely eliminate the case
%% expression and the constructor (or return false).
find_constructor_clause(Bs, E, Cs) ->
    case fcc(Bs, E, Cs) of
        {ok,_,Lhss,Rhss,Body} ->
            ?DEBUG("fcc returns ~p", [{ok,Lhss,Rhss,Body}]),
            {ok,Lhss,Rhss,Body};
        X -> X
    end.
fcc(Bs, E0, Cs0) ->
    %% XXX: in this instance simplify only needs to look at one or two
    %% paths
    ?DEBUG("fcc(Bs, ~p,~n ~p)~n",[E0,Cs0]),
    case simplify(Bs, E0, Cs0) of
        {_,_,[]} ->
            %% All the clauses just disappeared, so there is no body
            %% and this probably is probably going to be a runtime
            %% error.
            ?DEBUG("fcc all clauses gone~n",[]),
            false;
        {{nil,_},nothing,[{{clause,L,[{nil,_}],[],Body},nothing}]} ->
            %% Now nothing remains of the case expression but a single
            %% body.
            ?DEBUG("fcc: body: ~p~n",[Body]),
            {ok,L,[],[],Body};
        {E0,nothing,SCs} ->
            %% The expression didn't change, but if the clauses
            %% changed then try again.
            Cs = [C || {C,nothing} <- SCs],
            case Cs of
                Cs0 -> false;
                _ -> fcc(Bs, E0, Cs)
            end;
        {E,nothing,SCs} ->
            %% A new expression and new clauses, so there may be more
            %% improvements to make.
            Cs = [C || {C,nothing} <- SCs],
            fcc(Bs, E, Cs);
        {E,Rhs,SCs} ->
            %% An expression was removed from the constructor and the
            %% clauses were modified accordingly. Right now there are
            %% possibly more clauses remaining, each with its own Lhs
            %% for the extracted Rhs.
            ?DEBUG("fcc extracts an expression!~n E: ~p~n Rhs: ~p~n SCs: ~p~n", [E,Rhs,SCs]),
            %% Simplify the rest of the case expression, remembering
            %% which Lhs each clause used.
            ASCs = [{clause,{Lhs,L},P,G,B} || {{clause,L,P,G,B},Lhs} <- SCs],
            case fcc(Bs, E, ASCs) of
                {ok,{Lhs0,L},Lhss,Rhss,Body} ->
                    %% XXX: the line info for Lhs is lost
                    Lhs = case Lhs0 of nothing -> '_'; _ -> Lhs0 end,
                    {ok,L,[{var,1,Lhs}|Lhss],[Rhs|Rhss],Body};
                _ ->
                    %% Trying further simplifications did not result
                    %% in full elimination of the case expressions.
                    false
            end;
        X ->
            %% Something more clever happened.
            ?DEBUG("fcc default: E=~p~n X=~p~n", [E0,X]),
            false
    end.


%% Partitions the function clauses and arguments into simple variables
%% and patterns. The simple variables from the clauses can make a
%% (classic) let expression and the rest must make a case expression.
%% Must not be clever about the function arguments.
%% Returns {ok,Lhss,Rhss,E,Cs}.
partition(Line, Cs0, As0) ->
    ?DEBUG("partition~n Cs0=~p~n As0=~p~n",[Cs0,As0]),
    Arity = length(As0),
    %% Annotate the clauses with a list of used variables (includes
    %% multiple occurences).
    ACs = lists:map(fun ({clause,L,Ps,G,B}) ->
                            Vs = lists:flatmap(fun scp_expr:variables/1,
                                               %% TODO: is it relevant
                                               %% to check the guard?
                                               Ps ++ lists:flatten(G)),
                            {aclause,L,Ps,G,B,Vs}
                    end, Cs0),
    %% For every argument, check if the corresponding pattern always
    %% is a simple variable.
    Ns = lists:flatmap(
           fun (N) ->
                   Ok = lists:all(
                          fun ({aclause,_,Ps,_,_,Vs}) ->
                                  case lists:nth(N, Ps) of
                                      {var,_,'_'} ->
                                          true;
                                      {var,_,V} ->
                                          not lists:member(V, lists:delete(V,Vs));
                                      _ -> false
                                  end
                          end, ACs),
                   case Ok of
                       true -> [N];
                       _ -> []
                   end
           end, lists:seq(1, Arity)),
    ?DEBUG("Ns = ~p~n",[Ns]),
    %% Pick a name for each simple variable.
    Lhss = lists:map(
             fun (N) ->
                     Vars = lists:flatmap(
                              fun ({clause,_,Ps,_,_}) ->
                                      case lists:nth(N, Ps) of
                                          {var,_,'_'} -> [];
                                          V={var,_,_} -> [V];
                                          _ -> []
                                      end
                              end,
                              Cs0),
                     case Vars of
                         [Var|_] -> Var;
                         [] -> '_'
                     end
             end, Ns),
    %% Pick out the corresponding right-hand sides.
    Rhss = lists:map(fun (N) -> lists:nth(N, As0) end, Ns),
    %% The case scrutinee is whatever is left of the arguments.
    E = remove_exprs(Line, Ns, As0),
    %% The simple variables are now removed from the clauses and the
    %% bodies are modified to use the names from Lhss.
    ?DEBUG("Lhss=~p Rhss=~p E=~p~n",[Lhss,Rhss,E]),
    Cs = update_clauses(Cs0, Ns, Lhss),
    ?DEBUG("Cs=~p~n",[Cs]),
    {ok,Lhss,Rhss,E,Cs}.

%% For each N in Ns: remove the Nth element from As0. Construct a new
%% expression suitable as a scrutinee.
remove_exprs(Line, Ns, As0) ->
    Es = lists:flatmap(fun ({N,A}) ->
                               case lists:member(N, Ns) of
                                   false -> [A];
                                   _ -> []
                               end
                       end,
                       lists:zip(lists:seq(1, length(As0)),
                                 As0)),
    exprs_to_expr(Line, Es).

exprs_to_expr(Line, []) -> {nil,Line};
exprs_to_expr(Line, [X]) -> X;
exprs_to_expr(Line, Xs) -> {tuple,Line,Xs}.

%% Update the clause so that pattern N is removed and the variable Lhs
%% is used instead of the removed variable.
update_clauses(Cs0, Ns, Lhss) ->
    %% Update the clauses to use the variables from Lhss and mark
    %% patterns for removal (replace them with []).
    Cs = update_clauses1(Cs0, Ns, Lhss),
    lists:map(fun ({clause,L,Ps0,G,B}) ->
                      Ps1 = lists:filter(fun ({atom,-1,remove}) -> false;
                                             (_) -> true
                                         end, Ps0),
                      %% If the scrutinee must become a tuple, then so
                      %% must the patterns.
                      Ps = [exprs_to_expr(L, Ps1)],
                      {clause,L,Ps,G,B}
              end, Cs).
update_clauses1(Cs, [], []) -> Cs;
update_clauses1(Cs0, [N|Ns], [Lhs={var,_,NewName}|Lhss]) ->
    Cs = lists:map(
           fun ({clause,L,Ps0,G,B}) ->
                   {var,_,OldName} = lists:nth(N, Ps0),
                   %% Mark the pattern for removal.
                   Ps = lists:sublist(Ps0, 1, N-1) ++ [{atom,-1,remove}] ++
                       lists:sublist(Ps0, N+1, length(Ps0)),
                   C = {clause,L,Ps,G,B},
                   case OldName of
                       '_' -> C;
                       NewName -> C;
                       _ ->
                           %% This clause used a different variable
                           %% name.
                           ?DEBUG("Use a new name: ~p => ~p~n",[OldName,Lhs]),
                           S = dict:from_list([{OldName,Lhs}]),
                           scp_expr:subst(S, C)
                   end
           end, Cs0),
    update_clauses1(Cs, Ns, Lhss).

%% Go over the list of clauses left to right and return the clauses
%% that could match the constant E. Each element returned is a tuple
%% {Taken,Clause}, where Taken==yes if it's certain that the clause
%% will be taken. Only works with constants and patterns that are
%% constants (or that bind to _). The caller does not want to deal
%% with binding a variable.
find_matching_const(E, Cs0) -> fmcc(E, Cs0).
fmcc(E={T,_,V}, [C={clause,_,[{T,_,V}],_,_}|Cs]) -> fmcc_cons(E, {yes,C}, Cs);
fmcc(E={T,_,_}, [C={clause,_,[{T,_,_}],_,_}|Cs]) -> fmcc(E, Cs);
fmcc(E={nil,_}, [C={clause,_,[{nil,_}],_,_}|Cs]) -> fmcc_cons(E, {yes,C}, Cs);
fmcc(E={nil,_}, [{clause,_,[{cons,_,_,_}],_,_}|Cs]) -> fmcc(E, Cs);
fmcc(E, [C={clause,_,[{var,_,'_'}],_,_}|Cs]) -> fmcc_cons(E, {yes,C}, Cs);
fmcc(E, [C|Cs]) -> [{maybe,C}|fmcc(E, Cs)];
fmcc(_, []) -> [].
fmcc_cons(E, C={Taken,{clause,L,P,Guard,B}}, Cs) ->
    case guard_seq_eval(simplify_guard_seq(Guard)) of
        true -> [{Taken,{clause,L,P,[],B}}];
        false -> fmcc(E, Cs);
        _ -> [C|fmcc(E, Cs)]
    end.

%% Statically evaluate a guard sequence.
guard_seq_eval([]) -> true;
guard_seq_eval([[{atom,_,true}]]) -> true;
guard_seq_eval([[{atom,_,_}]]) -> false;
guard_seq_eval(_G) -> maybe.

%% Simplify a guard sequence by doing constant folding and
%% simplifications. TODO: remove redundant guards but do not remove
%% the last guard, 'if' expressions can't have empty guard sequences.
simplify_guard_seq([G0|Gs]) ->
    G = [geval(X) || X <- G0],
    [G|Gs];
simplify_guard_seq([]) ->
    [].

geval(E={op,L,Op,A0,B0}) ->
    A = geval(A0),
    B = geval(B0),
    case scp_expr:apply_op(L, Op, A, B) of
        {ok,V} -> V;
        _ -> E
    end;
geval(E={call,Line,F0,As0}) ->
    F = geval(F0),
    As = [geval(X) || X <- As0],
    %% make_call knows some tricks. Get the result expression, because
    %% side-effects in guards aren't too important, and there are no
    %% blocks in guards.
    scp_expr:result_exp(scp_expr:make_call(Line,F,As));
geval(E) -> E.


%% Perform one pass of simplifications on a case expression. Given the
%% bound variables Bs and the expression E (which must be a
%% constructor), return a new E, an extracted expression and a new
%% list of clauses. Each clause may also have a variable name
%% associated with it, to which the extracted expression should be
%% bound.
simplify(Bs, E0, Cs0) ->
    ?DEBUG("simplify E0=~p~n Cs0=~p~n",[E0,Cs0]),
    {E1,Cs1} = trivial(E0, Cs0),
    ?DEBUG("trivial E1=~p~n Cs1=~p~n",[E1,Cs1]),
    Cs2 = impossible(Bs, E1, Cs1),
    ?DEBUG("impossible ~n Cs=~p~n",[Cs2]),
    case simplify_const(E1, Cs2) of
        {E,SCs} ->
            {E,nothing,SCs};
        _ ->
            {E3,Rhs,SCs} = common(Bs, E1, Cs2),
            ?DEBUG("common E=~p ~n SCs=~p~n",[E3,SCs]),
            {E3,Rhs,SCs}
    end.

simplify_const(E0, Cs0) when ?IS_CONST_EXPR(E0) ->
    %% If E0 is a constant and there's a matching clause, then
    %% simplify the constant to a nil.
    case find_matching_const(E0, Cs0) of
        [{yes,{clause,L,_,[],B}}] ->
            E = {nil,1},
            C = {clause,L,[E],[],B},
            {E,[{C,nothing}]};
        _ -> false
    end;
simplify_const(_, _) -> false.


%% TODO: couldn't common/3 remove these?
trivial(E0={tuple,_,[A]}, Cs0) ->
    %% Do not construct a tuple if it can be avoided.
    AllOne = lists:all(fun ({clause,_,[P],G,B}) ->
                               case P of
                                   {tuple,_,[_]} -> true;
                                   _ -> false
                               end
                       end, Cs0),
    if AllOne == true ->
            E = A,
            Cs = lists:map(fun ({clause,Lc,[{tuple,_,[P0]}],G,B}) ->
                                   {clause,Lc,[P0],G,B}
                           end, Cs0);
       true ->
            E = E0,
            Cs = Cs0
    end,
    {E, Cs};

trivial(E0={cons,_,H,{nil,_}}, Cs0) ->
    %% Do not cons if it can be avoided.
    AllOne = lists:all(fun ({clause,_,[P],_,_}) ->
                               case P of
                                   {cons,_,_,{nil,_}} -> true;
                                   _ -> false
                               end
                       end, Cs0),
    if AllOne == true ->
            Cs = lists:map(fun ({clause,Lc,[{cons,_,Car,_}],G,B}) ->
                                   %% Extract the car.
                                   {clause,Lc,[Car],G,B}
                           end, Cs0),
            {H, Cs};
       true ->
            {E0, Cs0}
    end;
trivial(E0, Cs0) ->
    {E0, Cs0}.

%% Remove impossible case clauses given the scrutinee E and a list of
%% clauses Cs. If it is impossible for a clause to match the
%% expression then it should not be returned. Should not look inside
%% the operands.
impossible(Bs, E, [C={clause,_,[{match,_,_,_}],_,_}|Cs]) ->
    %% Conservatively include all matches.
    imp_cons(Bs, E, C, Cs);
impossible(Bs, E, [C={clause,L,P=[{var,_,N}],Guard,B}|Cs]) ->
    %% Unbound variables can match anything.
    case sets:is_element(N, Bs) of
        true ->
            %% But this variable is bound.
            [C|impossible(Bs, E, Cs)];
        _ ->
            case guard_seq_eval(Guard) of
                true -> [{clause,L,P,[],B}];
                false -> impossible(Bs, E, Cs);
                _ -> [C|impossible(Bs, E, Cs)]
            end
    end;
impossible(Bs, E={tuple,_,Es1}, [C={clause,_,[{tuple,_,Es2}],_,_}|Cs])
  when length(Es1) == length(Es2) ->
    imp_cons(Bs, E, C, Cs);
impossible(Bs, E={tuple,_,_}, [C={clause,_,[{record,_,_,_,_}],_,_}|Cs]) ->
    %% Records are really tuples. TODO: could be improved if it knew
    %% the record definition
    imp_cons(Bs, E, C, Cs);
impossible(Bs, E={tuple,_,_}, [_|Cs]) ->
    impossible(Bs, E, Cs);
impossible(Bs, E={cons,_,_H,_T}, [C={clause,_,[{cons,_,_,_}],_,_}|Cs]) ->
    imp_cons(Bs, E, C, Cs);
impossible(Bs, E={cons,_,_H,_T}, [C={clause,_,[{string,_,_}],_,_}|Cs]) ->
    %% Strings are really conses.
    imp_cons(Bs, E, C, Cs);
impossible(Bs, E={cons,_,_H,_T}, [_|Cs]) ->
    impossible(Bs, E, Cs);
impossible(Bs, E, [C|Cs]) ->
    imp_cons(Bs, E, C, Cs);
impossible(Bs, _, []) ->
    [].

imp_cons(Bs, E, C={clause,_,_,Guard,_}, Cs) ->
    case guard_seq_eval(Guard) of
        false -> impossible(Bs, E, Cs);
        _ -> [C|impossible(Bs, E, Cs)]
    end.

%% Common field elimination. Returns {E',Rhs,SCs}. E' is a new
%% scrutinee for the case expression. Rhs is an expression extracted
%% from E. SCs is a list of {Clause',Lhs}, where Clause' is a new case
%% clause and Lhs should be substituted for Rhs in the body.
common(Bs, E0, Cs) ->
    %%common(Bs, E0, Cs, [[]|paths(E0)]).
    common(Bs, E0, Cs, [[],[1],[2]]).

common(Bs, E0, Cs, [Path|Ps]) ->
    case common_try(Bs, Path, E0, Cs) of
        X={E,Rhs,SCs} ->
            X;
        _ ->
            common(Bs, E0, Cs, Ps)
    end;
common(_, E0, Cs, []) ->
    common_default(E0, Cs).

common_try(Bs, Path, E0, Cs) ->
    case path_ref(Path, E0) of
        {ok,Rhs} ->
            ?DEBUG("Path: ~p, Rhs: ~p~n",[Path,Rhs]),
            %% TODO: if Rhs is a variable and it is used in a pattern
            %% more than once, then find all occurences in the
            %% patterns and see if, for each one, the same occurence
            %% is in E0. If so, remove all but one occurence.
            SCs = [reconcile(Bs, Path, Rhs, C) || C <- Cs],
            case lists:member(false,[Rhs|SCs]) of
                true ->
                    %% No improvements on this path.
                    ?DEBUG("Fail. SCs: ~p~n",[SCs]),
                    false;
                _ ->
                    ?DEBUG("Success. Rhs: ~p, SCs: ~p~n",[Rhs,SCs]),
                    E = path_elim(Path, E0),
                    ?DEBUG("E: ~p~n",[E]),
                    {E,Rhs,SCs}
            end;
        _ ->
            false
    end.

common_default(E0, Cs) ->
    {E0,nothing,[{C,nothing} || C <- Cs]}.

reconcile(_Bs, _Path, _Rhs, C={clause,_,[{var,_,'_'}],_,_}) ->
    %% This pattern matches anything, the structure of the scrutinee
    %% doesn't matter.
    {C,nothing};
reconcile(Bs, Path, Rhs, C={clause,L,[P0],G,B}) ->
    PExpr = path_ref(Path, P0),
    ?DEBUG("PExpr: ~p~n",[PExpr]),
    case [Rhs|PExpr] of
        [_|{ok,{var,_,'_'}}] ->
            %% This part of the pattern doesn't matter.
            P = path_elim(Path, P0),
            {{clause,L,[P],G,B},nothing};
        [{var,_,N}|{ok,{var,_,N}}] ->
            %% The same variable in both Rhs and the pattern. It's
            %% already bound, just eliminate it.
            P = path_elim(Path, P0),
            {{clause,L,[P],G,B},nothing};
        [_|{ok,{var,_,N}}] ->
            case sets:is_element(N, Bs) of
                true ->
                    %% This part of the pattern is a bound variable.
                    %% Can't know if it matches Rhs or not.
                    false;
                _ ->
                    P = path_elim(Path, P0),
                    InG = sets:is_element(N, guard_variables(G)),
                    InP = sets:is_element(N, erl_syntax_lib:variables(P)),
                    case InG orelse InP of
                        true ->
                            %% The variable is used in the guard or
                            %% was used twice in P0.
                            case InG of
                                true ->
                                    %% Try constant propagation.
                                    reconcile_guard(Rhs, N, C, P);
                                _ ->
                                    false
                            end;
                        _ ->
                            %% The variable can be replaced with Rhs.
                            {{clause,L,[P],G,B},N}
                    end
            end;
        %% TODO: more reconcilable stuff. It could also detect things
        %% that can't possibly match.
        _ ->
            %% There was no way to reconcile Rhs and PExpr.
            ?DEBUG("Irreconcilable:~n ~p~n ~p~n",[Rhs,PExpr]),
            false
    end.

%% The variable N is used in P0 on path Path, but also in other places
%% in P0 or G. It might be possible to use P by replacing the
%% occurences of N in G0 with Rhs.
reconcile_guard(Rhs, N, {clause,L,[P0],G0,B}, P) ->
    %% FIXME: must check if Rhs is a variable in split_vars
    ?DEBUG("Nonlinear variable: ~p in ~p or ~p~n", [N,P0,G0]),
    case erl_lint:is_guard_test(Rhs) of
        true ->
            ?DEBUG("Replace with ~p.~n",[Rhs]),
            S = dict:from_list([{N, Rhs}]),
            G = [[scp_expr:subst(S,X) || X <- Xs] || Xs <- G0],
            ?DEBUG("Afterwards: ~p~n", [{{clause,L,[P],G,B},N}]),
            {{clause,L,[P],simplify_guard_seq(G),B},N};
        _ ->
            false
    end.

-ifdef(TEST).
%% Find paths to all elements in an expression.
paths({cons,_,H,T}) ->
    [[1],[2]] ++
        [[1|P] || P <- paths(H)] ++
        [[2|P] || P <- paths(T)];
%% paths({tuple,_,As}) ->
%%     ;
paths(_) ->
    [].
-endif.

%% Walk a path over an expression, if possible.
path_ref([], X) -> {ok,X};
path_ref([1|Is], {cons,_,X,_}) -> path_ref(Is, X);
path_ref([2|Is], {cons,_,_,X}) -> path_ref(Is, X);
path_ref([N|Is], {tuple,_,As}) when N =< length(As) ->
    path_ref(Is, lists:nth(N,As));
path_ref(X,Y) ->
    false.

%% Remove the element referenced by the path. Must be able to handle
%% anything that path_ref handles.
path_elim([1], {cons,_,_,T}) -> T;
path_elim([1|Is], {cons,L,H,T}) -> {cons,L,path_elim(Is, H),T};
path_elim([2], {cons,_,H,_}) -> H;
path_elim([2|Is], {cons,L,H,T}) -> {cons,L,H,path_elim(Is, T)};
path_elim([N], {tuple,L,As0}) when N =< length(As0) ->
    As = lists:sublist(As0,1,N-1) ++
        lists:sublist(As0,N+1,length(As0)),
    {tuple,L,As};
path_elim([N|Is], {tuple,L,As0}) when N =< length(As0) ->
    As = lists:sublist(As0,1,N-1) ++
        path_elim(Is,lists:nth(N,As0)) ++
        lists:sublist(As0,N+1,length(As0)),
    {tuple,L,As};
path_elim([], _) ->
    %% This will be eliminated by find_matching_const/3
    {nil,1}.

%% EUnit tests.
-ifdef(TEST).

pv_test() ->
    %% XXX: sort...
    ['H','Y'] = pattern_variables({match,15,{var,15,'Y'},{match,15,{var,15,'H'},{integer,15,5}}}),
    ['X'] = pattern_variables({tuple,18,[{integer,18,1},{var,18,'X'}]}).

impossible_test() ->
    E = {atom,1,foo},
    Cs0 = [{clause,1,[{atom,1,bar}],[],[{integer,1,0}]},
           {clause,1,[{atom,1,foo}],[],[{integer,1,1}]}],
    Cs = impossible(sets:new(), E, Cs0),
    Cs = Cs0.

path_ref_test() ->
    E = scp_expr:read("[{the},{great,quux}]"),
    {ok,{atom,_,the}} = path_ref([1,1], E),
    {ok,{atom,_,great}} = path_ref([2,1,1], E),
    {ok,{atom,_,quux}} = path_ref([2,1,2], E).

path_elim_test() ->
    ABCD = scp_expr:read("[{a,b},{c,d}]"),
    BCD = scp_expr:read("[{b},{c,d}]"),
    CD = scp_expr:read("[{c,d}]"),
    CD = path_elim([1], ABCD),
    AB = scp_expr:read("{a,b}"),
    AB = path_elim([2], ABCD),
    ACD = scp_expr:read("[{a},{c,d}]"),
    ACD = path_elim([1,2], ABCD),
    ABD = scp_expr:read("[{a,b},{d}]"),
    ABD = path_elim([2,1,1], ABCD),
    ABC = scp_expr:read("[{a,b},{c}]"),
    ABC = path_elim([2,1,2], ABCD),
    {nil,_} = path_elim([], ABCD),
    {ok,ABCD} = path_ref([], ABCD).

paths_test() ->
    E = scp_expr:read("[{the},{great,quux}]"),
    Paths = paths(E),
    Values = [path_ref(P,E) || P <- Paths],
    Elims = [path_elim(P,E) || P <- Paths],
    ?DEBUG("Values: ~p~n", [Values]),
    ?DEBUG("Elims: ~p~n", [Elims]),
    ?DEBUG("Paths: ~p~n",[Paths]).

common_test() ->
    {'case',_,E0,Cs} = scp_expr:read("case {X,Y} of {_,[]} -> 1; {X1,[X2|X3]} -> 2 end"),
    {E,Rhs,SCs} = common(sets:new(), E0, Cs),
    ?DEBUG("E: ~p~nRhs: ~p~nSCs: ~p~n", [E,Rhs,SCs]),
    true = Rhs =/= nothing.

reconcile_test() ->
    P = {tuple,1,[{var,1,'_'}]},
    C0 = {clause,1,[P],[],[{nil,1}]},
    {C,nothing} = reconcile(sets:new(), [1], {var,1,'X'}, C0),
    ?DEBUG("C: ~p~n",[C]).

fcc_nil_test() ->
    E = {nil,1},
    Cs0 = [{clause,8,
            [{cons,8,{var,8,'Hd@6750'},{var,8,'Tail@664'}}],
            [],
            [{nil,3}]},
           {clause,1,[{nil,1}],[],[{nil,2}]}],
    Result = find_matching_const(E, Cs0),
    ?DEBUG("Result: ~p~n", [Result]),
    Result = [{yes,{clause,1,[{nil,1}],[],[{nil,2}]}}].

-endif.
