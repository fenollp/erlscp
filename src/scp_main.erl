%% -*- coding: utf-8; mode: erlang -*-
%% @copyright 2012, 2013 Göran Weinholt
%% @author Göran Weinholt <goran@weinholt.se>
%% @doc The driving algorithm in the supercompiler.

-module(scp_main).
-export([drive/3]).

-include("scp.hrl").

%% Contexts.
-record(op_ctxt, {line, op, e1=hole, e2=hole}). %op(e1, e2)
-record(op1_ctxt, {line, op}).              %op(<hole>)
-record(call_ctxt, {line, args}).           %<hole>(args)
-record(case_ctxt, {line, clauses}).        %case <hole> of clauses...
-record(match_ctxt, {line, pattern}).       %pattern = <hole>

%% Find the 'fun' expression for Name/Arity.
lookup_function(Env, K={Name,Arity}) ->
    case dict:find(K, Env#env.global) of
        {ok,Fun} ->
            {ok,Fun};
        _ ->
            dict:find(K, Env#env.local)
    end.

head_variables(Head) ->
    sets:from_list(lists:flatmap(fun scp_pattern:pattern_variables/1, Head)).

extend_bound(Env,Vars) ->
    Env#env{bound=sets:union(Env#env.bound, Vars)}.

%% The driving algorithm. The environment is used to pass information
%% downwards and upwards the stack. R is the current context.

drive(Env0, E, Ctxt) ->
    ?DEBUG("~nDRIVE:~n~p~n~p~n",[E,Ctxt]),
    drive0(Env0, E, Ctxt).

%% Evaluation rules.
drive0(Env0, E, Ctxt=[#case_ctxt{clauses=Cs0}|R]) when ?IS_CONST_EXPR(E) -> %R1
    %% E is a constant. One of the case clauses should match the
    %% constant exactly and have a true guard.
    %% TODO: strings may be better treated as conses
    ?DEBUG("R1~n",[]),
    case scp_pattern:find_matching_const(E, Cs0) of
        [{yes,{clause,L,P,[],B}}] ->
            drive(Env0, scp_expr:list_to_block(L, B), R);
        _ ->
            %% No clause matches the constant exactly. TODO: if the
            %% first case that matches binds the constant to a
            %% variable and that variable is not defined by every
            %% clause, then turn this case into a let
            build(Env0, E, Ctxt)
    end;

drive0(Env0, E2, Ctxt=[#op_ctxt{line=L, op=Op, e1=E1, e2=hole}|R])
  when ?IS_CONST_EXPR(E2) -> %R2
    ?DEBUG("R2~n",[]),
    case scp_expr:apply_op(L, Op, E1, E2) of
        {ok,V} -> drive(Env0, V, R);
        _ -> build(Env0, E2, Ctxt)
    end;
drive0(Env0, E1, Ctxt=[#op1_ctxt{line=L, op=Op}|R])
  when ?IS_CONST_EXPR(E1) -> %R2
    ?DEBUG("R2~n",[]),
    case scp_expr:apply_op(L, Op, E1) of
        {ok,V} -> drive(Env0, V, R);
        _ -> build(Env0, E1, Ctxt)
    end;

%% drive(Env0, E={'atom',L0,G}, R=[#call_ctxt{args=Args}|_]) -> %R3
%%     %% This is a function call to a local function or a BIF.
%%     Arity = length(Args),
%%     case lookup_function(Env0, {G, Arity}) of
%%         {ok,Fun} -> drive_call(Env0, E, L0, G, Arity, Fun, R);
%%         _ -> build(Env0, E, R)
%%     end;
%% drive(Env0, E={'fun',Lf,{function,G,Arity}}, R=[#call_ctxt{args=Args}|_])
%%   when length(Args) == Arity ->                 %R3 alternative syntax
%%     drive(Env0, {'atom',Lf,G}, R);
drive0(Env0, E={'fun',Lf,{function,G,Arity}}, R) -> %R3
    ?DEBUG("R3~n",[]),
    case lookup_function(Env0, {G, Arity}) of
        {ok,Fun} -> drive_call(Env0, E, Lf, G, Arity, Fun, R);
        _ -> build(Env0, E, R)
    end;

drive0(Env0, E0={constructor,L,Cons},
      Ctxt=[#call_ctxt{args=Args},#case_ctxt{clauses=Cs0}|R]) -> %R4
    ?DEBUG("R4~n",[]),
    E = scp_expr:make_call(L, E0, Args),
    ?DEBUG("Known constructor in a case.~n~p~n~p~n",[E,Ctxt]),
    case scp_pattern:find_constructor_clause(Env0#env.bound, E, Cs0) of
        {ok,Lhss,Rhss,Body} ->
            %% FIXME: if one Lhs was defined by every clause then this
            %% can't really become a let, because Lhs might be used
            %% after the case expression.
            drive(Env0, scp_expr:make_let(L, Lhss, Rhss, Body), R);
        _ ->
            %% Couldn't find a clause that simply matches the known
            %% constructor.
            build(Env0, E0, Ctxt)
    end;

drive0(Env0, {'fun',_,{clauses,[{clause,_,[],[],Body}]}},
      [#call_ctxt{line=L,args=[]}|R]) ->
    %% Let with no bindings.
    ?DEBUG("R7 end~n",[]),
    drive(Env0, scp_expr:list_to_block(L, Body), R);
drive0(Env0, {'fun',_,{clauses,[{clause,_,[{var,_,'_'}],[],Body0}]}},
      [#call_ctxt{line=L,args=[Rhs]}|R]) ->
    %% Let that ignores the result from Rhs.
    ?DEBUG("R7 ignore~n",[]),
    drive(Env0, scp_expr:list_to_block(L, [Rhs|Body0]), R);
%% drive0(Env0, {'fun',_,{clauses,[{clause,_,[LhsV={var,_,Lhs}],[],Body0}]}},
%%       [#call_ctxt{line=L,args=[Rhs]}|R]) ->     %R7/R8/R9
drive0(Env0, {call,L, {'fun',_,{clauses,[{clause,_,[LhsV={var,_,Lhs}],[],Body0}]}},
              [Rhs]},R) ->     %R7/R8/R9
    %% Let.
    ?DEBUG("R7/R8/R9~n",[]),
    Body1 = scp_expr:list_to_block(L, Body0),
    ?DEBUG("let!!!~n Lhs=~p Rhs=~p~n Body=~p~n",[Lhs,Rhs,Body1]),
    %% FIXME: Also ensure that Lhs is not used improperly in a pattern
    %% or guard.
    case scp_expr:terminates(Env0, Rhs)
        orelse (scp_expr:is_linear(Lhs, Body1)
                andalso scp_expr:is_strict(Lhs, Body1)) of
        true ->
            ?DEBUG("no residual let.~n",[]),
            E = scp_expr:subst(dict:from_list([{Lhs,Rhs}]), Body1),
            drive(Env0, E, R);
        _ ->
            {Env1,NewRhs} = drive(Env0, Rhs, []),
            case Env0#env.seen_vars==Env1#env.seen_vars
                andalso scp_expr:terminates(Env1, NewRhs) of
                true ->
                    %% When the Rhs was driven the seen_vars set did
                    %% not change, so clearly no new functions were
                    %% created. See the end of 4.8.1.3 in Jonsson's
                    %% Ph.D. thesis.
                    E = scp_expr:subst(dict:from_list([{Lhs,NewRhs}]), Body1),
                    drive(Env1, E, R);
                _ ->
                    ?DEBUG("residual let.~n",[]),
                    Env2 = extend_bound(Env1, sets:from_list([Lhs])),
                    {Env3,Body} = drive(Env2, Body1, R),
                    Env = Env3#env{bound = Env0#env.bound},
                    {Env,scp_expr:make_let(L, [LhsV], [NewRhs], [Body])}
            end
    end;

drive0(Env0, E0={'fun',_,{clauses,Cs0}}, Ctxt=[#call_ctxt{line=Lc, args=As}|R]) -> %R5
    ?DEBUG("R5~n",[]),
    %% The original rule simply uses a let, but Erlang's function
    %% clauses have built-in pattern matching. The arguments that
    %% require pattern matching become a case expression and the rest
    %% becomes a let.
    case lists:all(fun ({clause,_,Ps,_,_}) -> length(Ps) == length(As) end, Cs0) of
        true ->
            %%?DEBUG("inline. Cs0=~p~nAs=~p~n",[Cs0,As]),
            {ok,Lhss,Rhss,CaseE,Cs} = scp_pattern:partition(Lc, Cs0, As),
            {Env,Case} = scp_expr:alpha_convert(Env0, scp_expr:make_case(Lc, CaseE, Cs)),
            E = scp_expr:make_let(Lc, Lhss, Rhss, [Case]),
            drive(Env, E, R);
        _ ->
            %% Arity mismatch.
            build(Env0, E0, Ctxt)
    end;
drive0(Env0, {'fun',Line,{clauses,Cs0}}, R) ->   %R6
    ?DEBUG("R6~n",[]),
    {Env,Cs} = drive_clauses(Env0, Cs0),
    build(Env, {'fun',Line,{clauses,Cs}}, R);

drive0(Env0, E={'call',Line,{'fun',1,{function,scp_expr,letrec,1}},[Arg]}, R) ->
    ?DEBUG("R9rec~n",[]),
    %% Letrec.
    io:fwrite("driving letrec: ~p~n",[E]),
    {Bs,Body} = scp_expr:letrec_destruct(E),
    Local = lists:foldl(fun ({Name,Arity,Rhs},L) ->
                                dict:store({Name,Arity}, Rhs, L)
                        end,
                        Env0#env.local, Bs),
    Env1 = Env0#env{local=Local},
    {Env, Expr} = drive(Env1, scp_expr:list_to_block(Line, Body), R),
    {Env#env{local=Env0#env.local},Expr};

drive0(Env0, E={'block',Lb,[{'match',Lm,P0,E0},Rest]}, R) ->
    ?DEBUG("R match/block~n",[]),
    drive(Env0, scp_expr:make_case(Lb, E0, [{clause,Lm,[P0],[],[Rest]}]), R);
drive0(Env0, {'block',Line,[A0,B0]}, R) ->
    %% TODO: have the driving of case, match, etc save up a list of
    %% variables that will become bound in B.
    ?DEBUG("R block~n",[]),
    {Env1, A} = drive(Env0, A0, []),
    {Env, B} = drive(Env1, B0, R),
    {Env, scp_expr:make_block(Line, A, B)};
drive0(Env0, {'block',Line,Es}, R) ->
    drive(Env0, scp_expr:list_to_block(Line, Es), R);

%% Focusing rules.
drive0(Env0, E, Ctxt=[#op_ctxt{line=L, op=Op, e1=hole, e2=E2}|R])
  when ?IS_CONST_EXPR(E) -> %R10
    ?DEBUG("R10~n",[]),
    drive(Env0, E2, [#op_ctxt{line=L, op=Op, e1=E}|R]);

drive0(Env0, {op,L,Op,E1,E2}, R) ->              %R11
    ?DEBUG("R11~n",[]),
    drive(Env0, E1, [#op_ctxt{line=L, op=Op, e2=E2}|R]);
drive0(Env0, {op,L,Op,E}, R) ->                  %R11
    ?DEBUG("R11~n",[]),
    drive(Env0, E, [#op1_ctxt{line=L, op=Op}|R]);

drive0(Env0, {'call',L,X={atom,La,N},Args}, R) ->            %R12
    ?DEBUG("R12: ~p~n~n",[X]),
    drive(Env0, {'fun',La,{function,N,length(Args)}}, [#call_ctxt{line=L, args=Args}|R]);
drive0(Env0, {'call',L,F,Args}, R) ->            %R12
    ?DEBUG("R12: ~p~n~n",[F]),
    drive(Env0, F, [#call_ctxt{line=L, args=Args}|R]);
drive0(Env0, {cons,L,H,T}, R) ->                 %R12 for cons
    ?DEBUG("R12cons~n",[]),
    drive(Env0, {constructor,L,cons}, [#call_ctxt{line=L, args=[H,T]}|R]);
drive0(Env0, {tuple,L,Es}, R) ->                 %R12 for tuple
    ?DEBUG("R12tuple~n",[]),
    drive(Env0, {constructor,L,tuple}, [#call_ctxt{line=L, args=Es}|R]);

drive0(Env0, {'match',L,P,E}, R) ->
    %% XXX: pushes match into case clauses etc
    ?DEBUG("R match~n",[]),
    drive(Env0, E, [#match_ctxt{line=L,pattern=P}|R]);

drive0(Env0, {'case',L,E,Cs}, R) ->              %R13
    ?DEBUG("R13~n",[]),
    drive(Env0, E, [#case_ctxt{line=L, clauses=Cs}|R]);

drive0(Env0, {'if',L,Cs}, R) ->
    ?DEBUG("R if~n",[]),
    drive_if(Env0, L, Cs, R);

%% Fallthrough.
drive0(Env0, Expr, R) ->                         %R14
    ?DEBUG("R14~n",[]),
    build(Env0, Expr, R).

%% Rebuilding expressions.
build(Env0, Expr, [#op_ctxt{line=Line, op=Op, e1=hole, e2=E2}|R]) ->        %R15
    ?DEBUG("R15~n",[]),
    {Env1,E} = drive(Env0, E2, []),
    build(Env1, {op,Line,Op,Expr,E}, R);
build(Env0, Expr, [#op_ctxt{line=Line, op=Op, e1=E1, e2=hole}|R]) ->        %R16
    ?DEBUG("R16~n",[]),
    build(Env0, {op,Line,Op,E1,Expr}, R);
build(Env0, Expr, [#call_ctxt{line=Line, args=Args0}|R]) -> %R17
    ?DEBUG("R17~n",[]),
    {Env,Args} = drive_list(Env0, fun drive/3, Args0),
    build(Env, scp_expr:make_call(Line,Expr,Args), R);

build(Env0, Expr, Ctxt=[#case_ctxt{line=Line, clauses=Cs0}|R]) -> %R18/R19
    build_case(Env0, Expr, Ctxt);
    %%build_case_simp(Env0, Expr, Ctxt);
build(Env0, Expr, [#op1_ctxt{line=Line, op=Op}|R]) ->
    ?DEBUG("R15/16 op1~n",[]),
    build(Env0, {op,Line,Op,Expr}, R);
build(Env0, Expr, [#match_ctxt{line=Line, pattern=P}|R]) ->
    ?DEBUG("R build match~n",[]),
    build(Env0, {match,Line,P,Expr}, R);

build(Env, Expr, []) ->                         %R20
    ?DEBUG("R20~n",[]),
    {Env, Expr}.

build_case(Env0, Expr={var,_,Name}, [#case_ctxt{line=Line, clauses=Cs0}|R]) -> %R18
    %% Try to substitute the variable for the pattern in clauses.
    ?DEBUG("R18~n",[]),
    CRs = lists:map(fun (C0={clause,Lc,[P],G0,B0}) when
                              ?IS_CONST_EXPR(P);
                              element(1,P)=='var', element(3,P) =/= '_' ->
                            %% TODO: investigate if this rule should
                            %% be more powerful
                            S = dict:from_list([{Name,P}]),
                            ?DEBUG("R18! Name=~p P=~p~nC0=~p R=~p~n",[Name,P,C0,R]),
                            {scp_expr:subst(S, C0), ctxt_subst(S, R)};
                        (C) ->
                            %% Nothing interesting happened today.
                            {C,R}
                    end, Cs0),
    {Cs,Rs} = lists:unzip(CRs),
    build_case_final(Env0, Line, Expr, Cs, Rs);
build_case(Env0, Expr, [#case_ctxt{line=Line, clauses=Cs0}|R]) -> %R19
    ?DEBUG("R19~n",[]),
    build_case_final(Env0, Line, Expr, Cs0, lists:duplicate(length(Cs0), R)).

build_case_final(Env0, Line, Expr, Cs0, Rs) ->
    %% Drive every clause body in the corresponding R context.
    {Cs1,Env1} = lists:mapfoldl(
                   fun ({{clause,Lc,H0,G0,B0},R},Env00) ->
                           Vars = head_variables(H0),
                           Env01 = extend_bound(Env00, Vars),
                           B1 = scp_expr:list_to_block(Lc, B0),
                           {Env02,B} = drive(Env01, B1, R),
                           Env03 = Env02#env{bound=Env00#env.bound},
                           {{clause,Lc,H0,G0,[B]},Env03}
                   end,
                   Env0, lists:zip(Cs0,Rs)),
    %% FIXME: find the new bindings going out of the case expr
    Case = scp_expr:make_case(Line, Expr, Cs1),
    {Env1, Case}.


%% Driving of if expressions.
drive_if(Env0, L, Cs0, R) -> drive_if(Env0, L, Cs0, R, []).

drive_if(Env0, Line, [{clause,Lc,[],G0,B0}|Cs], R, Acc) ->
    B1 = scp_expr:list_to_block(Lc, B0),
    G = scp_pattern:simplify_guard_seq(G0),
    case scp_pattern:guard_seq_eval(G) of
        true when Acc == [] ->
            %% The guard is always true and there were no other
            %% clauses before this one. Eliminate the if expression
            %% completely.
            drive(Env0, B1, R);
        true ->
            %% The guard is always true. Remove the rest of the
            %% clauses.
            drive_if1(Env0, Line, Lc, G, B1, [], R, Acc);
        false when Cs =/= []; Acc =/= [] ->
            %% The guard is always false and this is not the only
            %% clause left. Remove the clause.
            drive_if(Env0, Line, Cs, R, Acc);
        _ ->
            %% This clause is maybe true or it is the last clause
            %% which is always false.
            drive_if1(Env0, Line, Lc, G, B1, Cs, R, Acc)
    end;
drive_if(Env0, Line, [], _R, Acc) ->
    %% FIXME: find the new bindings going out of the if expr
    {Env0, scp_expr:make_if(Line, lists:reverse(Acc))}.

drive_if1(Env0, Line, Lc, G, B0, Cs, R, Acc) ->
    %% Drive a single if clause in the R context (thereby pushing R
    %% into the clause body).
    {Env1,B} = drive(Env0, B0, R),
    %% New bindings in one clause are not transmitted to the next
    %% clause.
    Env2 = Env1#env{bound=Env0#env.bound},
    C = {clause,Lc,[],G,[B]},
    drive_if(Env2, Line, Cs, R, [C|Acc]).

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
    Vars = head_variables(Head),
    Env1 = extend_bound(Env0, Vars),
    {Env2,Body} = drive(Env1, scp_expr:list_to_block(L, Body0), []),
    Env = Env2#env{bound=Env0#env.bound},
    {Env,{clause,L,Head,Guard,[Body]}}.

%% Driving of function calls. First try to find a renaming of an old
%% expression. Then try to find a homeomorphic embedding. Then if that
%% doesn't work, make a new function.
drive_call(Env0, Funterm, Line, Name, Arity, Fun0, R) ->
    %% It is safe to return {Env0,L} if things become difficult.
    ?DEBUG("Call: ~p, ~w/~w, R: ~p~n", [Funterm,Name,Arity,R]),
    ?DEBUG("Fun: ~p~n", [Fun0]),
    L = plug(Funterm, R),
    %% TODO: there will be trouble if some of the free variables of L
    %% appear multiple times and there is a folding or a new function.
    FV = scp_expr:free_variables(Env0#env.bound, L),
    %% First try to find a renaming.
    case scp_expr:find_renaming(Env0, L) of
        {ok,Fname} ->
            %% L is a renaming of an old expression.
            ?DEBUG("Folding. Fname=~p, FV=~p~n",[Fname,FV]),
            case FV of
                [] ->
                    Expr={'atom',Line,Fname};
                _ ->
                    Expr={'call',Line,{atom,Line,Fname},[{var,Line,X} || X <- FV]}
            end,
            {Env0#env{found=[Fname|Env0#env.found]},Expr};
        _ ->
            %% Next try to find a homeomorphic embedding.
            case Env0#env.whistle_enabled
                andalso scp_generalize:find_homeomorphic_embeddings(Env0, L) of
                {ok,Embeddings} ->
                    ?DEBUG("The whistle! ~p~n", [Embeddings]),
                    ?DEBUG("L: ~p~n", [L]),
                    Refl = lists:filter(
                             fun ({_Fname,OldExpr}) ->
                                     scp_generalize:whistle(L, OldExpr)
                             end,
                             Embeddings),
                    ?DEBUG("Refl: ~p~n", [Refl]),
                    case Refl of
                        [] ->
                            %% Generalize against the old expression.
                            [{_,OldExpr}|_] = Embeddings,
                            generalize(Env0, L, OldExpr);
                        [{Fname,_OldExpr}|_] ->
                            %% Upwards generalization.
                            {Env1,G} = scp_expr:gensym(Env0, "Intermediate"),
                            Env2 = Env1#env{w=[{Fname,L}|Env1#env.w]},
                            ?DEBUG("Upwards generalization. W=~p~n",[Env2#env.w]),
                            {Env2,{var,Line,G}}
                    end;
                _ ->
                    ?DEBUG("making a new function for: ~p~n", [L]),
                    %% Neither a renaming nor an embedding.
                    {Env1,Fname} = scp_expr:gensym(Env0, Env0#env.name),
                    {Env2,Fun} = scp_expr:alpha_convert(Env1, Fun0),
                    %% Remember that Fname came from the expression L.
                    Env3 = Env2#env{ls = [{Fname,L}|Env2#env.ls]},
                    %%?DEBUG("Before: ~p~nAfter: ~p~n", [Fun0,Fun]),
                    %% Drive the fun in the original context. If the context is a
                    %% call_ctxt then this might do inlining.
                    {Env4,E} = drive(Env3, Fun, R),
                    ?DEBUG("After driving the fun: ~p~n", [E]),
                    {Env5,S} = scp_expr:fresh_variables(Env4, dict:new(), FV),
                    %% The line numbers are probably going to be a bit wrong.
                    ?DEBUG("W? ~p ~p~n",[Fname, Env5#env.w]),
                    case lists:keysearch(Fname, 1, Env5#env.w) of
                        {value, {_, Expr}} ->
                            ?DEBUG("Upwards generalization. ~p~n",[Expr]),
                            Env6 = Env0#env{seen_vars=Env5#env.seen_vars},
                            generalize(Env6, L, Expr);
                        _ ->
                            case lists:member(Fname, Env5#env.found) of
                                false ->
                                    %% Fname was never used in E, so there is no need
                                    %% to residualize a new function. This basically
                                    %% inlines what would otherwise be a new function.
                                    {Env5#env{ls=Env2#env.ls},E};
                                _ ->
                                    Head = [scp_expr:subst(S, {var,Line,X}) || X <- FV],
                                    %% ?DEBUG("S: ~p~n", [S]),
                                    ?DEBUG("Free variables in ~p: ~w~n", [L,FV]),
                                    %% ?DEBUG("Head: ~p~n",[Head]),
                                    Guard = [],
                                    ?DEBUG("E: ~p~n",[E]),
                                    Body = scp_expr:subst(S, E),
                                    case FV of
                                        [] ->
                                            NewFun0 = E,
                                            NewTerm = {atom,Line,Fname};
                                        _ ->
                                            NewFun0 = {'fun',Line,
                                                       {clauses,
                                                        [{clause,Line,Head,Guard,[Body]}]}},
                                            NewTerm = {'call',Line,{atom,Line,Fname},
                                                       [{var,Line,X} || X <- FV]}
                                    end,
                                    ?DEBUG("NewFun0: ~p~n",[NewFun0]),
                                    ?DEBUG("NewTerm: ~p~n",[NewTerm]),
                                    {Env6,NewFun} = scp_expr:alpha_convert(Env5, NewFun0),
                                    ?DEBUG("NewFun: ~p ~p~n",[Fname,NewFun]),
                                    %% This letrec will become a top-level function later.
                                    Farity = erl_syntax:fun_expr_arity(NewFun),
                                    Letrec = scp_expr:make_letrec(Line,
                                                                  [{Fname,Farity,NewFun}],
                                                                  [NewTerm]),
                                    ?DEBUG("Letrec: ~p~n",[Letrec]),
                                    {Env6#env{ls=Env2#env.ls},Letrec}
                            end
                    end
            end
    end.

%% Simplifications on case expressions.
build_case_simp(Env0, E0, Ctxt=[CR=#case_ctxt{clauses=Cs0, line=Line}|R]) ->
    case scp_pattern:simplify(Env0#env.bound, E0, Cs0) of
        {_,_,[]} ->
            %% All the clauses disappeared. Preserve the error in the
            %% residual program.
            build_case(Env0, E0, Ctxt);
        {E0,nothing,SCs} ->
            Cs = [C || {C,nothing} <- SCs],
            case Cs of
                Cs0 ->
                    %% The expression didn't change and neither did
                    %% the clauses.
                    build_case(Env0, E0, Ctxt);
                _ ->
                    %% The expression didn't change, but some clauses
                    %% may have been removed.
                    build(Env0, E0, [CR#case_ctxt{clauses=Cs}|R])
            end;
        {E,nothing,SCs} ->
            %% A new expression, so driving might improve it further.
            Cs = [C || {C,nothing} <- SCs],
            drive(Env0, E, [CR#case_ctxt{clauses=Cs}|R]);
        {E,Rhs0,SCs} ->
            %% An expression was removed from the constructor.
            ?DEBUG("Stuff happens: E=~p~n Rhs0=~p~n SCs=~p~n", [E,Rhs0,SCs]),
            Cs1 = rebuild_clauses(Env0, Rhs0, SCs),
            case lists:member(false, Cs1) of
                true ->
                    build_case(Env0, E0, Ctxt);
                %% true ->
                %%     %% It wasn't possible to simply substitute the Lhs
                %%     %% in every clause. Bind Rhs0 to a new variable
                %%     %% and do the substitution with that instead. More
                %%     %% problematic than the equivalent let rule
                %%     %% because case can "leak" variables.
                %%     ?DEBUG("build_case_simp makes a block~n",[]),
                %%     {Env1,Rhs} = build(Env0, Rhs0, []),
                %%     {Env2,Var} = scp_expr:gensym(Env1, "P"),
                %%     Cs2 = rebuild_clauses(Env2, {var,Line,Var}, SCs),
                %%     Match = {match,Line,{var,Line,Var},Rhs},
                %%     Env3 = extend_bound(Env2, sets:from_list([Var])),
                %%     {Env4,Case} = build(Env3, E, [CR#case_ctxt{clauses=Cs2}|R]),
                %%     Block = scp_expr:make_block(Line, Match, Case),
                %%     ?DEBUG("block=~p~n", [Block]),
                %%     {Env4,Block};
                false ->
                    NewCtxt = [CR#case_ctxt{clauses=Cs1}|R],
                    case lists:all(fun ({_,nothing}) -> true;
                                       ({_,_}) -> false
                                   end, SCs) of
                        true ->
                            %% Lhs=nothing for all SCs, must
                            %% residualize Rhs for effect.
                            ?DEBUG("Residualized Rhs0=~p Cs1=~p~n", [Rhs0, Cs1]),
                            build(Env0, scp_expr:make_block(Line, Rhs0, E), NewCtxt);
                        false ->
                            %% Lhs in each clause was substituted for Rhs.
                            ?DEBUG("Stuff was easy. Cs1=~p~n",[Cs1]),
                            build(Env0, E, NewCtxt)
                    end
            end;
        Foo ->
            %% Something more clever happened.
            ?DEBUG("constructor case default: E=~p~n Ctxt=~p~n Foo=~p~n", [E0,Ctxt,Foo]),
            build_case(Env0, E0, Ctxt)
    end.

rebuild_clauses(Env, Rhs, [{C0,nothing}|SCs]) ->
    [C0|rebuild_clauses(Env, Rhs, SCs)];
rebuild_clauses(Env, Rhs, [{C0,Lhs}|SCs]) ->
    %% Replace Lhs with Rhs in the body, if it's semantically ok.
    {clause,L,P,G,B0} = C0,
    %% FIXME: if Lhs ever appears in a guard, then Rhs must be a legal
    %% guard expression.
    case scp_expr:terminates(Env, Rhs)
        orelse (scp_expr:is_linear(Lhs, scp_expr:list_to_block(0, B0))
                andalso scp_expr:is_strict(Lhs, scp_expr:list_to_block(0, B0))) of
        true ->
            S = dict:from_list([{Lhs,Rhs}]),
            B = [scp_expr:subst(S, X) || X <- B0],
            C = {clause,L,P,G,B},
            [C|rebuild_clauses(Env, Rhs, SCs)];
        _ ->
            [false]
    end;
rebuild_clauses(_, _, []) ->
    [].

%% Plug an expression into a context.
plug(Expr, [#call_ctxt{line=Line, args=Args}|R]) ->
    plug({call,Line,Expr,Args}, R);
plug(Expr, [#case_ctxt{line=Line, clauses=Cs}|R]) ->
    plug(scp_expr:make_case(Line,Expr,Cs), R);
plug(Expr, [#match_ctxt{line=Line, pattern=P}|R]) ->
    plug({match,Line,Expr,P}, R);
plug(Expr, [#op_ctxt{line=Line, op=Op, e1=hole, e2=E2}|R]) ->
    plug({op,Line,Op,Expr,E2}, R);
plug(Expr, [#op_ctxt{line=Line, op=Op, e1=E1, e2=hole}|R]) ->
    plug({op,Line,Op,E1,Expr}, R);
plug(Expr, [#op1_ctxt{line=Line, op=Op}|R]) ->
    plug({op,Line,Op,Expr}, R);
plug(Expr, []) ->
    Expr.

%% Perform a substitution on a context.
ctxt_subst(S, [C=#call_ctxt{args=Xs}|R]) ->
    [C#call_ctxt{args=[scp_expr:subst(S,X) || X <- Xs]}|
     ctxt_subst(S, R)];
ctxt_subst(S, [C=#case_ctxt{clauses=Xs}|R]) ->
    [C#case_ctxt{clauses=[scp_expr:subst(S,X) || X <- Xs]}|
     ctxt_subst(S, R)];
ctxt_subst(S, [C=#match_ctxt{pattern=X}|R]) ->
    [C#match_ctxt{pattern=scp_expr:subst(S,X)}|
     ctxt_subst(S, R)];
ctxt_subst(S, [C=#op_ctxt{e1=hole, e2=X}|R]) ->
    [C#op_ctxt{e2=scp_expr:subst(S,X)}|
     ctxt_subst(S, R)];
ctxt_subst(S, [C=#op_ctxt{e1=X, e2=hole}|R]) ->
    [C#op_ctxt{e1=scp_expr:subst(S,X)}|
     ctxt_subst(S, R)];
ctxt_subst(S, [C=#op1_ctxt{}|R]) ->
    [C|ctxt_subst(S, R)];
ctxt_subst(_, []) ->
    [].

%% Generalization.
generalize(Env0, E1, E2) ->
    ?DEBUG("gen: ~p ~n    ~p~n",[E1,E2]),
    {Env1,Expr0,Subst0} = case scp_generalize:msg(Env0, E1, E2) of
                              {_,{var,_,_},_} ->
                                  ?DEBUG("splitting instead~n",[]),
                                  scp_generalize:split(Env0, E1);
                              X -> X
                          end,
    ?DEBUG("Expr0: ~p~nSubst0: ~p~n",[Expr0,dict:to_list(Subst0)]),
    SplitVars = dict:fetch_keys(Subst0),
    SplitVarsSet = sets:from_list(SplitVars),
    %% Expr0 is a simpler version of E1.
    Env2 = Env1#env{split_vars=SplitVars ++ Env1#env.split_vars,
                    bound=sets:union(SplitVarsSet, Env1#env.bound)},
    {Env3,Expr1} = drive(Env2, Expr0, []),
    Env4 = Env3#env{bound=Env0#env.bound},
    %% Drive the right-hand sides of the substitution, yielding a new
    %% substitution.
    SubstList = dict:to_list(Subst0),
    {Env5,Rhss} = drive_list(Env4, fun drive/3, [Rhs||{_,Rhs}<-SubstList]),
    Subst = dict:from_list(lists:zipwith(fun ({Lhs,_},Rhs) ->
                                                 {Lhs,Rhs}
                                         end,
                                         SubstList, Rhss)),
    %% Apply the new substitution to the driven simplification of E1.
    %% The subexpressions of E1 and E1 itself has now been driven in
    %% the empty context.
    %% TODO: is it possible that Expr1 does not contain all the split
    %% variables now? If so, must residualize for effect.
    ?DEBUG("Expr1: ~p~nSubst: ~p~n",[Expr1,dict:to_list(Subst)]),
    Expr = scp_expr:subst(Subst, Expr1),
    %% The bindings going out is the union of the new bindings in Expr
    %% and the split expressions.
    Env = Env5#env{bound=sets:subtract(sets:union(Env3#env.bound, Env5#env.bound),
                                       SplitVarsSet),
                   split_vars=Env0#env.split_vars},
    {Env, Expr}.

%% EUnit tests.

build_test() ->
    {_,{integer,0,123}} = drive(#env{}, {integer,0,123}, []),
    Fun = {'fun',1, {clauses, [{clause,1,[{var,1,'X'}], [], [{var,2,'X'}]}]}},
    drive(#env{}, Fun, []).

residualize_test() ->
    %% When something is removed from the scrutinee it must either be
    %% side-effect free or else be residualized for effect.
    E0 = scp_expr:read("case [1|length(U)] of [X|_] -> 1 end"),
    {Env,E} = drive(#env{}, E0, []),
    io:fwrite("E=~p~n",[E]),
    ['U'] = scp_expr:variables(E).
