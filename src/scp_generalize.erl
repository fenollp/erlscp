%% -*- coding: utf-8; mode: erlang -*-
%% @copyright 2012 Göran Weinholt
%% @author Göran Weinholt <goran@weinholt.se>
%% @doc Homeomorphic embedding and most specific generalization.

-module(scp_generalize).
-export([find_homeomorphic_embeddings/2,
         whistle/2,
         split/2,
         msg/3]).
-include("scp.hrl").

%% Find old expressions that are homeomorphically embedded in Expr.
find_homeomorphic_embeddings(Env, Expr) ->
    Xs = lists:filter(fun ({_FName,OldExpr}) ->
                              whistle(OldExpr, Expr)
                      end,
                      Env#env.ls),
    case Xs of
        [] -> false;
        _ -> {ok,Xs}
    end.

%% The homeomorphic embedding test or "the whistle".
whistle(E1, E2) ->
    whistle(E1, E2, false).
whistle(E1, E2, InFun) ->
    peel(E1, E2, InFun) orelse
        lists:any(fun (E) -> whistle(E1, E, InFun) end,
                  dive(E2)).

%% Diving. Extract all subexpressions except patterns and guards.
dive({clause,_,_,_,B}) -> B;
dive(E) -> lists:flatten(subtrees(E)).

%% Peeling matches subterms. Also known as coupling.
peel(E1, E2, InFun) ->
    X = peel0(E1, E2, InFun),
    %%io:fwrite("peel ~p~n     ~p =>   ~p~n",[E1,E2,X]),
    X.
peel0(E1, E2, InFun) ->
    Type1 = erl_syntax:type(E1),
    Type2 = erl_syntax:type(E2),
    Es1 = lists:flatten(subtrees(E1)),
    Es2 = lists:flatten(subtrees(E2)),
    case Type1 of
        Type2 when length(Es1) == length(Es2) ->
            case Type1 of
                atom when InFun ->
                    A1 = erl_syntax:atom_value(E1),
                    A2 = erl_syntax:atom_value(E2),
                    A1 == A2;
                integer when InFun =/= false ->
                   erl_syntax:integer_value(E1) ==
                        erl_syntax:integer_value(E2);
                clause ->
                    B1 = erl_syntax:clause_body(E1),
                    B2 = erl_syntax:clause_body(E2),
                    length(B1) == length(B2) andalso
                        peel_list(B1, B2, InFun);
                module_qualifier ->
                    peel_list(Es1, Es2, true);
                arity_qualifier ->
                    peel_list(Es1, Es2, true);
                application ->
                    whistle(application_operator(E1),
                            application_operator(E2),
                            InFun) andalso
                        peel_list(erl_syntax:application_arguments(E1),
                                  erl_syntax:application_arguments(E2),
                                  InFun);
                _ ->
                    peel_list(Es1, Es2, InFun)
            end;
        _ -> false
    end.

peel_list(Es1, Es2, InFun) ->
    lists:all(fun ({E1,E2}) -> whistle(E1, E2, InFun) end,
              lists:zip(Es1, Es2)).

subtrees({cons,_,H,T}) ->
    [H,T];
subtrees(E) ->
    erl_syntax:subtrees(E).

application_operator(App) ->
    Op = erl_syntax:application_operator(App),
    case erl_syntax:type(Op) of
        atom ->
            Arity0 = length(erl_syntax:application_arguments(App)),
            Arity1 = erl_syntax:integer(Arity0),
            Arity = erl_syntax:copy_pos(Op, Arity1),
            Fun = erl_syntax:implicit_fun(Op, Arity),
            erl_syntax:copy_pos(Op, Fun);
        _ -> Op
    end.

%% Generate a new name for each element in Es. Returns
%% {NewEnv,NewNames,Substitution}.
gensyms(Env0, Line, Prefix, Es) ->
    {NewNames,{NewEnv,Subst}} =
        lists:mapfoldl(fun (E, {Env1,S0}) ->
                               {Env,N} = scp_expr:gensym(Env1, Prefix),
                               V = {var,Line,N},
                               S = dict:store(N, E, S0),
                               {V,{Env,S}}
                       end,
                       {Env0,dict:new()},
                       Es),
    {NewEnv,NewNames,Subst}.

%% This takes an expression and splits it into smaller parts. Returns
%% {NewEnv,NewExpr,Substitution}. The original expression can be
%% recovered by applying the substitution to the new expression.
split(Env0,{call,L,F,As}) ->
    %% Extract the operator and all operands.
    {Env1,[X|Xs],S} = gensyms(Env0, L, "Tmp", [F|As]),
    {Env1,{call,L,X,Xs},S};
split(Env0,{op,L,Op,A,B}) ->
    %% Extract both operands.
    {Env1,[X0,X1],S} = gensyms(Env0, L, "Tmp", [A,B]),
    {Env1,{op,L,Op,X0,X1},S};
split(Env0,{op,L,Op,A}) ->
    %% Extract the operand.
    {Env1,[X],S} = gensyms(Env0, L, "Tmp", [A]),
    {Env1,{op,L,Op,X},S};
split(Env0,{cons,L,H,T}) ->
    %% Extract both operands.
    {Env1,[X0,X1],S} = gensyms(Env0, L, "Tmp", [H,T]),
    {Env1,{cons,L,X0,X1},S};
split(Env0,{'tuple',L,Es}) ->
    %% Extract the expressions.
    {Env1,Xs,S} = gensyms(Env0, L, "Tmp", Es),
    {Env1,{'tuple',L,Xs},S};
split(Env0,{'block',L,Es}) ->
    %% Extract the expressions.
    {Env1,Xs,S} = gensyms(Env0, L, "Tmp", Es),
    {Env1,{'block',L,Xs},S};
split(Env0,{'fun',L,{clauses,Cs0}}) ->
    %% Extract all bodies.
    {Env1,Cs,S} = split_clauses(Env0, L, Cs0),
    {Env1,{'fun',L,{clauses,Cs}},S};
split(Env0,{'if',L,Cs0}) ->
    %% Extract all bodies.
    {Env1,Cs,S} = split_clauses(Env0, L, Cs0),
    {Env1,{'if',L,Cs},S};
split(Env0,{match,L,P,E0}) ->
    %% Extract the expression.
    {Env1,[E],S} = gensyms(Env0, L, "Tmp", [E0]),
    {Env1,{match,L,P,E},S};
split(Env0,{'case',L,E0,Cs0}) ->
    %% Extract the expression.
    %% TODO: should this also extract the bodies?
    {Env1,[X],S} = gensyms(Env0, L, "Tmp", [E0]),
    {Env1,{'case',L,X,Cs0},S};
split(Env,E={T,_,_})
  when T == 'var'; T == 'integer'; T == 'float'; T == 'atom';
       T == 'string'; T == 'char' ->
    %% No splitting is possible. Will probably not be needed, but it's
    %% here for completeness.
    {Env,E,dict:new()};
split(Env,E={nil,_}) ->
    {Env,E,dict:new()}.

split_clauses(Env0, Line, Cs0) ->
    Bs0 = [scp_expr:list_to_block(L,B) || {clause,L,_P,_G,B} <- Cs0],
    {Env1,Bs,S} = gensyms(Env0, Line, "Tmp", Bs0),
    Cs = lists:zipwith(fun ({clause,L,P,G,_}, B) ->
                               {clause,L,P,G,[B]}
                       end,
                       Cs0, Bs),
    {Env1,Cs,S}.

%% The most specific generalization (special one-substitution
%% edition). Create a new expression and a substitution. The
%% differences between the expressions are replaced by variables.
%% Applying the substitution to the expression gives you e1 back.
%% Returns the same sort of thing that split/2 returns.
msg(Env, E1, E2) ->
    {Env1,E,S} = msg(Env, scp_expr:free_variables(Env#env.bound, E1), E1, E2),
    io:fwrite("msg ~p~n    ~p =>~n ~p~nS: ~p~n",[E1,E2,E,S]),
    {Env1,E,dict:from_list(S)}.

msg(Env0, _, E={integer,_,I}, {integer,_,I}) ->
    {Env0,E,[]};
msg(Env0, _, E={nil,_}, {nil,_}) ->
    {Env0,E,[]};
msg(Env0, _, E={var,_,N}, {var,_,N}) ->
    {Env0,E,[]};
msg(Env0, Infvs, {cons,L,H1,T1},{cons,_,H2,T2}) ->
    {Env1,H,S1} = msg(Env0, Infvs, H1, H2),
    {Env2,T,S2} = msg(Env1, Infvs, T1, T2),
    {Env2,{cons,L,H,T},S1++S2};
msg(Env0, Infvs, {op,L,Op,A1,B1},{op,_,Op,A2,B2}) ->
    {Env1,A,S1} = msg(Env0, Infvs, A1, A2),
    {Env2,B,S2} = msg(Env1, Infvs, B1, B2),
    {Env2,{op,L,Op,A,B},S1++S2};
msg(Env0, Infvs, {call,L,F={atom,_,N},As1},{call,_,{atom,_,N},As2})
  when length(As1) == length(As2) ->
    {As,{Env3,S}} =
        lists:mapfoldl(fun ({E1,E2},{Env1,S0}) ->
                               {Env2,E,S} = msg(Env1, Infvs, E1, E2),
                               {E,{Env2,S++S0}}
                       end,
                       {Env0,[]},
                       lists:zip(As1, As2)),
    {Env3,{call,L,F,As},S};
%% msg(Env0, Infvs, {'case',L,E1,Cs1},{'case',_,E2,Cs2})
%%   when length(Cs1) == length(Cs2) ->
%%     %% The two cases may be the same, except alpha conversion has
%%     %% removed the exact similarity. Try to make Cs2 use the names
%%     %% from Cs1 first.
%%     ;
%% TODO: more expression types
msg(Env0, Infvs, E1, E2) ->
    msg_default(Env0, Infvs, E1,E2).

msg_default(Env0, Infvs, E1,E2) ->
    %% Just make a variable or a function that wraps all of E1.
    io:fwrite("msg_default~nE1=~p~nE2=~p~n",[E1,E2]),
    {Env1,G} = scp_expr:gensym(Env0, "V"),
    Line = erl_syntax:get_pos(E1),
    case scp_expr:free_variables(Env0#env.bound, E1)--Infvs of
        [] ->
            NewExpr = {var,Line,G},
            Rhs = E1;
        Fvs ->
            NewExpr = {call,Line,G,Fvs},
            Rhs = {'fun',Line,{clauses,
                               {clause,Line,[Fvs],[],[E1]}}}
    end,
    {Env1,NewExpr,[{G,Rhs}]}.

%% EUnit tests

gensyms_test() ->
    Env0 = #env{},
    Es0 = [{atom,1,foo},
           {var,1,"Var"}],
    {_Env1,Names,Subst} = gensyms(Env0, 1, "Tmp", Es0),
    Es1 = [scp_expr:subst(Subst, X) || X <- Names],
    Es0 = Es1.

split_test() ->
    Es = ["foo(1,2,3)",
          "Foo+Bar",
          "-Foo",
          "fun (N) when N<1 -> 0; (N) -> N-1 end",
          "[X|Y] = foo(1,2)",
          "case foo(foo(X)) of [A|B] -> A+B; A -> A end",
          "A = foo(Bar), B = bar(Foo)",
          "[Foo(X)|Bar(Y)]",
          "{Foo(X),Bar(Y)}"],
    lists:foreach(fun (E) ->
                          E0 = scp_expr:read(E),
                          io:fwrite("~nE0: ~p~n", [E0]),
                          {_Env1,E1,S} = split(#env{}, E0),
                          io:fwrite("E1: ~p~n", [E1]),
                          true = E0 =/= E1,
                          E0 = scp_expr:subst(S, E1)
                  end, Es).

whistle_test() ->
    true = whistle(scp_expr:read("B"),
                   scp_expr:read("a(B)")),
    true = whistle(scp_expr:read("c(B)"),
                   scp_expr:read("c(a(B))")),
    true = whistle(scp_expr:read("c(B)"),
                   scp_expr:read("c(a(B))")),
    true = whistle(scp_expr:read("c(B, B)"),
                   scp_expr:read("c(a(B), a(B))")),
    true = whistle(scp_expr:read("a(Xs,[])"),
                   scp_expr:read("a(Xs,[X])")),
    true = whistle(scp_expr:read("a(Y)"),
                   scp_expr:read("a(Y-1)")),
    false = whistle(scp_expr:read("a(c(B))"),
                    scp_expr:read("c(B)")),
    false = whistle(scp_expr:read("a(c(B))"),
                    scp_expr:read("c(a(B))")),
    false = whistle(scp_expr:read("a(c(B))"),
                    scp_expr:read("a(a(a(B)))")),
    true = whistle(scp_expr:read("case a(Xs,[]) of [] -> []; [Y|Ys] -> a(Ys,[X]) end"),
                   scp_expr:read("case a(Xs,[X]) of [] -> []; [Y|Ys] -> a(Ys,[X]) end")),
    true = whistle(scp_expr:read("x:y(x,y)"),
                   scp_expr:read("x:y(y,x)")),
    false = whistle(scp_expr:read("x:y(x,y)"),
                    scp_expr:read("x2:y(y,x)")),
    false = whistle(scp_expr:read("x:y(x,y)"),
                    scp_expr:read("x:y2(y,x)")),
    false = whistle(scp_expr:read("a(A)"),
                    scp_expr:read("b(A)")).
