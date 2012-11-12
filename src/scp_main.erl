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


is_const({integer,_,_}) -> true;
is_const({float,_,_}) -> true;
is_const({atom,_,_}) -> true;
is_const({string,_,_}) -> true;
is_const({char,_,_}) -> true;
is_const({nil,_}) -> true;
is_const(_) -> false.

%% The driving algorithm. The environment is used to pass information
%% downwards and upwards the stack. R is the current context.

%% Evaluation rules.
%% drive(Env0, {'integer',L0,C}, [Ctxt=#case_ctxt{}|R]) ->  %R1
%%     ;

drive(Env0, E={'atom',L0,G}, R=[#call_ctxt{args=Args}|_]) -> %R3
    %% This is a function call to a local function or a BIF.
    Arity = length(Args),
    case lookup_function(Env0, {G, Arity}) of
        {ok,Fun} -> drive_call(Env0, E, L0, G, Arity, Fun, R);
        _ -> build(Env0, E, R)
    end;
%% TODO: R3 for 'fun' references in any context

drive(Env0, {'fun',Lf,{clauses,Cs0}}, [#call_ctxt{line=Lc,args=As}|R]) -> %R5
    %% This is how inlining happens. The original rule uses a let, but
    %% the equivalent rule for Erlang must use a case. The fun should
    %% have been alpha converted already, so it doesn't matter that
    %% bindings can escape from the case.
    %%    (fun (X,Y) -> X) (1,2).
    %% => case {1,2} of {X,Y} -> X end.
    %% FIXME: check that the arity matches
    %% XXX: it might be better to treat this as a let, i.e. bite off
    %% one argument at a time, unless there are repeated variables...
    E = {tuple,Lc,As},
    Cs = lists:map(fun ({clause,Line,H0,G0,B0}) ->
                           {clause,Line,[{tuple,Line,H0}],G0,B0}
                   end,
                   Cs0),
    drive(Env0, {'case',Lf,E,Cs}, R);

drive(Env0, {'fun',Line,{clauses,Cs0}}, R) ->   %R6
    {Env,Cs} = drive_clauses(Env0, Cs0),
    build(Env, {'fun',Line,{clauses,Cs}}, R);

%% drive(Env0, {'block',Lb,[{'match',Lm,P0,E0},Rest0]}, R) ->
%%     ;
drive(Env0, {'block',Line,[A0,B0]}, R) ->
    {Env1, A} = drive(Env0, A0, []),
    {Env, B} = drive(Env1, B0, R),
    {Env, scp_expr:make_block(Line, A, B)};
drive(Env0, {'block',Line,Es}, R) ->
    %% XXX: this shouldn't be in the input language anymore
    drive(Env0, scp_expr:list_to_block(Line, Es), R);

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
    {Env,Body} = drive(Env1, scp_expr:list_to_block(L, Body0), []),
    {Env,{clause,L,Head,Guard,[Body]}}.

%% Driving of function calls.
drive_call(Env0, Funterm, Line, Name, Arity, Fun0, R) ->
    %% It is safe to return {Env0,L} if things become difficult.
    io:fwrite("Call: ~p, ~w/~w, R: ~p~n", [Funterm,Name,Arity,R]),
    io:fwrite("Fun: ~p~n", [Fun0]),
    L = plug(Funterm, R),
    FV = scp_expr:free_variables(Env0#env.bound, L),
    %% TODO: first try to find a renaming
    %% TODO: second try to find a homeomorphic embedding

    begin
        %% Neither a renaming nor an embedding.
        {Env1,Fname} = scp_expr:gensym(Env0,"h"),
        {Env2,Fun} = scp_expr:alpha_convert(Env1, Fun0),
        %% Remember that Fname came from the expression L.
        Env3 = Env2#env{ls = [{Fname,L}|Env2#env.ls]},
        io:fwrite("Before: ~p~nAfter: ~p~n", [Fun0,Fun]),
        %% Drive the fun in the original context. If the context is a
        %% call_ctxt then this might do inlining.
        {Env4,E} = drive(Env3, Fun, R),
        io:fwrite("After driving the fun: ~p~n", [E]),
        {Env5,S} = scp_expr:fresh_variables(Env4, dict:new(), FV),
        %% The line numbers are probably going to be a bit wrong.
        case FV of
            [] ->
                %% XXX: test this case
                NewFun0 = E,
                NewTerm = {'fun',Line,{function,{atom,Line,Fname},length(FV)}};
            _ ->
                Head = [scp_expr:subst(S, {var,Line,X}) || X <- FV],
                %% io:fwrite("S: ~p~n", [S]),
                %% io:fwrite("Free variables in ~p: ~w~n", [L,FV]),
                %% io:fwrite("Head: ~p~n",[Head]),
                Guard = [],
                %% io:fwrite("E: ~p~n",[E]),
                Body = scp_expr:subst(S, E),
                NewFun0 = {'fun',Line,
                           {clauses,
                            [{clause,Line,Head,Guard,[Body]}]}},
                NewTerm = {'call',Line,{atom,Line,Fname},
                           [{var,Line,X} || X <- FV]}
        end,
        io:fwrite("NewFun0: ~p~n",[NewFun0]),
        io:fwrite("NewTerm: ~p~n",[NewTerm]),
        {Env6,NewFun} = scp_expr:alpha_convert(Env5, NewFun0),
        io:fwrite("NewFun: ~p~n",[NewFun]),
        %% This letrec will become a top-level function later.
        Letrec = scp_expr:make_letrec(Line,[{Fname,length(FV),NewFun}],[NewTerm]),
        {Env6,Letrec}

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
