
-module(scp_main).
-export([drive/3]).

-include("scp.hrl").

%% Convert a list of expressions (such as a body) into nested blocks.
list_to_block(Line,[X]) ->
    X;
list_to_block(Line,[X|Xs]) ->
    make_block(Line, X, list_to_block(Line, Xs)).
    %% {'block',Line,[X,list_to_block(Line,Xs)]}.

%% From Oscar Waddell's dissertation. The return expression for whole
%% the block becomes the second expression of the block.
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
		    {'block',L1,{'block',L0,[E1n,E3]},E4};
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
is_simple({nil,_,_}) -> true;
is_simple({'fun',_,_}) -> true;
is_simple(_) -> false.

lookup_function(Env, Name) ->
    false.


%% The driving algorithm. The environment is used to pass information
%% downwards and upwards the stack. R is the current context.

%% Evaluation rules.
%% drive(Env0, {'integer',L0,C}, [Ctxt=#case_ctxt{}|R]) ->  %R1
%%     ;

drive(Env0, E={'var',L0,G}, R) ->		%R3
    case lookup_function(Env0, G) of
	{value,Cs} -> drive_call(Env0, E, Cs, R);
	_ -> build(Env0, E, R)
    end;

drive(Env0, {'fun',Line,{clauses,Cs0}}, R) ->	%R6
    {Env,Cs} = drive_clauses(Env0, Cs0),
    build(Env, {'fun',Line,{clauses,Cs}}, R);

%% drive(Env0, {'block',Lb,[{'match',Lm,P0,E0},Rest0]}, R) ->
%%     ;
drive(Env0, {'block',Line,[A0,B0]}, R) ->
    {Env1, A} = drive(Env0, A0, []),
    {Env, B} = drive(Env1, B0, R),
    {Env, make_block(Line, A, B)};
drive(Env0, {'block',Line,Es}, R) ->
    drive(Env0, list_to_block(Line, Es), R);

%% Focusing rules.
drive(Env0, {'call',L,F,Args}, R) ->		%R12
    drive(Env0, F, [#call_ctxt{line=L, args=Args}|R]);

%% Fallthrough.
drive(Env0, Expr, R) ->				%R14
    io:fwrite("~n%% Fallthrough!~n", []),
    io:fwrite("%% Env: ~p~n%% Expr: ~p~n%% R: ~p~n",
	      [Env0#env{forms=x}, Expr, R]),
    build(Env0, Expr, R).

%% Rebuilding expressions.
build(Env0, Expr, [#call_ctxt{line=Line, args=Args0}|R]) -> %R17
    {Env, Args} = drive_list(Env0, fun drive/3, Args0),
    build(Env, {call,Line,Expr,Args}, R);
build(Env, Expr, []) ->				%R20
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
    Env1 = Env0#env{in_set=Env0#env.in_set ++ Vars},
    {Env,Body} = drive(Env1, list_to_block(L, Body0), []),
    {Env,{clause,L,Head,Guard,[Body]}}.

%% Driving of function calls.
drive_call(Env0, Name, Clauses, R) ->
    {Env0, plug(Name, R)}.

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
