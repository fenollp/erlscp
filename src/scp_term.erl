%% -*- coding: utf-8; mode: erlang -*-
%% @copyright 2012 Göran Weinholt
%% @author Göran Weinholt <goran@weinholt.se>
%% @doc Miscellaneous tools for working with Erlang terms.

-module(scp_term).
-export([list_to_block/2, make_block/3,
	 function_to_fun/1, fun_to_function/3,
	 simplify/1,
	 free_variables/2]).
-include("scp.hrl").

%% Convert a list of expressions (such as in a function body) into
%% nested blocks.
list_to_block(_Line,[X]) ->
    X;
list_to_block(Line,[X|Xs]) ->
    make_block(Line, X, list_to_block(Line, Xs)).

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

%% Conversion between global and local functions.
function_to_fun({function,Line,_Name,_Arity,Clauses}) ->
    {'fun',Line,{clauses,Clauses}}.
fun_to_function({'fun',Line,{clauses,Clauses}},Name,Arity) ->
    {function,Line,Name,Arity,Clauses}.

%% TODO: Simplifies a form which was given to the parser transform.
%% Turns all bodies and blocks into two-armed blocks. XXX: Variables
%% defined by the left arm should be visible in the right arm.
%% Waddell's thing above might need to go?
simplify(Expr) ->
    Expr.

%% Find the free variables of an expression.
%% XXX: is this required to be an ordered set?
free_variables(Expr) ->
    io:fwrite("free_variables(~p)~n", [Expr]),
    {_,Free} = fv([],Expr),
    ordsets:to_list(ordsets:from_list(Free)).
free_variables(InSet, Expr) ->
    [ V || V <- free_variables(Expr), lists:member(V, InSet) ].

%% Bs is a list of bound variables.
fv(Bs,{var,_,V}) ->
    case lists:member(V,Bs) of
	true -> {[],[]};
	false -> {[],[V]}
    end;
fv(_,{integer,_,_}) -> {[],[]};
fv(_,{float,_,_}) -> {[],[]};
fv(_,{atom,_,_}) -> {[],[]};
fv(_,{string,_,_}) -> {[],[]};
fv(_,{char,_,_}) -> {[],[]};
fv(_,{nil,_,_}) -> {[],[]};
fv(Bs,{op,_,_Op,A}) -> fv(Bs, A);
fv(Bs,{op,_,_Op,A,B}) -> fv_list(Bs, [A,B]);
fv(Bs,{call,_,F,As}) ->
    {D0,F0} = fv(Bs, F),
    {D1,F1} = fv_list(Bs, As),
    {D0++D1,F0++F1};
fv(Bs,{cons,_,A,B}) -> fv_list(Bs, [A,B]);
fv(Bs,{tuple,_,Es}) -> fv_list(Bs, Es);
%% fv(Bs,{record,_,_,Is}) -> ;
%% fv(Bs,{bin,_,Fs}) -> ;
%% fv(Bs,{lc,_,E,Qs}) -> ;
%% fv(Bs,{bc,_,E,Qs}) -> ;

%% fv(Bs,{record,_,R,N,Us}) -;
%% fv(Bs,{record_index,_,N,F}) -> ;
%% fv(Bs,{record_field,_,R,N,F}) -> ;
%% fv(Bs,{record_field,_,R,F}) - ;

%% fv(Bs,{'if',_,Cs}) ->
%%     fv_icr_clauses(Bs,Cs,'if');
%% fv(Bs,{'case',_,E,Cs}) ->
%%     {D0,F0} = fv(Bs,E),
%%     {D1,F1} = fv_icr_clauses(Bs,Cs,'case'),
%%     {D0++D1,F0++F1};
%% fv(Bs,{'receive',_,Cs}) ->
%%     fv_icr_clauses(Bs,Cs,'receive');
%% fv(Bs,{'receive',_,Cs,To,ToEs}) ->
%%     {D0,F0} = fv_icr_clauses(Bs,Cs,'receive'),
%%     {D1,F1} = fv_list([Cs|ToEs]),
%%     {D0++D1,F0++F1};
%% fv(Bs,{'try',_,Es,Scs,Ccs,As}) -> ;
%% fv(Bs,{'fun',_,Body}) ->
%%     case Body of
%% 	{clauses,Cs} -> fv_fun_clauses(Cs);
%% 	{function,F,A} -> {[],[]};
%% 	{function,M,F,A} ->
%%     end;
fv(Bs,{'catch',_,E}) -> fv(Bs,E);
fv(Bs,{remote,_,M,F}) -> fv_list(Bs, [M,F]);

fv(Bs,{match,_,P,E}) ->
    %% This defines all pattern variables, except those already bound.
    D = scp_pattern:pattern_variables(P) -- Bs,
    {D0,F0} = fv(Bs, E),
    {D++D0, F0};
fv(Bs,{block,_,[A,B]}) ->
    %% Variables defined in A are not free in B.
    {D0,F0} = fv(Bs, A),
    {D1,F1} = fv(Bs++D0, B),
    {D0++D1,F0++(F1--D0)}.

fv_list(Bs,Es) ->
    {D,F} = lists:unzip(lists:map(fun (X) -> fv(Bs, X) end, Es)),
    {lists:flatten(D),lists:flatten(F)}.

%% if, case, receive: variables defined in all branches are defined
%% outside the expression afterwards. For try expression this is
%% currently not so, but may be in the future. Variables may be
%% defined in either the pattern or the body.
%% fv_icr_clauses(Bs,Cs,Keyword) ->
%%     .


fv0_test() ->
    {_,['Y']} = fv([],{match,1,{var,1,'X'},{var,1,'Y'}}).
fv1_test() ->
    {['X'],[]} = fv(['Y'],{match,1,{var,1,'X'},{var,1,'Y'}}).
fv2_test() ->
    {_,['X']} = fv([],{call,43,
		       {atom,43,foo},
		       [{op,43,'+',{var,43,'X'},{integer,43,1}}]}).
fv3_test() ->
    {['X'],['Y']} = fv([],{block,1,[{match,1,{var,1,'X'},{var,1,'Y'}},
				    {var,1,'X'}]}).
fv4_test() ->
    {['Z'],['Y','X']} = fv([],{block,1,[{match,1,{var,1,'Z'},{var,1,'Y'}},
					{var,1,'X'}]}).
