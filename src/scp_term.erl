%% -*- coding: utf-8; mode: erlang -*-
%% @copyright 2012 Göran Weinholt
%% @author Göran Weinholt <goran@weinholt.se>
%% @doc Miscellaneous tools for working with Erlang terms.

-module(scp_term).
-export([list_to_block/2, make_block/3,
	 function_to_fun/1, fun_to_function/3]).
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

function_to_fun({function,Line,_Name,_Arity,Clauses}) ->
    {'fun',Line,{clauses,Clauses}}.

fun_to_function({'fun',Line,{clauses,Clauses}},Name,Arity) ->
    {function,Line,Name,Arity,Clauses}.
