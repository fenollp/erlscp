-module(erlang_supercompiler).
-export([parse_transform/2]).
-include("scp.hrl").

parse_transform(Forms, Options) ->
    io:fwrite("Before: ~p~n", [Forms]),
    Ret = forms(Forms),
    io:fwrite("After: ~p~n", [Ret]),
    Ret.

forms(Forms) ->
    %% XXX: pass around parts of env
    lists:flatmap(fun (X) -> form(X, Forms) end, Forms).

form({function, Line, Name, Arity, Clauses0}, Forms) ->
    io:fwrite("~n~nLooking at function: ~w~n", [Name]),
    Env0 = #env{forms = Forms},
    Expr0 = {'fun',Line,{clauses,Clauses0}},
    {Env,Expr} = scp_main:drive(Env0, Expr0, []),
    {'fun',_,{clauses,Clauses}} = Expr,
    [{function, Line, Name, Arity, Clauses}];
form(X, _Forms) ->
    [X].
