-module(erlang_supercompiler).
-export([parse_transform/2]).
-include("scp.hrl").

parse_transform(Forms, Options) ->
    io:fwrite("Before: ~p~n", [Forms]),
    Global = extract_functions(Forms),
    Env0 = #env{forms = Forms,
		global = Global},
    Ret = forms(Forms, Env0),
    io:fwrite("After: ~p~n", [Ret]),
    Ret.

forms(Forms, Env) ->
    %% TODO: pass around parts of env
    lists:flatmap(fun (X) -> form(X, Env) end,
		  Forms).

form(F={function,Line,Name,Arity,_Clauses0}, Env0) ->
    io:fwrite("~n~nLooking at function: ~w~n", [Name]),
    Expr0 = scp_term:simplify(scp_term:function_to_fun(F)),
    {Env,Expr} = scp_main:drive(Env0, Expr0, []),
    [scp_term:fun_to_function(Expr, Name, Arity)];
form(X, _Env) ->
    [X].

%% Go over the forms and extract the top-level functions.
extract_functions(Forms) ->
    extract_functions(Forms, dict:new()).
extract_functions([F={function,Line,Name,Arity,Clauses}|Fs], Global) ->
    Fun = scp_term:function_to_fun(F),
    extract_functions(Fs, dict:store({Name,Arity}, Fun, Global));
extract_functions([_|Fs], Global) ->
    extract_functions(Fs, Global);
extract_functions([], Global) ->
    Global.
