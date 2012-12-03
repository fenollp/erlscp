-module(erlang_supercompiler).
-export([parse_transform/2]).
-include("scp.hrl").

parse_transform(Forms, Options) ->
    io:fwrite("Before: ~p~n", [Forms]),
    Global = extract_functions(Forms),
    Fnames = lists:map(fun ({Name,_Arity}) -> Name end,
                       dict:fetch_keys(Global)),
    Env0 = #env{%%forms = Forms,
		global = Global,
                seen_vars = sets:from_list(Fnames) },
    Ret = forms(Forms, Env0),
    io:fwrite("After: ~p~n", [Ret]),
    Ret.

forms(Forms0, Env) ->
    {Forms, _Env0} = lists:mapfoldl(fun form/2, Env, Forms0),
    lists:flatten(Forms).

form(F={function,Line,Name,Arity,_Clauses0}, Env0) ->
    %% TODO: what parts of the environment should be reset?
    io:fwrite("~n~nLooking at function: ~w/~w~n", [Name, Arity]),
    Expr0 = scp_expr:function_to_fun(F),
    Seen = sets:union(Env0#env.seen_vars,
                      erl_syntax_lib:variables(Expr0)),
    Env1 = Env0#env{bound = sets:new(),
                    seen_vars = Seen,
                    w=[], ls=[], found=[],
                    name = atom_to_list(Name)},
    {Env2,Expr1} = scp_expr:alpha_convert(Env1, Expr0),
    {Env,Expr2} = scp_main:drive(Env2, Expr1, []),
    {Expr,Letrecs} = scp_expr:extract_letrecs(Expr2),
    Functions = [ scp_expr:fun_to_function(Expr, Name, Arity) ||
                    {Name, Arity, Expr} <- Letrecs ],
    Function = scp_expr:fun_to_function(Expr, Name, Arity),
    {[Function|Functions],Env};
form(X, Env) ->
    {[X],Env}.

%% Go over the forms and extract the top-level functions.
extract_functions(Forms) ->
    extract_functions(Forms, dict:new()).
extract_functions([F={function,Line,Name,Arity,Clauses}|Fs], Global) ->
    Fun = scp_expr:function_to_fun(F),
    extract_functions(Fs, dict:store({Name,Arity}, Fun, Global));
extract_functions([_|Fs], Global) ->
    extract_functions(Fs, Global);
extract_functions([], Global) ->
    Global.
