-module(bench).
-export([run/1]).

benchmarks() ->
    [{append3,      10000},
     {append3pp,    10000},
     {flip,         30},
     {sumsqs,       100},
     {sumsqs_lc,    100},
     {sumsqtr,      30},
     {to_utf8,      1000},
     {vecdot,       10000},
     {vecdot_int,   10000}].

run(Name) ->
    Times = [run(Module, Iterations) || {Module, Iterations} <- benchmarks()],
    Result = [{N,I,T} || {{N,I},T} <- lists:zip(benchmarks(), Times)],
    io:fwrite("~p~n", [{Name,Result}]).

%% Run the Module benchmark in a loop Iteration times and return
%% statistics.
run(Module, Iterations) ->
    io:fwrite("Benchmarking ~p for ~p iterations~n", [Module, Iterations]),
    Input = Module:input(),
    Run = Module:make_run(Input),
    {Time, Result} = time_it(fun () -> run_loop(Run, Iterations) end),
    case Module:check(Input, Result) of
        true -> true;
        _ -> io:fwrite("~n~nBad test result: ~p returned~n~p~n",[Module, Result])
    end,
    Time.

run_loop(Run, 0) ->
    Run();
run_loop(Run, N) ->
    Run(),
    run_loop(Run, N - 1).

time_it(Fun) ->
    Fun(),
    garbage_collect(),
    {GCs0,Words0,_} = statistics(garbage_collection),
    statistics(exact_reductions),
    Fun(),
    {_, Reductions} = statistics(exact_reductions),
    garbage_collect(),
    {GCs1,Words1,_} = statistics(garbage_collection),
    {Time,V} = minimize_time(Fun),
    %%{Time,V} = timer:tc(Fun),
    {[{wallclock,Time},{reductions,Reductions},{gc,GCs1-GCs0,Words1-Words0}], V}.

%% Minimize wallclock time. This will still not give consistent
%% results across runs, but it will be closer to the truth.
minimize_time(Fun) ->
    minimize_time(Fun, inf, 100).
minimize_time(Fun, MinTime, 0) ->
    {MinTime,Fun()};
minimize_time(Fun, MinTime, N) ->
    case timer:tc(Fun) of
        {T,_} when T < MinTime ->
            %% io:fwrite("faster: ~p < ~p, N=~p~n",[T,MinTime,N]),
            minimize_time(Fun, T, 100);
        _ ->
            minimize_time(Fun, MinTime, N - 1)
    end.
