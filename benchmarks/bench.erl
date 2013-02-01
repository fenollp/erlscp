-module(bench).
-export([run/1, summary/1]).

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
    io:fwrite("~p.~n", [{Name,Result}]).

%% Run the Module benchmark in a loop Iteration times and return
%% statistics.
run(Module, Iterations) ->
    io:fwrite("%% Benchmarking ~w for ~w iterations~n", [Module, Iterations]),
    Input = Module:input(),
    Run = Module:make_run(Input),
    {Time, Result} = time_it(fun () -> run_loop(Run, Iterations) end),
    case Module:check(Input, Result) of
        true -> true;
        _ -> io:fwrite("~n~n%% Bad test result: ~w returned~n~w~n",[Module, Result])
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
    {[{wallclock,Time},
      {reductions,Reductions},
      {gc,GCs1-GCs0,Words1-Words0}], V}.

%% Minimize wallclock time. This will still not give consistent
%% results across runs, but it will be closer to the truth.
minimize_time(Fun) ->
    minimize_time(Fun, inf, 100).
minimize_time(Fun, MinTime, 0) ->
    {MinTime,Fun()};
minimize_time(Fun, MinTime, N) ->
    case timer:tc(Fun) of
        {T,_} when T < MinTime ->
            %% io:fwrite("%% faster: ~p < ~p, N=~p~n",[T,MinTime,N]),
            minimize_time(Fun, T, 100);
        _ ->
            minimize_time(Fun, MinTime, N - 1)
    end.

%% Load benchmarking outputs and print summaries.
summary(Filename) ->
    case file:consult(Filename) of
        {ok, Terms} ->
            {_,Noscp} = lists:keyfind(noscp, 1, Terms),
            {_,Scp} = lists:keyfind(scp, 1, Terms),
            {_,HiPE_noscp} = lists:keyfind(hipe_noscp, 1, Terms),
            {_,HiPE_scp} = lists:keyfind(hipe_scp, 1, Terms),
            io:fwrite("\\emph{Benchmark} & \\emph{Bytecode VM} & \\emph{Native code} \\\\~n"),
            compare_wallclock(benchmarks(), Noscp, Scp, HiPE_noscp, HiPE_scp),
            io:fwrite("~n\\emph{Benchmark} & \\emph{Reduction} \\\\~n",[]),
            compare(lists:zip(Noscp, Scp), gc)
    end.

compare(Data, What) ->
    [compare1(Datum, What) || Datum <- Data].
compare1({{Module,I,OriginalData},{Module,I,ImprovedData}}, What=gc) ->
    {_,_,Original} = lists:keyfind(What, 1, OriginalData),
    {_,_,Improved} = lists:keyfind(What, 1, ImprovedData),
    io:fwrite("~s & $~.2f$ \\\\~n",[escape(Module),1.0-(Improved/Original)]).

compare_wallclock([], [], [], [], []) ->
    ok;
compare_wallclock([{Module,Iterations}|Bs],
                  [{Module,Iterations,N}|Ns],
                  [{Module,Iterations,S}|Ss],
                  [{Module,Iterations,HN}|HNs],
                  [{Module,Iterations,HS}|HSs]) ->
    [NW,SW,HNW,HSW] = [element(2,lists:keyfind(wallclock,1,X)) || X <- [N,S,HN,HS]],
    io:fwrite("~s & $~.2f$ & $~.2f$ \\\\ ~n",[escape(Module),NW/SW,HNW/HSW]),
    compare_wallclock(Bs, Ns, Ss, HNs, HSs).

escape(X) when is_atom(X) ->
    escape(atom_to_list(X));
escape([]) ->
    [];
escape([$_|Cs]) ->
    [$\\,$_|escape(Cs)];
escape([C|Cs]) ->
    [C|escape(Cs)].

