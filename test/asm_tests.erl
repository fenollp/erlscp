%% Copyright © 2017 Pierre Fenoll ‹pierrefenoll@gmail.com›
%% See LICENSE for licensing information.
%% -*- coding: utf-8 -*-

%% @module Testing assembly generation.
-module(asm_tests).

-include_lib("eunit/include/eunit.hrl").

%% API tests.

deforestation0_test_() -> asm(deforestation0).

map4_test_() -> asm(map4).

%% Internals

asm(Mod) ->
    {setup
    ,fun () -> {ok,_} = file:copy(hrl(Mod), erl(Mod)), ok end
    ,fun (_) ->
             Erl = iolist_to_binary(erl(Mod)),
             ok = file:delete(Erl),
             ok = file:delete(binary:replace(Erl, <<".erl">>, <<".beam">>)),
             ok = file:delete(binary:replace(Erl, <<".erl">>, <<".P">>)),
             ok = file:delete(binary:replace(Erl, <<".erl">>, <<".E">>)),
             ok = file:delete(binary:replace(Erl, <<".erl">>, <<".S">>))
     end
    ,fun (_) ->
             {_,_} = write_both('P', Mod),
             {_,_} = write_both('E', Mod),
             {ERLC, SUPERC} = write_both('S', Mod),
             [compare_execution(fun purge_erlc_load/1, Mod)
             ,?_assertEqual(read(src('S', Mod)), ERLC)
             ,compare_execution(fun purge_superc_load/1, Mod)
             ,?_assertEqual(read(dst('S', Mod)), SUPERC)
             ]
     end
    }.

hrl(Mod) -> filename:join(["test", "asm_data", atom_to_list(Mod)++".hrl"]).
erl(Mod) -> filename:join(["test", "asm_data", atom_to_list(Mod)++".erl"]).

src(X, Mod) -> filename:join(["test", "asm_data", "src", atom_to_list(Mod)++"."++atom_to_list(X)]).
dst(X, Mod) -> filename:join(["test", "asm_data", "dst", atom_to_list(Mod)++"."++atom_to_list(X)]).

write_both(Option, Mod) ->
    ERLC   = erlc(Mod, [Option]),
    SUPERC = erlc(Mod, [Option|superc_options()]),
    write(src(Option, Mod), ERLC),
    write(dst(Option, Mod), SUPERC),
    {ERLC, SUPERC}.

write(Path, Data) ->
    ok = file:write_file(Path, Data).

read(S) ->
    {ok, Bin} = file:read_file(S),
    Bin.

compare_execution(ERLC, Mod) ->
    ok = ERLC(Mod),
    ?_assertEqual(Mod:b(), Mod:a()).

purge_erlc_load(Mod) ->
    purge_compile_load(Mod, erlc_options()).
purge_superc_load(Mod) ->
    purge_compile_load(Mod, erlc_options()++superc_options()).
purge_compile_load(Mod, Options) ->
    _ = code:purge(Mod),
    _ = code:delete(Mod),
    Erl = erl(Mod),
    Ebin = filename:dirname(Erl),
    {ok, Mod} = compile:file(Erl, [{outdir, Ebin}
                                   |Options
                                  ]),
    true = code:add_patha(Ebin),
    {module, Mod} = code:load_file(Mod),
    ok.

erlc(Mod, MoreOptions) ->
    Erl = erl(Mod),
    Ebin = filename:dirname(Erl),
    Options = MoreOptions ++ [{outdir,Ebin}, binary | erlc_options()],
    {ok, _, S} = compile:file(Erl, Options),
    iolist_to_binary(io_lib:format("~p\n", [S])).

superc_options() ->
    [AppEbin] = [Dir || Dir <- code:get_path(), lists:suffix("/erlscp/ebin", Dir)],
    [{parse_transform, erlang_supercompiler}
    ,{i, AppEbin}
    ].

erlc_options() ->
    [verbose
    ,report_errors
    ,report_warnings
    ].

%% End of Module.
