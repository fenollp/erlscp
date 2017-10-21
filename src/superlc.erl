%% -*- coding: utf-8; mode: erlang -*-
%% @module Escript entry point.
-module(superlc).

-export([main/1]).

main(Args0) ->
    Args = ["+{parse_transform, erlang_supercompiler}" | Args0],
    erl_compile2:compile_cmdline(Args).
