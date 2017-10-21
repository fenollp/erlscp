% -*- coding: utf-8 -*-
-module(inline0).
-export([a/0, b/0]).

a() ->
    {N,_} = a1(0),
    N.

a1(N) -> {N,N}.

b() -> 0.
