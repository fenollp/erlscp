%% -*- coding: utf-8 -*-
-module(erlangs).
-export([a/0,b/0,c/0]).
-compile(inline_list_funcs).

a() -> list_to_tuple(lists:duplicate(3, undefined)).

b() -> {undefined, undefined, undefined}.

c() -> list_to_tuple([1,2,3]).
