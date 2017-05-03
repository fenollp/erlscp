-module(try3).
-export([a/0, b/0]).

a() ->
    catch get().

b() ->
    get().
