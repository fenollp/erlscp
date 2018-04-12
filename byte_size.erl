-module(byte_size).
-export([a/0, b/0]).
-define(M, "Hello World\n").

a() ->
    S = <<?M>>,
    byte_size(S) + length(".!.").

b() ->
    15.
