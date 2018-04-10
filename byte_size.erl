-module(byte_size).
-export([a/0, b/0]).

a() ->
    byte_size(<<"Hello World\n">>).

b() ->
    12.
