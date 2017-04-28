-module(try0).
-export([a/0, b/0]).

a() ->
    42 = self() ! 42,
    receive
        <<"this">> -> that;
        42 -> length(lists:seq(1, 5))
    after 0 ->
            throw(argh)
    end.

b() ->
    5.
