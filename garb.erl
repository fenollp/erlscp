-module(garb).
-export([a/0, b/0]).

a() ->
    lists:sum([1 || X <- lists:seq(1,5), Y <- lists:seq(2,6), X =:= Y]).

b() -> 4.
