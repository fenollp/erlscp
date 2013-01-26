-module(append3pp).
-export([input/0, make_run/1, check/2]).
-include("bench.hrl").

input() ->
    append3:input().

check(Result, Input) ->
    append3:check(Result, Input).

?MAKE_RUN(ap, Xs, Ys, Zs).

ap(Xs,Ys,Zs) ->
    (Xs++Ys)++Zs.
