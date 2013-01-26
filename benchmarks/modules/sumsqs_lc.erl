-module(sumsqs_lc).
-export([input/0, make_run/1, check/2]).
-include("bench.hrl").


input() -> sumsqs:input().
check(Input, Result) -> sumsqs:check(Input, Result).
%% -compile({no_whistle,[make_run/1]}).
?MAKE_RUN(sumsqs, Xs).

sum([]) -> 0;
sum([X|Xs]) -> X + sum(Xs).

sumsqs(Xs) ->
    sum([ X * X || X <- Xs ]).
