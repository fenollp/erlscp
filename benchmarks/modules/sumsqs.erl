-module(sumsqs).
-export([input/0, make_run/1, check/2]).
-include("bench.hrl").

input() ->
    [lists:seq(1, 300)].

check([Xs], S) ->
    N=lists:last(Xs),
    S == ((2*N*N*N)+(3*N*N)+N)/6.

?MAKE_RUN(sumsqs, Xs).

map(_,[]) -> [];
map(Fun,[X|Xs]) -> [Fun(X)|map(Fun,Xs)].

sum([]) -> 0;
sum([X|Xs]) -> X + sum(Xs).

sumsqs(Xs) ->
    sum(map(fun (X) -> X * X end, Xs)).
