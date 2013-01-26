-module(vecdot_int).
-export([input/0, make_run/1, check/2]).
-include("bench.hrl").

input() ->
    [[10,22,33,44,0],
     [55,66,77,88,0]].

check(_, N) ->
    trunc(N) == 8415.

?MAKE_RUN(vecdot, Xs, Ys).

%% Another example shown in Jonsson's thesis. This cheats a little bit
%% by having the explicit case on Ys0.
zipwith(Fun, [X|Xs], Ys0) ->
    case Ys0 of
        [] -> Ys0;
        [Y|Ys] ->
            [Fun(X, Y)|zipwith(Fun, Xs,Ys)]
    end;
zipwith(_Fun, _, _) -> [].

sum([]) -> 0;
sum([X|Xs]) -> X + sum(Xs).

vecdot(Xs, Ys) ->
    sum(zipwith(fun (X, Y) -> X * Y end, Xs, Ys)).
