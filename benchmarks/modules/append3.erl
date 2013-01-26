-module(append3).
-export([input/0, make_run/1, check/2]).
-include("bench.hrl").

input() ->
    [[1,2,3,4],[5,6,7,8],[9,10,11,12]].

check(_, [1,2,3,4,5,6,7,8,9,10,11,12]) ->
    true;
check(_, _) ->
    false.

?MAKE_RUN(ap, Xs, Ys, Zs).

ap([],Ys) -> Ys;
ap([X|Xs],Ys) -> [X|ap(Xs,Ys)].

ap(Xs,Ys,Zs) ->
    ap(ap(Xs,Ys),Zs).
