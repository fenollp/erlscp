-module(flip).
-export([input/0, make_run/1, check/2]).
-include("bench.hrl").

%% Generate a tree of depth N. All the leafs will be at the bottom.
gentree(I,N) when I > N ->
    {leaf,N};
gentree(I,N) ->
    {branch,gentree(I+1,N),gentree(I+1,N)}.

depth({leaf,_}) ->
    0;
depth({branch,L,R}) ->
    1 + max(depth(L),depth(R)).

input() ->
    [gentree(1,12)].

check([Tree], S) ->
    N = depth(Tree),
    S == N * math:pow(2, N).

?MAKE_RUN(flipsum, X).

%% Example used in Jonsson's dissertation, from Wadler.
sumtr({leaf,X}) ->
    X;
sumtr({branch,L,R}) ->
    sumtr(L) + sumtr(R).

flip({leaf,X}) ->
    {leaf,X};
flip({branch,L,R}) ->
    {branch,flip(R),flip(L)}.

flipsum(X) ->
    sumtr(flip(flip((X)))).
