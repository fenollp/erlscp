-module(try1).
-export([a/0, b/0]).

a() ->
    try get() of
        [_|_]=PD -> PD;
        [] -> []
    catch
        _:_ -> impossible
    end.

b() ->
    get().
