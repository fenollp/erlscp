-module(try2).
-export([a/0, b/0]).

a() ->
    try get() of
        <<"abc">> -> <<"def">>;
        <<"π"/utf8>>=_Pi -> 3.14e0;
        [_|_]=PD -> PD
    catch
        _:_ -> impossible
    end.

b() ->
    get().
