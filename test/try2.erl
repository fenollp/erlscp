-module(try2).
-export([a/0, b/0]).

a() ->
    try get() of
        <<"abc">> -> <<"def">>;
        <<"π"/utf8>>=_Pi -> 3.14e0;
        PD when is_list(PD) -> PD
    catch
        _:_ -> impossible
    end.

b() ->
    get().
