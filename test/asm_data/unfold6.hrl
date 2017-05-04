-module(unfold6).
-export([a/0, b/0]).

-record(r, {'1', '2', '3', '4', '5'}).

a() ->
    Fs = [fun two/1
         ,fun three/1
         ,fun five/1
         ,fun 'TWO'/1
         ],
    R = lists:foldl(fun (F, R) -> F(R) end, #r{}, Fs),
    deux(R).

deux(#r{'2' = "DEUX"}) -> true;
deux(#r{'2' = Val}) -> Val.

two(R) -> setelement(1+2, R, "deux").
'TWO'(R) -> setelement(1+2, R, "DEUX").
three(R) -> setelement(1+3, R, "trois").
five(R) -> setelement(1+5, R, "cinq").

b() -> true.
