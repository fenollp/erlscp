-module(unfold4).
-export([a/0, b/0]).

-record(r, {'1', '2', '3', '4', '5'}).

a() ->
    S = {some, "state"},
    Fs = [fun two/2
         ,fun three/2
         ,fun five/2
         ,fun 'TWO'/2
         ],
    lists:foldl(fun (F, R) -> F(R, S) end, #r{}, Fs).

two(R, _) -> setelement(1+2, R, "deux").
'TWO'(R, _) -> setelement(1+2, R, "DEUX").
three(R, _) -> setelement(1+3, R, "trois").
five(R, _) -> setelement(1+5, R, "cinq").

b() ->
    #r{'2' = "DEUX"
      ,'3' = "trois"
      ,'5' = "cinq"
      }.
