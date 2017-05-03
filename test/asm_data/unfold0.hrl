-module(unfold0).
-export([a/0, b/0]).

-record(r, {'1', '2', '3', '4', '5'}).

a() ->
    Fs = [fun (R) -> setelement(1+2, R, "deux") end
         ,fun (R) -> setelement(#r.'3', R, "trois") end
         ,fun (R) -> setelement(1+5, R, "cinq") end
         ,fun (R) -> setelement(1+2, R, "DEUX") end
         ],
    lists:foldl(fun (F, R) -> F(R) end, #r{}, Fs).

b() ->
    #r{'2' = "DEUX"
      ,'3' = "trois"
      ,'5' = "cinq"
      }.
