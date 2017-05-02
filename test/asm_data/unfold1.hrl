-module(unfold1).
-export([a/0, b/0]).

-record(r, {'1', '2', '3', '4', '5'}).

a() ->
    R0 = #r{},
    R1 = setelement(1+2, R0, "deux"),
    R2 = setelement(1+3, R1, "trois"),
    R3 = setelement(1+5, R2, "cinq"),
    R4 = setelement(1+2, R3, "DEUX"),
    R4.

b() ->
    #r{'2' = "DEUX"
      ,'3' = "trois"
      ,'5' = "cinq"
      }.
