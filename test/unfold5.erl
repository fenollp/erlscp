-module(unfold5).
-export([a/0, b/0]).

-record(r, {'1', '2', '3', '4', '5'}).

a() ->
    R0 = #r{},
    R1 = (fun () -> setelement(1+2, R0, "deux") end)(),
    R2 = (fun () -> setelement(1+3, R1, "trois") end)(),
    R3 = (fun () -> setelement(1+5, R2, "cinq") end)(),
    R4 = (fun () -> setelement(1+2, R3, "DEUX") end)(),
    R4.

b() ->
    #r{'2' = "DEUX"
      ,'3' = "trois"
      ,'5' = "cinq"
      }.
