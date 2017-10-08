-module(unfold6).
-export([a/0, b/0]).
-compile({parse_transform, fancyflow_trans}).

-record(r, {'1', '2', '3', '4', '5'}).

a() ->
    [pipe](#r{}
          ,setelement(1+2, _, "deux")
          ,setelement(1+3, _, "trois")
          ,setelement(1+5, _, "cinq")
          ,setelement(1+2, _, "DEUX")
          ).

b() ->
    #r{'2' = "DEUX"
      ,'3' = "trois"
      ,'5' = "cinq"
      }.
