-module(deforestation12).
-export([a/0, b/0]).

a() ->
    AsList = maps:to_list(data()),
    NewData = [{K,V} || {K,V} <- AsList, is_integer(V)],
    maps:from_list(NewData).

b() -> #{#{} => 42}.

data() ->
    #{<<"key1">> => "bla"
     ,#{} => 42
     ,'' => <<"Ha!">>
     }.
