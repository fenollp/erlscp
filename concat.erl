-module(concat).
-export([a0/0, a1/0, b0/0, b1/0]).

a0() ->
    atom_to_list(tom) ++ "tom".
a1() ->
    lists:concat([tom,"tom"]).

b0() ->
    "tomtom".
b1() ->
    "tomtom".
