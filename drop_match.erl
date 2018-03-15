-module(drop_match).
-export([a/0,b/0]).
-export([aa/0,bb/0]).

a() ->
    _ = {erlang:erase(a), erlang:erase(b)},
    ok.

b() ->
    _ = erlang:erase(a),
    _ = erlang:erase(b),
    ok.

aa() ->
    {1,2} = {erlang:get(a), erlang:get(b)},
    ok.

bb() ->
    1 = erlang:get(a),
    2 = erlang:get(b),
    ok.
