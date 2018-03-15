-module(drop_match).
-export([a/0,b/0]).

a() ->
    _ = {erlang:erase(a), erlang:erase(b)},
    ok.

b() ->
    _ = erlang:erase(a),
    _ = erlang:erase(b),
    ok.
