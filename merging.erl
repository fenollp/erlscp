-module(merging).
-export([a/0,aa/1]).

a() ->
    maps:merge(#{}, #{a => 1}).

aa(L) ->
    maps:merge(#{a => 1}, #{a => L}).
