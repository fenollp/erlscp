-module(map1).
-export([a/0, b/0]).

a() ->
    M = #{a => 1},
    M#{a => 42, b=> 1}.

b() -> #{a => 42, b=> 1}.
