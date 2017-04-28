-module(map4).
-export([a/0, b/0]).

a() ->
    #{key := Y} = #{key => b},
    M = (fun (X) -> #{a => X} end)(Y),
    M#{a => 42, Y => 1}.

b() -> #{a => 42, b => 1}.
