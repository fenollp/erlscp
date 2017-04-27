-module(map2).
-export([a/0, b/0]).

a() ->
    M = (fun () -> #{a => 1} end)(),
    M#{a => 42, b=> 1}.

b() -> #{a => 42, b=> 1}.
