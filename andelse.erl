-module(andelse).
-export([a/0, b/0]).

a() ->
    false
        orelse ( true
                 andalso node()
               ).

b() -> node().
