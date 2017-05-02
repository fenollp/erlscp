-module(deforestation10).
-export([a/0, b/0, a/1, b/1]).

a() -> a([blip, blop, 3]).
a(Args) ->
    case not lists:member(length(Args), [1,2]) of
        true -> io:format("usage: ...\n", []);
        false -> do:the_thing(Args)
    end.

b() -> b([bla]).
b([_]) -> io:format("usage: ...\n", []);
b([_,_]) -> io:format("usage: ...\n", []);
b([_|_]=Args) -> do:the_thing(Args).
