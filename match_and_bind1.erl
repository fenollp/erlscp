-module(match_and_bind1).
-export([a/0, b/0]).

a () ->
    {1, "b", F=io} = c(),
    F:module_info().

b() -> io:module_info().

c() ->
    case rand:uniform() of
        F when F < 1.0 ->
            {1, "b", io};
        _ ->
            {2, "c", d}
    end.
