-module(match_and_bind0).
-export([a/0, b/0]).

a () ->
    {1, "b", F=c} = c(),
    F.

b() -> c.

c() ->
    case rand:uniform() of
        F when F < 1.0 ->
            {1, "b", c};
        _ ->
            {2, "c", d}
    end.
