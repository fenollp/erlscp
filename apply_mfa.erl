-module(apply_mfa).
-export([a/0, b/0]).

a() ->
    (fun blip:blop/1)([]).

b() ->
    blip:blop([]).
