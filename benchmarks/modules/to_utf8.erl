-module(to_utf8).
-export([input/0, make_run/1, check/2]).
-include("bench.hrl").

input() ->
    ["Aristoteles Αριστοτέλης Aristotle"].

check(Input, Result) ->
    Expect = binary:bin_to_list(
               unicode:characters_to_binary(Input, unicode, utf8)),
    Result == Expect.

?MAKE_RUN(string_to_utf8, S).

map(_,[]) -> [];
map(Fun,[X|Xs]) -> [Fun(X)|map(Fun,Xs)].

flatten([]) -> [];
flatten([Xs|Xss]) -> Xs ++ flatten(Xss).

to_utf8(Code, Len, I, Set, Mask) when Len >= I ->
    A = if Len == I -> Code; true -> Code bsr (6 * (Len - I)) end,
    B = if Set == 0 -> A; true -> A bor Set end,
    [if Mask == 16#FF -> B; true -> B band Mask end];
to_utf8(_, _, _, _, _) ->
    [].

to_utf8(Code, Len) ->
    LengthCodes = {16#00, 16#00, 16#C0, 16#E0, 16#F0},
    flatten(
      [to_utf8(Code, Len, 1, element(Len + 1, LengthCodes), 16#FF),
       to_utf8(Code, Len, 2, 16#80, 16#BF),
       to_utf8(Code, Len, 3, 16#80, 16#BF),
       to_utf8(Code, Len, 4, 16#80, 16#BF)]).

to_utf8(Code) when Code < 16#80 -> to_utf8(Code, 1);
to_utf8(Code) when Code < 16#800 -> to_utf8(Code, 2);
to_utf8(Code) when Code < 16#10000 -> to_utf8(Code, 3);
to_utf8(Code) -> to_utf8(Code, 4).

string_to_utf8(S) ->
    flatten(map(fun to_utf8/1, S)).
