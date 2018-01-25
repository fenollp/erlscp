-module(unfold3).
-export([a/0, b/0]).
-compile({inline, [pipe/2]}).
-compile(inline_list_funcs).
%% -compile(inline).
-compile({inline_size, 100000}).

-record(r, {'1', '2', '3', '4', '5'}).

a() ->
    Fs = [fun two/1
         ,fun three/1
         ,fun five/1
         ,fun 'TWO'/1
         ],
    pipe(#r{}, Fs).

pipe(Acc0, Routines) ->
    lists:foldl(fun (F, R) -> F(R) end, Acc0, Routines).

two(R) -> setelement(1+2, R, "deux").
'TWO'(R) -> setelement(1+2, R, "DEUX").
three(R) -> setelement(1+3, R, "trois").
five(R) -> setelement(1+5, R, "cinq").

b() ->
    #r{'2' = "DEUX"
      ,'3' = "trois"
      ,'5' = "cinq"
      }.
