%% -*- coding: utf-8; mode: erlang -*-

%% Copyright (C) 2012-2013 Göran Weinholt <goran@weinholt.se>

%% Permission is hereby granted, free of charge, to any person obtaining a
%% copy of this software and associated documentation files (the "Software"),
%% to deal in the Software without restriction, including without limitation
%% the rights to use, copy, modify, merge, publish, distribute, sublicense,
%% and/or sell copies of the Software, and to permit persons to whom the
%% Software is furnished to do so, subject to the following conditions:

%% The above copyright notice and this permission notice shall be included in
%% all copies or substantial portions of the Software.

%% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
%% IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
%% FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
%% THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
%% LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
%% FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
%% DEALINGS IN THE SOFTWARE.

%% Various test cases for the supercompiler.

-module(testcases).
-export([ap/2, ap/3,
         rev/2, map/2, zip/2, flatten/1,
         double/1,
         sum/1, square/1, sumsqs/1, seq/2, sumsq/1,
         zipmap/4, mapsq/1, f/1, g/1, mapsq2/1, sumf/1,
         zipwith/3, vecdot/2,
         ap_opl/3, ap_opr/3,
         sort/1,
         %%to_utf8/1, string_to_utf8/1,
         same_length/2
        ]).
-include("scp.hrl").                            %merely enables EUnit
-compile({parse_transform, erlang_supercompiler}).

ap([],Ys) -> Ys;
ap([X|Xs],Ys) -> [X|ap(Xs,Ys)].

ap(Xs,Ys,Zs) ->
    ap(ap(Xs,Ys),Zs).

map(_,[]) -> [];
map(Fun,[X|Xs]) -> [Fun(X)|map(Fun,Xs)].

%% zip([],_) -> [];
%% zip([X|Xs],[Y|Ys]) -> [{X,Y}|zip(Xs,Ys)].

zip([],_) -> [];
zip([X|Xs],Ys0) ->
    case Ys0 of
        [] -> Ys0;
        [Y|Ys] ->
            [{X,Y}|zip(Xs,Ys)]
    end.

flatten([]) ->
    [];
flatten([Xs|Xss]) ->
    Xs ++ flatten(Xss).
%%    ap(Xs,flatten(Xss)).

square(X) -> X * X.
sum([]) -> 0;
sum([X|Xs]) -> X + sum(Xs).
sumsqs(Xs) ->
    sum(map(fun square/1, Xs)).

seq(I, N) when I > N ->
    [];
seq(I, N) ->
    [I|seq(I+1, N)].

sumsq(N) ->
    sumsqs(seq(1, N)).

%% Requires the whistle.
rev([],Ys) -> Ys;
rev([X|Xs],Ys) -> rev(Xs, [X|Ys]).

%% Tests upwards generalization.
double(Xs) -> ap(Xs, Xs).

%% Not improved.
zipmap(F, G, Xs, Ys) ->
    zip(map(F,Xs), map(G, Ys)).

%% Fusing two successive applications.
mapsq(Xs) -> map(fun square/1, Xs).
f([]) -> [];
f([X|Xs]) -> [2*X|g(Xs)].
g([]) -> [];
g([X|Xs]) -> [3*X|f(Xs)].
mapsq2(Xs) -> mapsq(mapsq(Xs)).
sumf(Xs) -> sum(f(Xs)).

%% Another example shown in Jonsson's thesis.
zipwith(Fun, [X|Xs], Ys0) ->
    case Ys0 of
        [] -> Ys0;
        [Y|Ys] ->
            [Fun(X, Y)|zipwith(Fun, Xs,Ys)]
    end;
zipwith(_Fun, _, _) -> [].
vecdot(Xs, Ys) ->
    sum(zipwith(fun (X, Y) -> X * Y end, Xs, Ys)).

%% The ++ operator.
ap_opl(Xs, Ys, Zs) -> Xs ++ (Ys ++ Zs).
ap_opr(Xs, Ys, Zs) -> (Xs ++ Ys) ++ Zs.

%% Examples from the Erlang Programming Examples User's Guide.
sort([Pivot|T]) ->
    sort([ X || X <- T, X < Pivot]) ++
        [Pivot] ++
        sort([ X || X <- T, X >= Pivot]);
sort([]) -> [].

%%-compile({no_whistle,[xappend/1, xmap/2, xfilter/2]}).
xappend(L) ->  [X || L1 <- L, X <- L1].
xmap(Fun, L) -> [Fun(X) || X <- L].
xfilter(Pred, L) -> [X || X <- L, Pred(X)].

select(X, L) ->  [Y || {X1, Y} <- L, X == X1].

%% The residual program shouldn't rebuild the list.
append_lc(Xs, Ys) ->
    [X+1 || X <- Xs, is_integer(X)] ++ Ys.

-ifndef(LET).
-define(LET(L,R,B), ((fun(L) -> (B) end) (R))).
-endif.


-define(FOOBAR,1).

-ifdef(FOOBAR).
%% byte_bsr(A,0) -> A;
%% byte_bsr(A,B) -> A bsr B.
%% byte_bor(A,0) -> A;
%% byte_bor(A,B) -> A bor B.
%% byte_band(A,16#FF) -> A;
%% byte_band(A,B) -> A band B.
%% to_utf8(Code, Len, I, Set, Mask) when Len >= I ->
%%     [byte_band(byte_bor(byte_bsr(Code, (6 * (Len - I))),
%%                         Set),
%%                Mask)];

to_utf8(Code, Len, I, Set, Mask) when Len >= I ->
    A = if Len == I -> Code; true -> Code bsr (6 * (Len - I)) end,
    B = if Set == 0 -> A; true -> A bor Set end,
    [if Mask == 16#FF -> B; true -> B band Mask end];
    %% A = case Len of I -> Code; _ -> Code bsr (6 * (Len - I)) end,
    %% B = case Set of 0 -> A; _ -> A bor Set end,
    %% [case Mask of 16#FF -> B; _ -> B band Mask end];
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

atom_test() ->
    1 = case false of
            true -> 0;
            false -> 1
        end.

tuple_case_test() ->
    1 = case {} of
            {X} -> 0;
            {} -> 1
        end.

integer_test() ->
    1 = case 5 of
            4 -> 0;
            5 -> 1
        end.

string_test() ->
    1 = case "foo" of
            "bar" -> 0;
            "foo" -> 1
        end.

char_test() ->
    1 = case $B of
            $A -> 0;
            $B -> 1;
            $C -> 2
        end.

guard_test() ->
    Xyzzy = 1,
    1 = case foo of
            bar -> 0;
            foo when Xyzzy == 1 -> 1
        end.

simplify_test() ->
    1 = case {foo} of
            foo -> wrong;
            {bar} -> 0;
            {foo} -> 1
        end.

bound_test() ->
    X = 1,
    1 = case 1 of
            X -> 1;
            _Y -> 0
        end.

unbound_test() ->
    X = 1,
    1 = case 1 of
            _Y -> 1;
            X -> 0;
            _ -> vat
        end.

trival_cons_test() ->
    1 = case [1] of
        [1] -> 1;
        [2] -> 0
    end.

match_test() ->
    X = 1,
    X = case hd([foo]) of
            foo -> 1;
            bar -> 0
        end.

infix_op_test() ->
    1 = 2+2-3*1.

prefix_op_test() ->
    1 = -(2+2-5).

div_test() ->
    1 = trunc(1/case hd([foo]) of
                    foo -> 1;
                    bar -> 0
                end).

tuple_test() ->
    1=element(1,{tuple_case_test(),1+1,1+1+1}).

guard_variable_test() ->
    1 = case {1} of
            {X} when X == 1 -> X;
            _ -> 0
        end.

guard_2_variable_test() ->
    1 = case {3,2} of
            {X,Y} when X > Y -> X-Y;
            _ -> 0
        end.

guard_2c_variable_test() ->
    1 = case [3|2] of
            [X|Y] when X > Y -> X-Y;
            _ -> 0
        end.

if_test() ->
    1 = ?LET(X, 42,
             if X == 42 -> 1;
                true -> 2
             end).

guard_simplify_test() ->
    1 = case {{1}} of
            {X} when element(1, X) == 1 ->
                element(1, X)
        end.

guard_2_simplify_test() ->
    1 = case {{1},length([1,2,3])} of
            {X,_} when element(1, X) == 1 ->
                element(1, X)
        end.

r18_test() ->
    X = 1,
    case X of
        [] -> [x|X];
        1 -> X+1-X;
        Y -> X =:= Y
    end.

r18_underscore_test() ->
    X = 1,
    case X of
        [] -> [x|X];
        _ -> X
    end.

let_test() ->
    ?LET(X, fun (Y) -> Y end(1),
         {X,X}).

foo(Ps,Xs,Ys,Zs) ->
    case {Ys,Xs} of
        {0,B} -> B;
        {A,0} -> A
    end.

%% There is no improvement here, but scp_tidy should make sure
%% that the residual program doesn't have case {Xs,Ys} of ...
same_length([], []) -> true;
same_length([_|Xs],[_|Ys]) -> same_length(Xs,Ys);
same_length(_,_) -> false.

%% apt({Xs,Ys}) ->
%%     case {Xs,Ys} of
%%         {[]} -> Ys;
%%         {[X|Xs]} -> [X|apt({Xs,Ys})]
%%     end.

-endif.

%% foo(Xs) ->
%%     case ap([a],Xs) of
%%         [A|B] ->
%%             A
%%     end.

%% foo(Xs) ->
%%     case ap([],Xs) of
%%         [A|B] ->
%%             A
%%     end.

%% foo() ->
%%     1 = case [1|2] of
%%             [] -> 2;
%%             [A|B] -> A
%%         end.


%% -compile({no_whistle,[foo/1]}).

foo(Xs) ->
    flatten(map(fun bar/1, Xs)).

bar(X) ->
    [X+1].
