-module(testcases).
-export([to_utf8/1,
         %%string_to_utf8/1,
         ap/2, ap/3, sumsqs/1,
         rev/2, double/1,
         map/2, flatten/1,
         sum/1
        ]).
-include("scp.hrl").
-compile({parse_transform, erlang_supercompiler}).

%% int_test() ->
%%     1234.

%% lc_test() ->
%%     [X || X <- [1,2,a,3,4,b,5,6], integer(X), X > 3].

%% fun_test() ->
%%     Y = fun (X) -> X + 1 end,
%%     Y.

%% yo(Y=H=5) ->
%%     5.

%% tuple({1,X}) -> 5;
%% tuple(_) -> 1.

%% build(Env, Expr, [#call_ctxt{line=Line, args=Args}|R]) ->
%%     error({todo}).

%% foo(Y, X=#call_ctxt.line) ->
%%     ok.

%% foobar(<<X,4:4,Y:4/little-signed-integer-unit:8,Rest/binary>>) ->
%%     ok.

-ifndef(LET).
-define(LET(L,R,B), ((fun(L) -> (B) end) (R))).
-endif.


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
            Y -> 0
        end.

unbound_test() ->
    X = 1,
    1 = case 1 of
            Y -> 1;
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
            {X} when X == 1 ->
                X;
            _ ->
                0
        end.

guard_2_variable_test() ->
    1 = case {3,2} of
            {X,Y} when X > Y ->
                X-Y;
            _ ->
                0
        end.

if_test() ->
    1 = ?LET(X, 42,
             if X == 42 ->
                     1;
                true ->
                     2
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

%% bar_test() ->
%%     1,
%%     fun (X) ->
%% 	    begin X + 1, X + 3 end,
%% 	    X
%%     end.

%% apt({Xs,Ys}) ->
%%     case {Xs,Ys} of
%%         {[]} -> Ys;
%%         {[X|Xs]} -> [X|apt({Xs,Ys})]
%%     end.

%% ap(Xs,Ys) ->
%%     case Xs of
%%         [] -> Ys;
%%         [X|Xs] -> [X|ap(Xs,Ys)]
%%     end.


%% foo2(X,X)->X.
%% foo2() ->
%%     (X=1)+(X=1).

%% cases(X) ->
%%     case X of
%%         [A|B] -> ok;
%%         _ -> B = X
%%     end,
%%     B.


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


%% lists:append(X=[1,2],X=[3,4]),


ap([],Ys) -> Ys;
ap([X|Xs],Ys) -> [X|ap(Xs,Ys)].

ap(Xs,Ys,Zs) ->
    ap(ap(Xs,Ys),Zs).

%% Tests like these should be made with quickcheck and should be in a
%% different module so that they are not supercompiled.
%% ap3_test() ->
%%     X = [1,2,3],
%%     Y = [a,b,c],
%%     Z = [9,8,7],
%%     Ap3 = ap(X,Y,Z),
%%     Ap3 = ap(ap(X,Y),Z),
%%     Ap3 = ap(X,ap(Y,Z)),
%%     Ap3 = X++ap(Y,Z),
%%     Ap3 = X++Y++Z.

sum([]) -> 0;
sum([X|Xs]) -> X + sum(Xs).

square(X) -> X * X.

map(_,[]) -> [];
map(Fun,[X|Xs]) -> [Fun(X)|map(Fun,Xs)].

sumsqs(Xs) ->
    sum(map(fun square/1, Xs)).

flatten([]) ->
    [];
flatten([Xs|Xss]) ->
    ap(Xs,flatten(Xss)).

%% string_to_utf8(S) ->
%%     flatten(map(fun to_utf8/1, S)).

%% broken(Code) ->
%%     map(fun (X) ->
%%                 X * 100
%%         end,
%%         to_utf8(Code)).

%% Requires the whistle.
rev([],Ys) ->
    Ys;
rev([X|Xs],Ys) ->
    rev(Xs, [X|Ys]).

%% Tests upwards generalization.
double(Xs) ->
    ap(Xs, Xs).

%% TODO: there is no improvement here, but scp_tidy should make sure
%% that the residual program doesn't have case {Xs,Ys} of ...
%% same_length([], []) -> true;
%% same_length([X|Xs],[Y|Ys]) -> same_length(Xs,Ys);
%% same_length(_,_) -> false.
