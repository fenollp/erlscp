-module(testcases).
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

%% bar_test() ->
%%     1,
%%     fun (X) ->
%% 	    begin X + 1, X + 3 end,
%% 	    X
%%     end.

%%foo(0) -> 0;
foo(X) ->
    foo(X+1).
