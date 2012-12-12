%% -*- coding: utf-8; mode: erlang -*-
%% @copyright 2012 Göran Weinholt
%% @author Göran Weinholt <goran@weinholt.se>
%% @doc Translates list comprehensions etc into simpler code.

-module(scp_desugar).
-export([forms/2]).
-include("scp.hrl").

%% Libnames is a dict containing the names for some standard functions.
forms([F={function,_,Name,Arity,_}|Fs], Libnames) ->
    Expr0 = scp_expr:function_to_fun(F),
    Expr = desugar(Expr0, Libnames),
    Function = scp_expr:fun_to_function(erl_syntax:revert(Expr), Name, Arity),
    [Function|forms(Fs, Libnames)];
forms([X|Xs], Libnames) ->
    [X|forms(Xs, Libnames)];
forms([], _) ->
    [].

desugar(E0, Libnames) ->
    erl_syntax_lib:map(
      fun (Node) ->
              case erl_syntax:type(Node) of
                  list_comp ->
                      X = lc_translate(erl_syntax:list_comp_template(Node),
                                       erl_syntax:list_comp_body(Node),
                                       Libnames),
                      ?DEBUG("desugared:~n~p~n", [erl_syntax:revert(X)]),
                      X;
                  infix_expr ->
                      Op = erl_syntax:infix_expr_operator(Node),
                      case erl_syntax:type(Op) of
                          operator ->
                              case erl_syntax:operator_name(Op) of
                                  '++' ->
                                      infix_translate(Node, Libnames, append);
                                  _ ->
                                      Node
                              end;
                          _ ->
                              Node
                      end;
                  _ ->
                      Node
              end
      end, E0).

%% Translate list comprehensions using a simple approach from Simon
%% PJ's _The Implementation of Functional Programming Languages_.
lc_translate(Expr, [B0|Bs], Libnames) ->
    case erl_syntax:type(B0) of
        generator ->
            V = erl_syntax:generator_pattern(B0),
            L = erl_syntax:generator_body(B0),
            Op = ca(B0, erl_syntax:atom(dict:fetch(flat1map, Libnames))),
            C = ca(B0, erl_syntax:clause([V],[],[lc_translate(Expr, Bs, Libnames)])),
            Fun = ca(B0, erl_syntax:fun_expr([C])),
            ca(B0, erl_syntax:application(Op, [Fun, L]));
        binary_generator ->
            todo = finish_this;
        _ ->
            Conseq = ca(B0, erl_syntax:clause([ca(B0, erl_syntax:atom(true))], [],
                                              [lc_translate(Expr, Bs, Libnames)])),
            Alter = ca(B0, erl_syntax:clause([ca(B0, erl_syntax:atom(false))], [],
                                             [ca(B0, erl_syntax:nil())])),
            ca(B0, erl_syntax:case_expr(B0, [Conseq, Alter]))
    end;
lc_translate(Expr, [], _) ->
    ca(Expr, erl_syntax:cons(Expr, ca(Expr, erl_syntax:nil()))).

%% An infix expression becomes a call.
infix_translate(E0, Libnames, Fname) ->
    L = erl_syntax:infix_expr_left(E0),
    R = erl_syntax:infix_expr_right(E0),
    Ap = ca(E0, erl_syntax:atom(dict:fetch(Fname, Libnames))),
    ca(E0, erl_syntax:application(Ap, [L, R])).

%% Copy line info
ca(Src, Dst) -> erl_syntax:copy_attrs(Src, Dst).
