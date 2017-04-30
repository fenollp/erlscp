%% -*- coding: utf-8; mode: erlang -*-

%% Copyright (C) 2012-2013, 2017 Göran Weinholt <goran@weinholt.se>

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

%% Translates list comprehensions, records, etc into simpler code.

-module(scp_desugar).
-export([forms/4]).
-include("scp.hrl").

%% Libnames is a dict containing the names for some standard
%% functions. Records is a dict of record names to definitions.
forms([F={function,_,Name,Arity,_}|Fs], Libnames, Records, InlinedModuleFuns) ->
    Expr0 = scp_expr:function_to_fun(F),
    Expr = desugar(Expr0, Libnames, Records, InlinedModuleFuns),
    Function = scp_expr:fun_to_function(erl_syntax:revert(Expr), Name, Arity),
    [Function|forms(Fs, Libnames, Records, InlinedModuleFuns)];
forms([X|Xs], Libnames, Records, InlinedModuleFuns) ->
    [X|forms(Xs, Libnames, Records, InlinedModuleFuns)];
forms([], _, _, _) ->
    [].

desugar(E0, Libnames, Records, InlinedModuleFuns) ->
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
                  record_expr ->
                      %% Rewrite record expressions to tuples.
                      Type = erl_syntax:record_expr_type(Node),
                      case erl_syntax:type(Type) of
                          atom ->
                              case dict:find(erl_syntax:atom_value(Type), Records) of
                                  {ok,RecordDef} ->
                                      record_expr_translate(Node, RecordDef);
                                  _ -> Node
                              end;
                          _ -> Node
                      end;
                  module_qualifier ->
                      %% Rewrite some module functions to our own functions.
                      Module = erl_syntax:atom_value(erl_syntax:module_qualifier_argument(Node)),
                      Function = erl_syntax:atom_value(erl_syntax:module_qualifier_body(Node)),
                      case dict:find({Module,Function}, InlinedModuleFuns) of
                          {ok,NewName} ->
                              erl_syntax:atom(dict:fetch(NewName, Libnames));
                          _ ->
                              Node
                      end;
                  _ -> Node
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

%% Rewrite record expressions to tuple expressions. Def is a list of
%% record_field tuples. Only #r{...} is rewritten for now.
record_expr_translate(E, Def) ->
    case erl_syntax:record_expr_argument(E) of
        none ->
            RecordType = erl_syntax:record_expr_type(E),
            Updates = erl_syntax:record_expr_fields(E),
            ?DEBUG("From Def: ~p~nFrom E: ~p~n", [Def, Updates]),
            Record0 = record_initial_tuple(Def),
            ?DEBUG("Initial tuple: ~p~n", [Record0]),
            Record = record_update_fields(Record0, Def, Updates),
            ?DEBUG("Updated tuple: ~p~n", [Record]),
            erl_syntax:revert(erl_syntax:tuple([RecordType|Record]));
        _ -> E
    end.

record_field_value(F) ->
    case erl_syntax:record_field_value(F) of
        none ->
            ca(F, erl_syntax:atom("undefined"));
        E ->
            E
    end.

record_initial_tuple([F|Fs]) ->
    V = record_field_value(F),
    [erl_syntax:revert(V)|record_initial_tuple(Fs)];
record_initial_tuple([]) ->
    [].

record_update_fields(Record0, Defs, [F|Fs]) ->
    FieldName = erl_syntax:atom_value(erl_syntax:record_field_name(F)),
    FieldValue = erl_syntax:record_field_value(F),
    Record = record_update_one(Record0, Defs, FieldName, FieldValue),
    record_update_fields(Record, Defs, Fs);
record_update_fields(Record, _, []) ->
    Record.

record_update_one([Field|Fields], [Def|Defs], FieldName, FieldValue) ->
    DefName = erl_syntax:atom_value(erl_syntax:record_field_name(Def)),
    case DefName of
        FieldName ->
            [FieldValue|Fields];
        _ ->
            [Field|record_update_one(Fields, Defs, FieldName, FieldValue)]
    end.
