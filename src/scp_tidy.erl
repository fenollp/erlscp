%% -*- coding: utf-8; mode: erlang -*-
%% @copyright 2012 Göran Weinholt
%% @author Göran Weinholt <goran@weinholt.se>
%% @doc Tidy up the residual program.

-module(scp_tidy).
-export([function/1]).
-include("scp.hrl").

function(X0) ->
    flatten_bodies(X0).

%% Remove block expressions from clause bodies.
flatten_bodies(E0) ->
    E = erl_syntax_lib:map(
          fun (Node) ->
                  case erl_syntax:type(Node) of
                      clause ->
                          B0 = erl_syntax:clause_body(Node),
                          B = lists:flatten([flatten(flatten_bodies(E)) || E <- B0]),
                          E = erl_syntax:clause(erl_syntax:clause_patterns(Node),
                                                erl_syntax:clause_guard(Node),
                                                B),
                          erl_syntax:copy_attrs(Node, E);
                      _ ->
                          Node
                  end
          end,
          E0),
    erl_syntax:revert(E).

flatten({block,_,Xs}) ->
    lists:flatten([flatten(X) || X <- Xs]);
flatten(X) ->
    X.

%% TODO: nicer variable names

%% TODO: lift out the clauses in fun (X) -> case X of ... end end.
