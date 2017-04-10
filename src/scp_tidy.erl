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

%% Tidy up the residual program.

-module(scp_tidy).
-export([function/1]).
-include("scp.hrl").

function(X0) ->
    X1 = flatten_bodies(X0),
    X2 = lift_cases(X1),
    X3 = recover_ifs(X2),
    X4 = nicer_names(X3),
    erl_syntax:revert(X4).

%% Remove block expressions from clause bodies.
flatten_bodies(E0) ->
    erl_syntax_lib:map(
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
      end, E0).

flatten(E) ->
    case erl_syntax:type(E) of
        block_expr ->
            [flatten(X) || X <- erl_syntax:block_expr_body(E)];
        _ -> E
    end.

%% Lift out the clauses in fun (X) -> case X of ... end end. The case
%% argument can be a variable from the fun expr patterns. The case may
%% also have a tuple on it that doesn't need to be there. The patterns
%% in the fun expr must be only non repeated variables. The fun expr
%% must not have a guard. The case scrutinee must be only non-repeated
%% variables found in the patterns of the fun expr. The case clauses
%% must not reference any of the variables from the fun expr patterns.
lift_cases(E0) ->
    E = erl_syntax_lib:map(
          fun (Node) ->
                  case erl_syntax:type(Node) of
                      fun_expr ->
                          Cs0 = erl_syntax:fun_expr_clauses(Node),
                          case try_lift(Cs0) of
                              {ok,Cs} ->
                                  E = erl_syntax:fun_expr(Cs),
                                  erl_syntax:copy_attrs(Node, E);
                              _ ->
                                  Node
                          end;
                      _ ->
                          Node
                  end
          end, E0),
    erl_syntax:revert(E).

try_lift([C]) ->
    Ps = erl_syntax:clause_patterns(C),
    erl_syntax:clause_guard(C) == none andalso
        only_nonrepeating_vars(Ps) andalso
        case erl_syntax:clause_body(C) of
            [E] ->
                PNames = lists:map(fun erl_syntax:variable_name/1, Ps),
                erl_syntax:type(E) == case_expr andalso
                    begin
                        Arg = erl_syntax:case_expr_argument(E),
                        Cs = erl_syntax:case_expr_clauses(E),
                        case erl_syntax:type(Arg) of
                            variable ->
                                Name = erl_syntax:variable_name(Arg),
                                lists:member(Name, PNames) andalso
                                    not_used_elsewhere([Name], Cs) andalso
                                    {ok,lift_var(Ps, Name, Cs)};
                            tuple ->
                                Vars = erl_syntax:tuple_elements(Arg),
                                only_nonrepeating_vars(Vars) andalso
                                    lists:all(fun (C) ->
                                                      [P] = erl_syntax:clause_patterns(C),
                                                      erl_syntax:type(P) == tuple andalso
                                                          length(Vars) ==
                                                          length(erl_syntax:tuple_elements(P))
                                              end, Cs)
                                    andalso
                                    begin
                                        Names = [erl_syntax:variable_name(X) || X <- Vars],
                                        lists:all(fun (N) -> lists:member(N, PNames) end,
                                                  Names) andalso
                                            not_used_elsewhere(Names, Cs) andalso
                                            {ok,lift_tuple(Ps, Names, Cs)}
                                    end;
                            _ ->
                                false
                        end
                    end;
            _ ->
                false
        end;
try_lift(_) ->
    false.

lift_var(Ps0, Name, [C0|Cs]) ->
    %% The case argument is a variable from the fun patterns that is
    %% not used elsewhere in the case expression.
    [CaseP] = erl_syntax:clause_patterns(C0),
    Ps = lists:map(
           fun (P) ->
                   PName = erl_syntax:variable_name(P),
                   case PName of
                       Name -> CaseP;
                       _ ->
                           case not_used_elsewhere([PName],[C0]) of
                               true ->
                                   %% Do not introduce an
                                   %% unused variable in this
                                   %% clause.
                                   erl_syntax:underscore();
                               _ ->
                                   P
                           end
                   end
           end, Ps0),
    C1 = erl_syntax:clause(Ps,
                           erl_syntax:clause_guard(C0),
                           erl_syntax:clause_body(C0)),
    C = erl_syntax:copy_attrs(C0, C1),
    [C|lift_var(Ps0, Name, Cs)];
lift_var(_, _, []) ->
    [].

lift_tuple(Ps0, Names, [C0|Cs]) ->
    %% The case argument is a tuple of variables. It's possible that
    %% PNames and Names are in different orders or lengths. The
    %% patterns in Cs need to use the same order as PNames.
    CasePs = erl_syntax:tuple_elements(hd(erl_syntax:clause_patterns(C0))),
    Indices = lists:zip(Names, lists:seq(1, length(Names))),
    Ps = lists:map(
           fun (P) ->
                   PName = erl_syntax:variable_name(P),
                   case lists:keyfind(PName, 1, Indices) of
                       {_, Idx} ->
                           lists:nth(Idx, CasePs);
                       _ ->
                           P
                   end
           end, Ps0),
    C1 = erl_syntax:clause(Ps,
                           erl_syntax:clause_guard(C0),
                           erl_syntax:clause_body(C0)),
    C = erl_syntax:copy_attrs(C0, C1),
    [C|lift_tuple(Ps0, Names, Cs)];
lift_tuple(_, _, []) ->
    [].

only_nonrepeating_vars(Es) ->
    %% Check that all the expressions are nonrepeating variables.
    lists:all(fun (E) -> erl_syntax:type(E) == variable end, Es) andalso
        begin
            Names = lists:map(fun erl_syntax:variable_name/1, Es),
            length(Names) == gb_sets:size(gb_sets:from_list(Names))
        end.

not_used_elsewhere([Name|Ns], Cs) ->
    %% Check that the variable name is not used anywhere in the clauses.
    Elsewhere = erl_syntax_lib:variables(
                  erl_syntax:case_expr(erl_syntax:nil(), Cs)),
    (not sets:is_element(Name, Elsewhere))
        andalso not_used_elsewhere(Ns, Cs);
not_used_elsewhere([], _) -> true.

%% Nicer variable names. Fun is a top-level function (represented as a
%% fun expr), so it's a closed expression, which makes things easy.
%% Different clauses can use the same names without problem.
nicer_names(F0) ->
    %% Extract all the variables from the
    %% expression and make a dict containing new unique and nicer names,
    %% then do a renaming with erl_syntax:map/2.
    Cs = lists:map(fun rename_clause/1,
                   erl_syntax:fun_expr_clauses(F0)),
    F = erl_syntax:fun_expr(Cs),
    erl_syntax:copy_attrs(F0, F).

rename_clause(C) ->
    OldNames = scp_expr:delete_duplicates(scp_expr:variables(C)),
    Prefixes = [drop_suffix(scp_expr:gensym_name(N)) || N <- OldNames],
    %% io:fwrite("OldNames = ~p,~nPrefixes = ~p;~n", [OldNames,Prefixes]),
    {Subst,_} =
        lists:mapfoldl(fun ({Old,Prefix}, {Prefix,N}) ->
                               %% Same prefix as the previous name.
                               NewName = Prefix ++ integer_to_list(N),
                               {{Old,NewName},{Prefix,N + 1}};
                           ({Old,"_"}, _) ->
                               %% Don't rename anything to just _.
                               {{Old,"_0"},{"_",1}};
                           ({Old,Prefix}, _) ->
                               %% Reset the counter.
                               {{Old,Prefix},{Prefix,0}}
                       end,
                       {'',0},
                       lists:keysort(2, lists:zip(OldNames, Prefixes))),
    rename(dict:from_list(Subst), C).

%% Drop the number suffix from a string.
drop_suffix(Str) ->
    %% XXX: this turns _1 into _.
    lists:reverse(lists:dropwhile(fun (C) -> (C >= $0) and (C =< $9) end,
                                  lists:reverse(Str))).

%% Straight up renaming variables without any regard for scoping.
rename(S, E) ->
    erl_syntax_lib:map(
      fun (Node) ->
              case erl_syntax:type(Node) of
                  variable ->
                      case dict:find(erl_syntax:variable_name(Node), S) of
                          {ok,NewName} ->
                              V = erl_syntax:variable(NewName),
                              erl_syntax:copy_attrs(Node, V);
                          _ ->
                              Node
                      end;
                  _ ->
                      Node
              end
      end, E).

%% Case expressions that are just poorly written if expressions.
recover_ifs(E0) ->
    E = erl_syntax_lib:map(
          fun (Node) ->
                  case erl_syntax:type(Node) of
                      case_expr ->
                          Arg = erl_syntax:case_expr_argument(Node),
                          Cs0 = erl_syntax:case_expr_clauses(Node),
                          case try_recover_if(Arg, Cs0) of
                              {ok,Cs} ->
                                  IfE = erl_syntax:if_expr(Cs),
                                  erl_syntax:copy_attrs(Node, IfE);
                              _ ->
                                  Node
                          end;
                      _ ->
                          Node
                  end
          end, E0),
    erl_syntax:revert(E).

try_recover_if(Arg, Cs0) ->
    erl_syntax:type(Arg) == nil
        andalso
        lists:all(fun (C) ->
                          [P] = erl_syntax:clause_patterns(C),
                          erl_syntax:type(P) == nil orelse
                              erl_syntax:type(P) == underscore
                  end, Cs0)
        andalso
        {ok,lists:map(fun (C0) ->
                              %% If expr clauses must have at least one
                              %% guard.
                              G = case erl_syntax:clause_guard(C0) of
                                      none -> [[{atom,0,true}]];
                                      X -> X
                                  end,
                              B = erl_syntax:clause_body(C0),
                              C1 = erl_syntax:clause([], G, B),
                              C = erl_syntax:copy_attrs(C0, C1)
                      end, Cs0)}.


%% TODO: turn lets into matches

%% TODO: lift out if exprs just like case exprs are lifted out

%% TODO: after tidying single functions, go over all the remaining
%% functions and see if e.g. ap@N/2 happens to be a renaming of ap/2.
%% See if ap/3 merely calls ap@N/3 with the same arguments it was
%% given.

%% TODO: remove unused and unexported functions that have a gensymed name

%% TODO: case expressions that are just matches in disguise
