%% -*- coding: utf-8; mode: erlang -*-
%% @copyright 2012 Göran Weinholt
%% @author Göran Weinholt <goran@weinholt.se>
%% @doc Pattern matching utilities.

-module(scp_pattern).
-export([pattern_variables/1,
         is_simple_pattern/1]).

-include("scp.hrl").


%% List the variables used in a pattern.
%% TODO: see if erl_syntax_lib:variables(Expr) works just as well
pattern_variables(Expr) ->
    Vars = pv(Expr),
    gb_sets:to_list(gb_sets:from_list(Vars)).
pv({integer,_,_}) -> [];
pv({char,_,_}) -> [];
pv({float,_,_}) -> [];
pv({atom,_,_}) -> [];
pv({string,_,_}) -> [];
pv({nil,_}) -> [];
pv({var,_,'_'}) -> [];
pv({var,_,V}) -> [V];
pv({op,_,A}) -> pv(A);
pv({op,_,L,R}) -> pv(L) ++ pv(R);
pv({match,_,L,R}) -> pv(L) ++ pv(R);
pv({cons,_,H,T}) -> pv(H) ++ pv(T);
pv({tuple,_,Ps}) -> lists:flatmap(fun pv/1, Ps);
pv({bin,_,Fs}) -> lists:flatmap(fun pv_bin/1, Fs);
pv({record,_,_Name,Pfs}) -> lists:flatmap(fun pv_record/1, Pfs);
pv({record_index,_,_Name,F}) -> pv(F).
pv_record({record_field,_,{atom,_,F},P}) -> pv(P);
pv_record({record_field,_,{var,_,'_'},P}) -> pv(P).
pv_bin({bin_element,_,Value,default,Type}) -> pv(Value);
pv_bin({bin_element,_,Value,Size,Type}) -> pv(Value) ++ pv(Size).

%% A pattern is simple if no variable appears more than once.
is_simple_pattern(P) ->
    Vars = scp_expr:variables(P),
    Uniq = gb_sets:from_list(Vars),
    length(Vars) == gb_sets:size(Uniq).

%% %% Conservatively determine if a match is at all possible.
%% is_match_possible({call,_,_}, _, _) -> true;
%% is_match_possible({var,_,_}, _, _) -> true;
%% is_match_possible({match,_,_}, _, _) -> true;
%% is_match_possible(Expr, Pattern, Guard) ->
%%     %% TODO: it might be useful to look deeper into the pattern, so
%%     %% that this function returns false more often.
%%     erl_syntax:type(Expr) == erl_syntax:type(Pattern).


%% EUnit tests.

pv_test() ->
    %% XXX: sort...
    ['H','Y'] = pattern_variables({match,15,{var,15,'Y'},{match,15,{var,15,'H'},{integer,15,5}}}),
    ['X'] = pattern_variables({tuple,18,[{integer,18,1},{var,18,'X'}]}).

simple_test() ->
    false = is_simple_pattern({'block',1,[{var,1,'X'},{var,1,'X'}]}),
    true = is_simple_pattern({'block',1,[{var,1,'X'},{var,1,'Y'}]}).
