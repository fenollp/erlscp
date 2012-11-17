%% -*- coding: utf-8; mode: erlang -*-
%% @copyright 2012 Göran Weinholt
%% @author Göran Weinholt <goran@weinholt.se>
%% @doc Pattern matching utilities.

-module(scp_pattern).
-export([pattern_variables/1,
         is_simple_pattern/1,
         find_matching_const/2,
         find_matching_clauses/3]).

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

%% A pattern is simple if no variable appears more than once and there
%% are no match expressions.
is_simple_pattern(P) ->
    Vars = scp_expr:variables(P),
    Uniq = gb_sets:from_list(Vars),
    length(Vars) == gb_sets:size(Uniq) andalso
        scp_expr:matches(P) == [].

%% %% Conservatively determine if a match is at all possible.
%% is_match_possible({call,_,_}, _, _) -> true;
%% is_match_possible({var,_,_}, _, _) -> true;
%% is_match_possible({match,_,_}, _, _) -> true;
%% is_match_possible(Expr, Pattern, Guard) ->
%%     %% TODO: it might be useful to look deeper into the pattern, so
%%     %% that this function returns false more often.
%%     erl_syntax:type(Expr) == erl_syntax:type(Pattern).

%% Go over the list of clauses left to right and return the clauses
%% that could match the constant E. Only works with constant
%% expressions (including the empty tuple) and patterns that are
%% constants.
find_matching_const(E, Cs) ->
    io:fwrite("find_matching_const(~p, ~p)~n",[E,Cs]),
    fmcc(E, Cs).

fmcc(E={T,_,V}, [C={clause,_,[{T,_,V}],_,_}|Cs]) -> fmcc_cons(E, C, Cs);
fmcc(E={T,_,_}, [C={clause,_,[{T,_,_}],_,_}|Cs]) -> fmcc(E, Cs);
fmcc(E={nil,_}, [C={clause,_,[{nil,_}],_,_}|Cs]) -> fmcc_cons(E, C, Cs);
fmcc(E, [C|Cs]) -> [C|fmcc(E, Cs)];
fmcc(_, []) -> [].
fmcc_cons(E, C={clause,_,_,[],_}, Cs) -> [C];
fmcc_cons(E, C={clause,L,P,Guard,B}, Cs) ->
    case static_eval(E, Guard) of
        true -> [{clause,L,P,[],B}];
        false -> fmcc(E, Cs);
        _ -> [C|fmcc(E, Cs)]
    end.

static_eval(_, [[{atom,_,true}]]) -> true;
static_eval(_, [[{atom,_,_}]]) -> false;
static_eval(_, _) -> maybe.

%% Given the bound variables Bs and the expression E (which must be a
%% constructor and simple), return a new E and the list
%% of clauses that have the potential to match. The constructors are
%% cons, tuple, bin and record.
find_matching_clauses(Bs, E, Cs) ->
    case scp_expr:matches(E) of
        [] ->
            %% TODO: check for bound variables
            fmc(Bs, E, Cs);
        _ ->
            %% The expression contains a match and fmc is currently
            %% too weak to handle that.
            {E,[{C,[]} || C <- Cs]}
    end.

%% Handle very simple conses (only [X|Xs]).
fmc(Bs, E={cons,_,RH,RT}, [C={clause,_,[{cons,_,LH={var,_,_},LT={var,_,_}}],_,_}|Cs]) ->
    %% TODO: must not return {var,_,'_'} as a left-hand side
    fmc_cons(Bs, E, {C,[{LH,RH},{LT,RT}]}, Cs);
fmc(Bs, E={cons,_,_,_}, [C={clause,_,[{cons,_,_,_}],_,_}|Cs]) ->
    fmc_cons(Bs, E, {C,[]}, Cs);
fmc(Bs, E={cons,_,_,_}, [_|Cs]) ->
    fmc(Bs, E, Cs);

fmc(Bs, E, [C|Cs]) ->
    %% Be on the safe side and include this clause.
    [{C,[]}|fmc(Bs, E, Cs)];
fmc(Bs, E, []) ->
    [].

fmc_cons(Bs, E, C={{clause,_,_,[],_},_}, Cs) ->
    %% Called by fmc() when it finds a pattern that it knows will
    %% match E. If there's no guard then there's no need to look at
    %% the rest of the clauses.
    {E,[C]};
fmc_cons(Bs, E0, C={{clause,_,_,_Guard,_},_}, Cs0) ->
    {E,Cs} = fmc(Bs, E0, Cs0),
    {E,[C|Cs]}.

%% EUnit tests.

pv_test() ->
    %% XXX: sort...
    ['H','Y'] = pattern_variables({match,15,{var,15,'Y'},{match,15,{var,15,'H'},{integer,15,5}}}),
    ['X'] = pattern_variables({tuple,18,[{integer,18,1},{var,18,'X'}]}).

simple_test() ->
    false = is_simple_pattern({'block',1,[{var,1,'X'},{var,1,'X'}]}),
    true = is_simple_pattern({'block',1,[{var,1,'X'},{var,1,'Y'}]}).
