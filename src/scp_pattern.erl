%% -*- coding: utf-8; mode: erlang -*-
%% @copyright 2012 Göran Weinholt
%% @author Göran Weinholt <goran@weinholt.se>
%% @doc Pattern matching utilities.

-module(scp_pattern).
-export([pattern_variables/1,
         find_matching_const/3,
         simplify/3]).

-include("scp.hrl").


%% List the variables used in a pattern.
%% TODO: see if erl_syntax_lib:variables(Expr) works just as well
pattern_variables(Expr) ->
    Vars = erl_syntax_lib:variables(Expr),
    sets:to_list(Vars).
%% pattern_variables(Expr) ->
%%     Vars = pv(Expr),
%%     gb_sets:to_list(gb_sets:from_list(Vars)).
%% pv({integer,_,_}) -> [];
%% pv({char,_,_}) -> [];
%% pv({float,_,_}) -> [];
%% pv({atom,_,_}) -> [];
%% pv({string,_,_}) -> [];
%% pv({nil,_}) -> [];
%% pv({var,_,'_'}) -> [];
%% pv({var,_,V}) -> [V];
%% pv({op,_,A}) -> pv(A);
%% pv({op,_,L,R}) -> pv(L) ++ pv(R);
%% pv({match,_,L,R}) -> pv(L) ++ pv(R);
%% pv({cons,_,H,T}) -> pv(H) ++ pv(T);
%% pv({tuple,_,Ps}) -> lists:flatmap(fun pv/1, Ps);
%% pv({bin,_,Fs}) -> lists:flatmap(fun pv_bin/1, Fs);
%% pv({record,_,_Name,Pfs}) -> lists:flatmap(fun pv_record/1, Pfs);
%% pv({record_index,_,_Name,F}) -> pv(F).
%% pv_record({record_field,_,{atom,_,F},P}) -> pv(P);
%% pv_record({record_field,_,{var,_,'_'},P}) -> pv(P).
%% pv_bin({bin_element,_,Value,default,Type}) -> pv(Value);
%% pv_bin({bin_element,_,Value,Size,Type}) -> pv(Value) ++ pv(Size).

%% A pattern is simple if no variable appears more than once and there
%% are no match expressions.
%% is_simple_pattern(P) ->
%%     Vars = scp_expr:variables(P),
%%     Uniq = gb_sets:from_list(Vars),
%%     length(Vars) == gb_sets:size(Uniq) andalso
%%         scp_expr:matches(P) == [].

%% Go over the list of clauses left to right and return the clauses
%% that could match the constant E. Each clause is the tuple
%% {Taken,Clause}, where Taken==yes if it's certain that the clause
%% will be taken. Only works with constant expressions (including the
%% empty tuple) and patterns that are constants.
find_matching_const(Bs, E, Cs0) ->
    %%io:fwrite("find_matching_const(~p, ~p)~n => ~p~n",[E,Cs,fmcc(E, Cs)]),
    Cs = impossible(Bs, E, Cs0),                %also handles variables
    fmcc(E, Cs).

fmcc(E={T,_,V}, [C={clause,_,[{T,_,V}],_,_}|Cs]) -> fmcc_cons(E, {yes,C}, Cs);
fmcc(E={T,_,_}, [C={clause,_,[{T,_,_}],_,_}|Cs]) -> fmcc(E, Cs);
fmcc(E={nil,_}, [C={clause,_,[{nil,_}],_,_}|Cs]) -> fmcc_cons(E, {yes,C}, Cs);
fmcc(E, [C|Cs]) -> [{maybe,C}|fmcc(E, Cs)];
fmcc(_, []) -> [].
%%fmcc_cons(E, C={Taken,{clause,_,_,[],_}}, Cs) -> [C];
fmcc_cons(E, C={Taken,{clause,L,P,Guard,B}}, Cs) ->
    case static_eval(E, Guard) of
        true -> [{Taken,{clause,L,P,[],B}}];
        false -> fmcc(E, Cs);
        _ -> [C|fmcc(E, Cs)]
    end.

%% Statically evaluate a guard.
static_eval(_, []) -> true;
static_eval(_, [[{atom,_,true}]]) -> true;
static_eval(_, [[{atom,_,_}]]) -> false;        %XXX: check is this is really true
static_eval(_E, _G) -> maybe.


%% Perform one simplification on a case expression. Given the bound
%% variables Bs and the expression E (which must be a constructor),
%% return a new E, an extracted expression and a new list of clauses.
%% Each clause may also have a variable name associated with it, to
%% which the extracted expression should be bound.

simplify(Bs, E0, Cs0) ->
    io:fwrite("simplify E0=~p~n Cs0=~p~n",[E0,Cs0]),
    {E1,Cs1} = trivial(E0, Cs0),
    io:fwrite("trivial E1=~p~n Cs1=~p~n",[E1,Cs1]),
    Cs = impossible(Bs, E1, Cs1),
    io:fwrite("impossible ~n Cs=~p~n",[Cs]),
    %% TODO: extract a common field
    E = E1,
    {E,nothing,[{C,nothing} || C <- Cs]}.


trivial(E0={tuple,_,[A]}, Cs0) ->
    %% Do not construct a tuple if it can be avoided.
    AllOne = lists:all(fun ({clause,_,[P],G,B}) ->
                               case P of
                                   {tuple,_,[_]} -> true;
                                   _ -> false
                               end
                       end, Cs0),
    if AllOne == true ->
            E = A,
            Cs = lists:map(fun ({clause,Lc,[{tuple,_,[P0]}],G,B}) ->
                                   {clause,Lc,[P0],G,B}
                           end, Cs0);
       true ->
            E = E0,
            Cs = Cs0
    end,
    {E, Cs};

trivial(E0={cons,_,H,{nil,_}}, Cs0) ->
    %% Do not cons if it can be avoided.
    AllOne = lists:all(fun ({clause,_,[P],_,_}) ->
                               case P of
                                   {cons,_,_,{nil,_}} -> true;
                                   _ -> false
                               end
                       end, Cs0),
    if AllOne == true ->
            Cs = lists:map(fun ({clause,Lc,[{cons,_,Car,_}],G,B}) ->
                                   %% Extract the car.
                                   {clause,Lc,[Car],G,B}
                           end, Cs0),
            {H, Cs};
       true ->
            {E0, Cs0}
    end;
trivial(E0, Cs0) ->
    {E0, Cs0}.

%% Remove impossible case clauses given the scrutinee E and a list of
%% clauses Cs. If it is impossible for a clause to match the
%% expression then it should not be returned. Should not look inside
%% the operands.
impossible(Bs, E, [C={clause,_,[{match,_,_,_}],_,_}|Cs]) ->
    %% Conservatively include all matches.
    imp_cons(Bs, E, C, Cs);
impossible(Bs, E, [C={clause,L,P=[{var,_,N}],Guard,B}|Cs]) ->
    %% Unbound variables can match anything.
    case sets:is_element(N, Bs) of
        true ->
            %% But this variable is bound.
            [C|impossible(Bs, E, Cs)];
        _ ->
            case static_eval(E, Guard) of
                true -> [{clause,L,P,[],B}];
                false -> impossible(Bs, E, Cs);
                _ -> [C|impossible(Bs, E, Cs)]
            end
    end;
impossible(Bs, E={tuple,_,Es1}, [C={clause,_,[{tuple,_,Es2}],_,_}|Cs])
  when length(Es1) == length(Es2) ->
    imp_cons(Bs, E, C, Cs);
impossible(Bs, E={tuple,_,_}, [C={clause,_,[{record,_,_,_,_}],_,_}|Cs]) ->
    %% Records are really tuples. TODO: could be improved if it knew
    %% the record definition
    imp_cons(Bs, E, C, Cs);
impossible(Bs, E={tuple,_,_}, [_|Cs]) ->
    impossible(Bs, E, Cs);
impossible(Bs, E={cons,_,_H,_T}, [C={clause,_,[{cons,_,_,_}],_,_}|Cs]) ->
    imp_cons(Bs, E, C, Cs);
impossible(Bs, E={cons,_,_H,_T}, [C={clause,_,[{string,_,_}],_,_}|Cs]) ->
    %% Strings are really conses.
    imp_cons(Bs, E, C, Cs);
impossible(Bs, E={cons,_,_H,_T}, [_|Cs]) ->
    impossible(Bs, E, Cs);
impossible(Bs, E, [C|Cs]) ->
    imp_cons(Bs, E, C, Cs);
impossible(Bs, _, []) ->
    [].

imp_cons(Bs, E, C={clause,_,_,Guard,_}, Cs) ->
    case static_eval(E, Guard) of
        false -> impossible(Bs, E, Cs);
        _ -> [C|impossible(Bs, E, Cs)]
    end.

%% EUnit tests.

pv_test() ->
    %% XXX: sort...
    ['H','Y'] = pattern_variables({match,15,{var,15,'Y'},{match,15,{var,15,'H'},{integer,15,5}}}),
    ['X'] = pattern_variables({tuple,18,[{integer,18,1},{var,18,'X'}]}).

impossible_test() ->
    E = {atom,1,foo},
    Cs0 = [{clause,1,[{atom,1,bar}],[],[{integer,1,0}]},
           {clause,1,[{atom,1,foo}],[],[{integer,1,1}]}],
    Cs = impossible(sets:new(), E, Cs0),
    Cs = Cs0.
