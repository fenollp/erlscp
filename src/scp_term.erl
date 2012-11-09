%% -*- coding: utf-8; mode: erlang -*-
%% @copyright 2012 Göran Weinholt
%% @author Göran Weinholt <goran@weinholt.se>
%% @doc Miscellaneous tools for working with Erlang terms.

-module(scp_term).
-export([list_to_block/2, make_block/3,
         function_to_fun/1, fun_to_function/3,
         simplify/1,
         free_variables/2,
         gensym/2, alpha_convert/2]).
-include("scp.hrl").

%% Convert a list of expressions (such as in a function body) into
%% nested blocks.
list_to_block(_Line,[X]) ->
    X;
list_to_block(Line,[X|Xs]) ->
    make_block(Line, X, list_to_block(Line, Xs)).

%% From Oscar Waddell's dissertation. The return expression for whole
%% the block becomes the second expression of the block.
make_block(L0, E1, E2) ->
    case is_simple(E1) of
        true -> E2;
        false ->
            E1n = case E1 of
                      {'block',_,[E1a,E1b]} ->
                          case is_simple(E1b) of
                              true -> E1a;
                              _ -> E1
                          end;
                      _ -> E1
                  end,
            case E2 of
                {'block',L1,[E3,E4]} ->
                    {'block',L1,{'block',L0,[E1n,E3]},E4};
                _ ->
                    {'block',L0,[E1n,E2]}
            end
    end.

is_simple({var,_,_}) -> true;
is_simple({integer,_,_}) -> true;
is_simple({float,_,_}) -> true;
is_simple({atom,_,_}) -> true;
is_simple({string,_,_}) -> true;
is_simple({char,_,_}) -> true;
is_simple({nil,_,_}) -> true;
is_simple({'fun',_,_}) -> true;
is_simple(_) -> false.

%% Conversion between global and local functions.
function_to_fun({function,Line,_Name,_Arity,Clauses}) ->
    {'fun',Line,{clauses,Clauses}}.
fun_to_function({'fun',Line,{clauses,Clauses}},Name,Arity) ->
    {function,Line,Name,Arity,Clauses}.

%% TODO: Simplifies a form which was given to the parser transform.
%% Turns all bodies and blocks into two-armed blocks.
simplify({block,L,Es}) ->
    list_to_block(L, Es);
simplify(Expr) ->
    Expr.

delete_duplicates([X|Xs]) -> [X|[Y || Y <- Xs, X =/= Y]];
delete_duplicates([]) -> [].

%% Find the free variables of an expression.
free_variables(Expr) ->
    {_,Free} = fv([],Expr),
    delete_duplicates(Free).
free_variables(Bound, Expr) ->
    %% Find free variables that are also bound outside the expression.
    [ V || V <- free_variables(Expr), sets:is_element(V, Bound) ].

%% free_variables(Expr) ->
%%     %% This is really nice, but unfortunately uses ordered sets.
%%     Tree = erl_syntax_lib:annotate_bindings(Expr, ordsets:new()),
%%     Ann = erl_syntax:get_ann(),
%%     case lists:keyfind(free, 0, Ann) of
%%         {_,Free} ->
%%             Free;
%%         _ -> []
%%     end.

%% Bs is a list of bound variables.
fv(Bs,{var,_,V}) ->
    case lists:member(V,Bs) of
        true -> {[],[]};
        false -> {[],[V]}
    end;
fv(_,{integer,_,_}) -> {[],[]};
fv(_,{float,_,_}) -> {[],[]};
fv(_,{atom,_,_}) -> {[],[]};
fv(_,{string,_,_}) -> {[],[]};
fv(_,{char,_,_}) -> {[],[]};
fv(_,{nil,_,_}) -> {[],[]};
fv(Bs,{op,_,_Op,A}) -> fv(Bs, A);
fv(Bs,{op,_,_Op,A,B}) -> fv_list(Bs, [A,B]);
fv(Bs,{call,_,F,As}) ->
    {D0,F0} = fv(Bs, F),
    {D1,F1} = fv_list(Bs, As),
    {D0++D1,F0++F1};
fv(Bs,{cons,_,A,B}) -> fv_list(Bs, [A,B]);
fv(Bs,{tuple,_,Es}) -> fv_list(Bs, Es);
%% fv(Bs,{record,_,_,Is}) -> ;
%% fv(Bs,{bin,_,Fs}) -> ;
%% fv(Bs,{lc,_,E,Qs}) -> ;
%% fv(Bs,{bc,_,E,Qs}) -> ;

%% fv(Bs,{record,_,R,N,Us}) -;
%% fv(Bs,{record_index,_,N,F}) -> ;
%% fv(Bs,{record_field,_,R,N,F}) -> ;
%% fv(Bs,{record_field,_,R,F}) - ;

%% fv(Bs,{'if',_,Cs}) ->
%%     fv_icr_clauses(Bs,Cs,'if');
%% fv(Bs,{'case',_,E,Cs}) ->
%%     {D0,F0} = fv(Bs,E),
%%     {D1,F1} = fv_icr_clauses(Bs,Cs,'case'),
%%     {D0++D1,F0++F1};
%% fv(Bs,{'receive',_,Cs}) ->
%%     fv_icr_clauses(Bs,Cs,'receive');
%% fv(Bs,{'receive',_,Cs,To,ToEs}) ->
%%     {D0,F0} = fv_icr_clauses(Bs,Cs,'receive'),
%%     {D1,F1} = fv_list([Cs|ToEs]),
%%     {D0++D1,F0++F1};
%% fv(Bs,{'try',_,Es,Scs,Ccs,As}) -> ;
%% fv(Bs,{'fun',_,Body}) ->
%%     %% This defines all pattern variables, shadowing those already
%%     %% bound.
%%     case Body of
%%         {clauses,Cs} -> fv_fun_clauses(Cs);
%%         {function,F,A} -> {[],[]};
%%         {function,M,F,A} ->
%%     end;
fv(Bs,{'catch',_,E}) -> fv(Bs,E);
fv(Bs,{remote,_,M,F}) -> fv_list(Bs, [M,F]);

fv(Bs,{match,_,P,E}) ->
    %% This defines all pattern variables, except those already bound.
    D = scp_pattern:pattern_variables(P) -- Bs,
    {D0,F0} = fv(Bs, E),
    {D++D0, F0};
fv(Bs,{block,_,[A,B]}) ->
    %% Variables defined in A are not free in B.
    {D0,F0} = fv(Bs, A),
    {D1,F1} = fv(Bs++D0, B),
    {D0++D1,F0++(F1--D0)}.

fv_list(Bs,Es) ->
    {D,F} = lists:unzip(lists:map(fun (X) -> fv(Bs, X) end, Es)),
    {lists:flatten(D),lists:flatten(F)}.

%% if, case, receive: variables defined in all branches are defined
%% outside the expression afterwards. For try expression this is
%% currently not so, but may be in the future. Variables may be
%% defined in either the pattern or the body.
%% fv_icr_clauses(Bs,Cs,Keyword) ->
%%     .

%% Generate a fresh variable.
gensym(Env0, Prefix) ->
    F = fun (N) -> Prefix ++ integer_to_list(N) end,
    Name = erl_syntax_lib:new_variable_name(F, Env0#env.seen_vars),
    Env = Env0#env{seen_vars=sets:add_element(Name, Env0#env.seen_vars)},
    {Env,list_to_atom(Name)}.

%% Alpha conversion. Generates fresh names for all variables
%% introduced in the expression.
alpha_convert(Env0, Expr0) ->
    {Env1,_S,Expr} = ac(Env0,dict:new(),Expr0),
    Env = Env0#env{seen_vars = Env1#env.seen_vars},
    {Env, Expr}.

ac(Env,S,E={var,L,'_'}) -> {Env,S,E};
ac(Env,S,E={var,L,V}) ->
    %% Look up V in the substitution environment.
    case dict:find(V, S) of
        {ok,V1} -> {Env,S,{var,L,V1}};
        _ -> {Env,S,E}
    end;
ac(Env,S,E={integer,_,_}) -> {Env,S,E};
ac(Env,S,E={float,_,_}) -> {Env,S,E};
ac(Env,S,E={atom,_,_}) -> {Env,S,E};
ac(Env,S,E={string,_,_}) -> {Env,S,E};
ac(Env,S,E={char,_,_}) -> {Env,S,E};
ac(Env,S,E={nil,_,_}) -> {Env,S,E};
ac(Env0,S0,{call,L,F0,Es0}) ->
    {Env,S,[F|Es]} = ac_list(Env0,S0,[F0|Es0]),
    {Env,S,{call,L,F,Es}};
ac(Env0,S0,{op,L,Op,A0}) ->
    {Env,S,A} = ac(Env0,S0,A0),
    {Env,S,{op,L,Op,A}};
ac(Env0,S0,{op,L,Op,A0,B0}) ->
    {Env,S,[A,B]} = ac_list(Env0,S0,[A0,B0]),
    {Env,S,{op,L,Op,A,B}};
ac(Env0,S0,{cons,L,A0,B0}) ->
    {Env,S,[A,B]} = ac_list(Env0,S0,[A0,B0]),
    {Env,S,{cons,L,A,B}};
ac(Env0,S0,{tuple,L,Es0}) ->
    {Env,S,Es} = ac_list(Env0,S0,Es0),
    {Env,S,{tuple,L,Es}};

ac(Env0,S0,{'fun',L,{clauses,Cs0}}) ->
    {Env,S,Cs} = ac_fun_clauses(Env0,S0,Cs0),
    {Env,S,{'fun',L,{clauses,Cs}}};
ac(Env,S,E={'fun',L,{function,_,_}}) ->
    {Env,S,E};
ac(Env,S,E={'fun',L,{function,M,F,A}}) when is_atom(M), is_atom(F), is_integer(A) ->
    {Env,S,E};
ac(Env0,S0,{'fun',L,{function,M0,F0,A0}}) ->
    {Env,S,[M,F,A]} = ac_list(Env0,S0,[M0,F0,A0]),
    {Env,S,{'fun',L,{function,M,F,A}}};

ac(Env0,S0,{match,L,P0,E0}) ->
    %% An unbound variable defined in P0 may already have been seen in
    %% a different pattern but not yet been bound. It'll be in S then,
    %% and it should not receive a new name.
    Names0 = lists:filter(fun (Name) -> not dict:is_key(Name, S0) end,
                          scp_pattern:pattern_variables(P0)),
    %% Pattern variables also in Env0#env.in_set are not shadowed.
    Names = sets:subtract(sets:from_list(Names0), Env0#env.bound),
    {Env1,S1} = fresh_names(Env0, S0, sets:to_list(Names)),
    %% Variables defined in P0 are visible after this expression.
    Env2 = Env1#env{bound = sets:union(Env0#env.bound, Names)},
    {Env3,S2,P} = ac(Env2,S1,P0),
    {Env,S,E} = ac(Env3,S2,E0),
    {Env,S,{match,L,P,E}};

ac(Env0,S0,{block,L,[A0,B0]}) ->
    %% Variables defined in A are bound in B.
    {Env1,S1,A} = ac(Env0,S0,A0),
    {Env,S,B} = ac(Env1,S1,B0),
    {Env,S,{block,L,[A,B]}}.

ac_list(Env0,S0,[E0|Es0]) ->
    %% The rule here is that definitions made in expressions are
    %% visible only after the expressions, but different definitions
    %% can refer to the same unbound variable.
    {Env1,S1,E} = ac(Env0, S0, E0),
    %% The rest of the expressions have the same set of bound
    %% variables as E0.
    {Env2,S2,Es} = ac_list(Env1#env{bound=Env0#env.bound}, S1, Es0),
    %% The variables visible afterwards is the union of the variables
    %% bound by the expressions.
    Env = Env2#env{bound = sets:union(Env1#env.bound, Env2#env.bound)},
    {Env,S2,[E|Es]};
ac_list(Env,S,[]) ->
    {Env,S,[]}.

ac_fun_clauses(Env0,S0,[{clause,L,H0,G0,B0}|Cs0]) ->
    %% Variables defined in head shadow those which have already been
    %% bound, so their substitutions are removed here.
    Shadowing = lists:flatmap(fun scp_pattern:pattern_variables/1, H0),
    S1 = dict:filter(fun (Name,_) -> not lists:member(Name,Shadowing) end,
                     S0),
    {Env1,S2,H} = ac_head(Env0, S1, H0),
    {Env2,S3,G} = ac_guard(Env1, S2, G0),
    {Env3,S4,B} = ac_list(Env2, S3, B0),
    C = {clause,L,H,G,B},
    {Env4,S,Cs} = ac_fun_clauses(Env3, S4, Cs0),
    %% Freshly bound variables are not visible outside the clause.
    Env = Env4#env{bound=Env0#env.bound},
    {Env,S0,[C|Cs]};
ac_fun_clauses(Env,S,[]) ->
    {Env,S,[]}.

ac_head(Env0,S0,[P0|Ps0]) ->
    %% The pattern variables that need fresh names are those which
    %% have not yet been given a fresh name.
    Names = lists:filter(fun (Name) -> not dict:is_key(Name, S0) end,
                         scp_pattern:pattern_variables(P0)),
    %% The names defined in a head are bound in guard and body.
    Env1 = Env0#env{bound = sets:union(Env0#env.bound,
                                       sets:from_list(Names))},
    {Env2,S1} = fresh_names(Env1, S0, Names),
    {Env3,S2,P} = ac(Env2, S1, P0),
    {Env,S,Ps} = ac_head(Env3, S2, Ps0),
    {Env,S,[P|Ps]};
ac_head(Env0,S0,[]) ->
    {Env0,S0,[]}.

ac_guard(Env0,S0,[]) ->
    %% XXX: probably can't change Env and S?
    %% TODO:
    {Env0,S0,[]}.

fresh_names(Env0,S0,Names) ->
    %% Updates the substitution dict S0 with fresh names for Names.
    lists:foldl(fun (V, {Env0,S0}) ->
                        %% Generate a new variable name
                        %% for each variable in the
                        %% pattern.
                        {Env,GV} = gensym(Env0, atom_to_list(V)),
                        S = dict:store(V, GV, S0),
                        {Env,S}
                end,
                {Env0,S0},
                Names).

%% EUnit tests.

fv0_test() ->
    {_,['Y']} = fv([],{match,1,{var,1,'X'},{var,1,'Y'}}).
fv1_test() ->
    {['X'],[]} = fv(['Y'],{match,1,{var,1,'X'},{var,1,'Y'}}).
fv2_test() ->
    {_,['X']} = fv([],{call,43,
                       {atom,43,foo},
                       [{op,43,'+',{var,43,'X'},{integer,43,1}}]}).
fv3_test() ->
    {['X'],['Y']} = fv([],{block,1,[{match,1,{var,1,'X'},{var,1,'Y'}},
                                    {var,1,'X'}]}).
fv4_test() ->
    {['Z'],['Y','X']} = fv([],{block,1,[{match,1,{var,1,'Z'},{var,1,'Y'}},
                                        {var,1,'X'}]}).

check_ac(E0) ->
    Vars0 = erl_syntax_lib:variables(E0),
    {Env,E1} = alpha_convert(#env{seen_vars=Vars0}, E0),
    io:fwrite("Result: ~p~n",[E1]),
    io:fwrite("Env: ~p~n",[Env]),
    %% TODO: check that E1 is a renaming
    true = E1 =/= E0,
    Vars1 = erl_syntax_lib:variables(E1),
    N0 = sets:size(Vars0),
    N0 = sets:size(Vars1).

ac0_test() ->
    E0 = {'fun',43,
          {clauses,
           [{clause,43,
             [{var,43,'X'}],
             [],
             [{op,44,'+',{var,44,'X'},{integer,44,1}}]}]}},
    check_ac(E0).

ac1_test() ->
    E0 = {'fun',43,
          {clauses,
           [{clause,43,
             [{var,43,'X'}],
             [],
             [{block,43,
               [{match,44,{var,44,'X'},{integer,44,0}},
                {var,45,'X'}]}]}]}},
    check_ac(E0).

ac2_test() ->
    E0 = {'fun',43,
          {clauses,
           [{clause,43,
             [{var,43,'X'}],
             [],
             [{block,43,
               [{match,44,
                 {tuple,44,[{var,44,'X'},{var,44,'Y'}]},
                 {tuple,44,[{var,44,'X'},{integer,44,1}]}},
                {var,45,'X'}]}]}]}},
    check_ac(E0).

ac3_test() ->
    E0 = {'fun',43,
          {clauses,
           [{clause,43,
             [{var,43,'X'},{var,43,'X'}],
             [],
             [{block,43,
               [{match,44,
                 {tuple,44,[{var,44,'X'},{var,44,'Y'}]},
                 {tuple,44,[{var,44,'X'},{integer,44,1}]}},
                {var,45,'X'}]}]}]}},
    check_ac(E0).

ac4_test() ->
    E0 = {'fun',47,
          {clauses,
           [{clause,47,[],[],
             [{op,48,'+',
               {match,48,{var,48,'X'},{integer,48,1}},
               {match,48,{var,48,'X'},{integer,48,1}}}]}]}},
    check_ac(E0).

ac5_test() ->
    E0 = {'fun',47,
          {clauses,
           [{clause,47,[],[],
             [{call,48,{atom,48,'foo'},
               [{match,48,{var,48,'X'},{integer,48,1}},
                {match,48,{var,48,'X'},{integer,48,1}}]}]}]}},
    check_ac(E0).
