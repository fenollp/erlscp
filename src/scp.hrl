
-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

%% Environments.
-record(env, {found = [],
              w = [],
              ls = [],
              memo = [],
              %% This contains the variables that were returned in a
              %% substitution created by scp_generalize:split/2.
              split_vars = [],
              bound = sets:new(),
              %% Global and local functions. The keys are {Name,Arity}
              %% and the values are fun terms.
              global = dict:new(),
              local = dict:new(),
              %% seen_vars keeps track of all the variable names which
              %% have been seen anywhere. It's used when generating
              %% fresh names (gensym).
              seen_vars = sets:new(),
              %% The name of the function being supercompiled.
              name = "",
              %% The whistle can be disabled.
              whistle_enabled = true,
              no_whistling = sets:new()}).

-define(IS_CONST_TYPE(T),
        T=='integer';
            T=='float';
            T=='atom';
            T=='string';
            T=='char';
            T=='nil').

-define(IS_CONST_EXPR(E),
        ?IS_CONST_TYPE(element(1,E));
            element(1,E)=='tuple', element(3,E)==[]).

%%-define(DEBUG(P,A), (io:fwrite(P,A))).
-define(DEBUG(P,A), (false)).
