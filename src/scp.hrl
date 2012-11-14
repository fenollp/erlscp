
-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

%% Environments.
-record(env, {used = [],                        %passed upwards
              ls = [],
              memo = [],
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
              %% The name of the function begin supercompiled.
              name = "",
              forms = []}).

%% Contexts.
-record(op_ctxt, {line, op, e1}).           %op(e0, e1)
-record(call_ctxt, {line, args}).           %call(<hole>, args...)
-record(case_ctxt, {line, clauses}).        %case <hole> of clauses...
-record(cons_ctxt, {line, tail}).           %[<hole>|tail]
