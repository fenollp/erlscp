
-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

%% Environments.
-record(env, {used = [],			%passed upwards
	      ls = [],
	      split_vars = [],
	      in_set = [],
	      global = [],
	      local = [],
	      fun_names = [],
	      forms = []}).

%% Contexts.
-record(op_ctxt, {line, e0, e1}).	      %op(e0, e1)
-record(call_ctxt, {line, args}).	      %call(<hole>, args...)
-record(case_ctxt, {line, clauses}).	      %case <hole> of clauses...
