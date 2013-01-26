-ifdef(SUPERCOMPILE).
-compile({parse_transform, erlang_supercompiler}).
-endif.

-define(MAKE_RUN(F,A),
        make_run([A]) -> fun () -> F(A) end).
-define(MAKE_RUN(F,A,B),
        make_run([A,B]) -> fun () -> F(A,B) end).
-define(MAKE_RUN(F,A,B,C),
        make_run([A,B,C]) -> fun () -> F(A,B,C) end).
