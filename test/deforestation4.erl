-module(deforestation4).
-export([a/0, b/0]).

-define(APP, my_app).

a() -> iolist_to_binary(["app [", atom_to_list(?APP), <<"]">>]).

b() -> <<"app [my_app]">>.
