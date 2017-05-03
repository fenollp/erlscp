-module(deforestation3).
-export([a/0, b/0]).

-define(APP, my_app).

a() -> atom_to_list(?APP).

b() -> "my_app".
