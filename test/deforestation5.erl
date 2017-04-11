-module(deforestation5).
-export([a/0, b/0]).

-define(APP, my_app).

a() -> atom_to_binary(?APP, utf8).

b() -> <<"my_app">>.
