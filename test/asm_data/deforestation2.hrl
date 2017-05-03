-module(deforestation2).
-export([a/0, b/0]).

-define(APP_VERSION, <<"0.1.0">>).

a() -> "User Agent/" ++ binary_to_list(?APP_VERSION).

b() -> "User Agent/0.1.0".
