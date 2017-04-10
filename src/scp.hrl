%% -*- coding: utf-8; mode: erlang -*-

%% Copyright (C) 2012-2013 Göran Weinholt <goran@weinholt.se>

%% Permission is hereby granted, free of charge, to any person obtaining a
%% copy of this software and associated documentation files (the "Software"),
%% to deal in the Software without restriction, including without limitation
%% the rights to use, copy, modify, merge, publish, distribute, sublicense,
%% and/or sell copies of the Software, and to permit persons to whom the
%% Software is furnished to do so, subject to the following conditions:

%% The above copyright notice and this permission notice shall be included in
%% all copies or substantial portions of the Software.

%% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
%% IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
%% FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
%% THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
%% LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
%% FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
%% DEALINGS IN THE SOFTWARE.

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
              no_whistling = sets:new(),
              %% The gensym'd names for stdfuns().
              libnames = dict:new()
             }).

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

-ifdef(LOG).
-define(DEBUG(P,A), (io:fwrite(P,A))).
-else.
-define(DEBUG(P,A), (false)).
-endif.
