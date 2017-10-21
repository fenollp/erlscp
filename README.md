# erlscp [![TravisCI build status](https://travis-ci.org/fenollp/erlscp.svg?branch=master)](https://travis-ci.org/fenollp/erlscp/builds) [![Coverage Status](https://coveralls.io/repos/github/fenollp/erlscp/badge.svg?branch=master)](https://coveralls.io/github/fenollp/erlscp?branch=master)

A supercompiler pass for Erlang. Brought back from the ashes by pierrefenoll@gmail.com.

### Example

Inlines [inline0.erl](test/asm_data/inline0.hrl)'s `a/0` into `b/0`:

```erlang
-module(inline0).
-export([a/0, b/0]).

a() ->
    {N,_} = a1(0),
    N.

a1(N) -> {N,N}.

b() -> 0.
```

```shell
$ rebar3 escriptize
$ ./superlc -S inline0.erl
...
$ cat inline0.S
...
{function, a, 0, 2}.
  {label,1}.
    {line,[{location,"inline0.erl",5}]}.
    {func_info,{atom,inline0},{atom,a},0}.
  {label,2}.
    {move,{integer,0},{x,0}}.  %% <--- a() got compiled into a() -> 0.
    return.
...
```

## Extracts of conversations with @weinholt

In case you want to spend some time fixing the last few issues...

### Incomplete matching support

```
> I notice your implementation of the inline foldl uses case instead of
> function clauses. I'm guessing this has to do with the incomplete
> matching support?

Yeah, that's exactly it. I think I mentioned it in the thesis, that I
should've implemented unification instead of what I did.
```

### Should use erl_syntax modules

```
Something I can say in general about the code base, is that erl_syntax
and erl_syntax_lib has a lot of useful utilities that I should've used
more throughout the code. I'm sure that an Erlang module somewhere
already implements alpha conversion, since it's such a common thing to
do in a compiler. If so, it should be used instead of erlscp's own ac
function.
```

### Make blocks more like lets

```
> The one test that has me worried is
> https://github.com/fenollp/erlscp/blob/b2a61cf40aeee1fb9be674bcda0e441d782852a4/test/asm_tests.erl#L41
> The tested code is
> https://github.com/fenollp/erlscp/blob/b2a61cf40aeee1fb9be674bcda0e441d782852a4/test/asm_data/unfold4.hrl#L13
> It fails with the compiler complaining that "S" in unbound. I'm not sure
> where to start looking on that one...

I had a look at the "S" bug in unfold4 and think I've traced it to the
"let" rule R7/R8/R9 (renamed S to State to make it easier to search
for):

| R7/R8/R9
| let!!!
|  Lhs='State@7' Rhs={tuple,7,[{atom,7,some},{string,7,"state"}]}
|  Body={match,8,
|              {var,8,'Fs@527'},
|              {cons,8,
|                    {'fun',8,{function,two,2}},
|                    {cons,8,
|                          {'fun',9,{function,three,2}},
|                          {cons,8,
|                                {'fun',10,{function,five,2}},
|                                {cons,8,
|                                      {'fun',11,{function,'TWO',2}},
|                                      {nil,8}}}}}}
| no residual let.

As you can see, it believes this to be a let where Lhs doesn't appear
anywhere in Body. But in actuality Lhs appears in a block right next to
the whole expression. I don't have time to fix it myself right now, but
I can say the fix would probably be to adjust scp_expr:make_block/3.
There's already a TODO:

| %% From Oscar Waddell's dissertation. The return expression for whole
| %% the block becomes the second expression of the block.
|
| %% TODO: this should instead create a structure where matches in E1
| %% become structured like let.
| make_block(L0, E1, E2) ->
|     case is_simple(E1) of
|         true -> E2;
|         false ->
|             E1n = case E1 of
|                       {block,_,[E1a,E1b]} ->
|                           case is_simple(E1b) of
|                               true -> E1a;
|                               _ -> E1
|                           end;
|                       _ -> E1
|                   end,
|             case E2 of
|                 {block,L1,[E3,E4]} ->
|                     {block,L1,[{block,L0,[E1n,E3]},E4]};
|                 _ ->
|                     {block,L0,[E1n,E2]}
|             end
|     end.

So the make_block/3 you see here is from Oscar Waddell's Ph.D.
dissertation, which was about the partial evaluator cp0 from Chez
Scheme. It had a useful property in that optimizer, but I'm pretty sure
that I never got any use of this property in erlscp.

The TODO is about making the blocks match the structure of a let. In
Erlang there is no let expression, but we can pretend that "begin X = Y,
expr end." is a simple let expression binding one variable X to Y in
expr. So an improved make_block/3 would structure the blocks so that
matches always end up as the first expression of a block, and the second
expression is the expression where the new variables are visible.

I have a suspicion that it will not be enough to check if E1 is a match
expression. One might also need to check inside E2 to see if there is
a new level of blocks where there is a match that should be pulled out.
Something like "begin begin X = Y, Y end, Y end" where the nested X = Y
should be pulled out to the top level. Not sure if it's a problem in
practice, but the point is to not let the drive function see what it
thinks is a let expression, where the Lhs is actually used outside of
the second expression.
```


## Original README by @weinholt

-*- coding: utf-8-with-signature; mode: outline -*-

Copyright (C) 2013 Göran Weinholt <goran@weinholt.se>

* What erlscp is and what it is used for

The Erlang Supercompiler (erlscp for short) is a parse transform that
is capable of removing many redundancies in Erlang code. It can
optimise code but it also has many other metacomputational uses that
have not been fully explored in the context of this project.

Those interested in the algorithm may peruse these publications:

  Peter A. Jonsson and Johan Nordlander. Positive supercompilation for
  a higher order call-by-value language. In /Proceedings of the 36th
  annual ACM SIGPLAN-SIGACT symposium on Principles of programming
  languages/, POPL '09, pages 277--288, New York, NY, USA, 2009. ACM.

  Peter A. Jonsson and Johan Nordlander. Strengthening
  supercompilation for call-by-value languages. In Andrei P. Nemytykh,
  editor, /Proceedings of the second International Valentin Turchin
  Memorial Workshop on Metacomputation in Russia/, pages 64--81.
  Ailamazyan University of Pereslavl, July 2010.

  Peter A. Jonsson and Johan Nordlander. Taming code explosion in
  supercompilation. In /Proceedings of the 20th ACM SIGPLAN workshop
  on Partial evaluation and program manipulation/, PEPM '11, pages
  33--42, New York, NY, USA, 2011. ACM.

  Peter A. Jonsson. /Time- and Size-Efficient Supercompilation/. PhD
  thesis, Luleå University of Technology, Luleå Sweden, 2011.

  Göran Weinholt. /Supercompiling Erlang/. Master's thesis, Chalmers
  University of Technology, Gothenburg, 2013.

* Before you use erlscp

Before using erlscp you will need to have Erlang installed. The only
version that has been tested is Erlang R15B01. Another requirement is
erlang-syntax-tools.

Currently erlscp does not support the full Erlang language. The
treatment of patterns is simplistic and support for some expression
types is missing. You may need to read the supercompiler output to
determine if the code got better.

Something will happen if the supercompiled module contains
side-effects such as message passing, and it will probably not be
something good.

* How to use erlscp

(There is probably some nice way of packaging Erlang modules so that
this stuff is easier, but that is for the future.)

Obtain a copy of erlscp from this website:

  http://weinholt.se/gitweb/?p=erlscp.git

A tarball can be obtained from this URL:

  http://weinholt.se/gitweb/?p=erlscp.git;a=snapshot;h=HEAD;sf=tgz

The source code repository can be cloned with this command:

  git clone http://weinholt.se/git/erlscp.git/

Compile erlscp using make (which might need to be GNU make). This will
produce a few .beam files in the ebin directory. This is the directory
that you need to add to Erlang's path.

Add this line to the Erlang module that you want to supercompile:

-compile({parse_transform, erlang_supercompiler}).

Then you can invoke the Erlang compiler as per usual, but make sure
that you have added the ebin directory to its path (e.g. by invoking
erlc with the flags -pa path/to/erlscp/ebin).

tl;dr:
  git clone http://weinholt.se/git/erlscp.git/
  cd erlscp
  make
  cat > foo.erl << EOF
-module(foo).
-export([append/3]).
-compile({parse_transform, erlang_supercompiler}).
append(Xs, Ys, Zs) ->
  (Xs ++ Ys) ++ Zs.
EOF
  erlc -pa ebin foo.erl
  erlc -P -pa ebin foo.erl
  less foo.P

* Possible side-effects

Due to incomplete handling of pattern matching it is currently
possible for the supercompiler to introduce allocations of tuples.

The supercompiler has not been tamed and code explosion is possible.

If the second or higher Futamura projections are used then the
supercompiler output is a derivative of erlscp. This means that the
license in LICENSE.txt is applicable to the supercompiled program.
This only applies to when the supercompiler is applied to itself (as
in the Futamura projections mentioned). Merely using erlscp for
optimisations does not make the output a derivative of erlscp.

Not that the Futamura projections can be used with erlscp yet, but,
you know, just in case that day ever comes. A man can dream.

* How to properly store erlscp

Store on a digital medium and outside the reach of children. Dispose
of in the bitbucket. Patches are submitted to the author by email.

* Other information

This README was modelled after an informational paper slip that came
in a package of medicine. I've left out the parts about pregnancy and
heavy machinery.
