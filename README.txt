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
