[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)
[![CI](https://github.com/SRI-CSL/yices2/actions/workflows/ci.yml/badge.svg)](https://github.com/SRI-CSL/yices2/actions/workflows/ci.yml)
[![Coverity Scan Build Status](https://scan.coverity.com/projects/12768/badge.svg)](https://scan.coverity.com/projects/sri-csl-yices2)
[![Coverage Status](https://coveralls.io/repos/github/SRI-CSL/yices2/badge.svg?branch=master)](https://coveralls.io/github/SRI-CSL/yices2?branch=master)

<img width="100" style="display: block; margin: auto;" src="https://avatars.githubusercontent.com/u/8029212"/>

# SRI Yices 2

SRI Yices 2 is a solver for [Satisfiability Modulo
Theories](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories)
(SMT) problems. Yices 2 can process input written in the SMT-LIB language, or in Yices' own specification language.
We also provide a [C API](https://github.com/SRI-CSL/yices2/blob/master/src/include/yices.h) 
and bindings for [Java](https://github.com/SRI-CSL/yices2_java_bindings), [Python](https://github.com/SRI-CSL/yices2_python_bindings), [Go](https://github.com/SRI-CSL/yices2_go_bindings), and [OCaml](https://github.com/SRI-CSL/yices2_ocaml_bindings).

This repository includes the source of Yices 2, documentation, tests,
and examples.

Yices 2 is developed by Bruno Dutertre, Dejan Jovanovic, Stéphane Graham-Lengrand, and Ian A. Mason
at the Computer Science Laboratory, SRI International. To contact us,
or to get more information about Yices, please visit our
[website](https://yices.csl.sri.com).

## Simple Examples

Here are a few typical small examples that illustrate 
the use of Yices using the [SMT2 language](http://smtlib.cs.uiowa.edu/language.shtml).

#### Linear Real Arithmetic

```smt2
;; QF_LRA = Quantifier-Free Linear Real Arithmetic
(set-logic QF_LRA)
;; Declare variables x, y
(declare-fun x () Real)
(declare-fun y () Real)
;; Find solution to (x + y > 0), ((x < 0) || (y < 0))
(assert (> (+ x y) 0))
(assert (or (< x 0) (< y 0)))
;; Run a satisfiability check
(check-sat)
;; Print the model
(get-model)
```

Running Yices on the above problem gives a solution
```
> yices-smt2 lra.smt2
sat
((define-fun x () Real 2.0)
 (define-fun y () Real (- 1.0)))
```

#### Bit-Vectors

```smt2
;; QF_BV = Quantifier-Free Bit-Vectors
(set-logic QF_BV)
;; Declare variables
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
;; Find solution to (signed) x > 0, y > 0, x + y < x
(assert (bvsgt x #x00000000))
(assert (bvsgt y #x00000000))
(assert (bvslt (bvadd x y) x))
;; Check
(check-sat)
;; Get the model
(get-model)
```

Running Yices on the above problem gives

```
> yices-smt2 bv.smt2
sat
((define-fun x () (_ BitVec 32) #b01000000000000000000000000000000)
 (define-fun y () (_ BitVec 32) #b01000000000000000000000000000000))
```

#### Non-Linear Arithmetic

```smt2
;; QF_NRA = Quantifier-Free Nonlinear Real Arithmetic
(set-logic QF_NRA)
;; Declare variables
(declare-fun x () Real)
(declare-fun y () Real)
;; Find solution to x^2 + y^2 = 1, x = 2*y, x > 0
(assert (= (+ (* x x) (* y y)) 1))
(assert (= x (* 2 y)))
(assert (> x 0))
;; Check
(check-sat)
;; Get the model
(get-model)
```

Running Yices on the above problem gives

```
sat
((define-fun x () Real 0.894427)
 (define-fun y () Real 0.447214))
```

## Installing Prebuilt Binaries

Currently you can install Yices either using Homebrew or Apt.

#### Homebrew

Installing on Darwin using homebrew can be achieved via:
```
brew install SRI-CSL/sri-csl/yices2
```
This will install the full mcsat-enabled version of Yices, including dynamic library and header files.


#### Apt

To install Yices on Ubuntu or Debian, do the following:
```
sudo add-apt-repository ppa:sri-csl/formal-methods
sudo apt-get update
sudo apt-get install yices2
```
This will install the executables. If you also need the Yices library and header files, replace
the last step with:
```
sudo apt-get install yices2-dev
```


## Building From Source

#### Prerequisites

To build Yices from the source, you need:

- GCC version 4.0.x or newer (or clang 3.0 or newer)
- gperf version 3.0 or newer
- the GMP library version 4.1 or newer

+ other standard tools: make (gnumake is required), sed, etc.


To build the manual, you also need:

- a latex installation
- the latexmk tool

To build the on-line documentation, you need to install the Sphinx
python package. The simplest method is:

```
sudo pip install sphinx
```

Sphinx 1.4.x or better is needed.


#### Quick Installation

Do this:

```
autoconf
./configure
make
sudo make install
```

This will install binaries and libraries in `/usr/local/`. You can
change the installation location by giving option `--prefix=...` to
the `./configure` script.

For more explanations, please check `doc/COMPILING`.

#### Support for Non-Linear Arithmetic and MC-SAT

Yices supports non-linear real and integer arithmetic using a method
known as *Model-Constructing Satisfiability* (MC-SAT), but this is not
enabled by default. The MC-SAT solver also supports other theories and
theory combination. We are currently extending it to handle bit-vector
constraints.

If you want the MC-SAT solver, follow these instructions:

1. Install SRI's library for polynomial manipulation. It's available
   on [github](https://github.com/SRI-CSL/libpoly).

2. Install the CUDD library for binary-decision diagrams. We recommend
   using the github distribution: https://github.com/ivmai/cudd.

3. After you've installed libpoly and CUDD, add option
   `--enable-mcsat` to the configure command. In details, type this in
   the toplevel Yices directory:

```
autoconf
./configure --enable-mcsat
make
sudo make install
```

3. You may need to provide `LDFLAGS/CPPFLAGS` if `./configure` fails to
  find the libpoly or CUDD libraries. Other options may be useful too.  Try
  `./configure --help` to see what's there.


#### Support for Thread Safety

The Yices library is not thread safe by default, if you need a re-entrant version:
```
autoconf
./configure --enable-thread-safety
make
sudo make install
```

If configured with `--enable-thread-safety` the Yices library will be thread
safe in the following sense: as long as the creation and manipulation of
each context and each model is restricted to a single thread, there should be no races.
In particular separate threads can create their own contexts, and manipulate and check
them without impeding another thread's progress.

NOTE: `--enable-mcsat` and `--enable-thread-safety` are currently incompatible.

#### Windows Builds

We recommend compiling using Cygwin. If you want a version that works
natively on Windows (i.e., does not depend on the Cygwin DLLs), you
can compile from Cygwin using the MinGW cross-compilers. This is
explained in doc/COMPILING.


#### Documentation

To build the manual from the source, type
```
make doc
```
This will build `./doc/manual/manual.pdf`.

Other documentation is in the `./doc` directory:

- `doc/COMPILING` explains the compilation process and options in detail.
- `doc/NOTES` gives an overview of the source code.
- `doc/YICES-LANGUAGE` explains the syntax of the Yices language, and
  describes commands, functions, and heuristic parameters.

To build the Sphinx documentation:
```
cd doc/sphinx
make html
```

This will build the documentation in build/html (within directory
doc/sphinx). You can also do:
```
make epub
```
and you'll have the doc in `build/epub/Yices.epub`.

## Getting Help and Reporting bugs

For further questions about Yices, please contact us via the Yices
mailing lists yices-help@csl.sri.com. This mailing list is moderated,
but you do not need to register to post to it. You can register to
this mailing list if you are interested in helping others.

Please submit bug reports through GitHub issues. Please include enough
information in your bug report to enable us to reproduce and fix the
problem. This is an example of a good report:

> I am experiencing a segmentation fault from Yices. The following
> is a small test case that causes the crash. I am using Yices 2.4.1 on
> x86_64 statically linked against GMP on Ubuntu 12.04.

This is an example of a poor bug report:

> I have just downloaded Yices. After I compile my code and link it
> with Yices, there is a segmentation fault when I run the executable.
> Can you help?

Please try to include answers to the following questions:
* Which version of Yices are you using?
* On which hardware and OS?
* How can we reproduce the bug? If possible, include an input file or program fragment.
