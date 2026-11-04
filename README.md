[![License: BSD 3-Clause](https://img.shields.io/badge/License-BSD_3--Clause-blue.svg)](LICENSE.txt)
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

## License

The Yices source is distributed under the
[BSD 3-Clause License](LICENSE.txt). Earlier releases remain available
under the license that accompanied each release.

Yices 2 is developed by Bruno Dutertre, Dejan Jovanovic, Stéphane Graham-Lengrand, Ian A. Mason, and Ahmed Irfan
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

## Parallel Yices Example

Yices can be run in parallel using a portfolio approach, which launches several instances of `yices_smt2` with different configurations and returns as soon as one instance finds a solution. This is useful for hard SMT problems where different configurations may solve the problem faster.

A Python script is provided in `utils/yices2_parallel.py` for this purpose. Example usage:

```sh
python3 utils/yices2_parallel.py --yices /path/to/yices_smt2 -n 4 --verbose path/to/problem.smt2
```

- `--yices` specifies the path to the `yices_smt2` executable (default: `yices_smt2` in the script directory)
- `-n` sets the number of parallel threads/configurations (default: 4)
- `--verbose` enables detailed output
- The last argument is the path to your SMT2 file

The script will run several Yices instances in parallel and print the result (`sat`, `unsat`, or `unknown`) as soon as one instance finishes.

For more options, run:

```sh
python3 utils/yices2_parallel.py --help
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

We provide APT packages for Ubuntu through a Launchpad PPA:
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

The PPA provides packages for Ubuntu 22.04 (Jammy) on amd64. It may lag the
current release. Check with `apt-cache policy yices2`. For the current
release, use the binary distributions at https://yices.csl.sri.com or build
from source.


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

The API documentation in the Git checkout requires Python 3.8 or later
and a compatible Sphinx installation, at least version 1.8. Use an isolated
Python environment with the Sphinx distribution metadata and license intact.
See [doc/sphinx/README.md](doc/sphinx/README.md) in that checkout for the build
and notice-delivery requirements. Compatibility with every older version
combination is not implied.


#### Quick Installation

Choose a fresh installation directory that you own, using an absolute path
without whitespace. Check that `$HOME/local/yices-2.8.0` does not already
exist; if it does, choose another unused path in the command below:

```
autoconf
./configure --prefix="$HOME/local/yices-2.8.0"
make
make install
```

This installs binaries, libraries and headers under the chosen prefix,
without `sudo`. `LICENSE` and `NOTICES` go in `share/doc/yices-2.8.0` under
that prefix, and license texts go in `share/licenses/yices-2.8.0`. Add the
prefix's `bin` directory to `PATH` or invoke the binaries by their full paths.

Warning: `make install` has no existing-installation check and can overwrite
Yices files without prompting. Unlike `install-yices` in the prebuilt binary
archives, it does not refuse an existing Yices installation. Reusing a
prefix can replace binaries, libraries, headers and other installed files.
If `--prefix` is omitted, the default is `/usr/local`. Install into a shared
prefix with elevated privileges only when you intend to replace its Yices
files and have backed up anything you need to retain.

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
   the toplevel Yices directory. Choose a fresh prefix for this variant
   too; the same overwrite warning applies:

```
autoconf
./configure --prefix="$HOME/local/yices-2.8.0-mcsat" \
            --enable-mcsat
make
make install
```

3. You may need to provide `LDFLAGS/CPPFLAGS` if `./configure` fails to
  find the libpoly or CUDD libraries. Other options may be useful too.  Try
  `./configure --help` to see what's there.


#### Support for Thread Safety

The Yices library is not thread safe by default. If you need a re-entrant
version, choose a fresh prefix for it, subject to the overwrite warning above:

```
autoconf
./configure --prefix="$HOME/local/yices-2.8.0-threadsafe" \
            --enable-thread-safety
make
make install
```

If configured with `--enable-thread-safety` the Yices library will be thread
safe in the following sense: as long as the creation and manipulation of
each context and each model is restricted to a single thread, there should be no races.
In particular separate threads can create their own contexts, and manipulate and check
them without impeding another thread's progress.

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

- `doc/COMPILING`
