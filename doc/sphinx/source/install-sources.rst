:tocdepth: 2

.. highlight:: c


Building Yices from Source
==========================

The source for the latest release is at https://yices.csl.sri.com.  If
you prefer, you can clone our `GitHub
<https://github.com/SRI-CSL/yices2.git>`_ repository:

.. code-block:: sh

   git clone https://github.com/SRI-CSL/yices2.git

You can choose between different compile-time features and optional components:

1. Support for the MCSAT solver (necessary for non-linear arithmetic).

2. Support for back-end Boolean SAT solvers (which can provide performance
   improvements on bit-vector problems).

3. Build a thread-safe version of the Yices library.

The following build instructions are written for Ubuntu but they should work
with minor adjustments on other Unix variants. For Windows, we recommand
compiling using Cygwin or with the MinGW cross-compilers.


Common Dependencies
-------------------

No matter which variant you want to build, you need a C compiler that
supports C99. Any reasonably recent version of GCC or Clang should
work. You will also need standard build tools such as ``GNU Make`` and ``sed``.

You also need the `GNU Multiple Precision <http://gmplib.org>`_
library (GMP) and the `gperf <http://www.gnu.org/software/gperf>`_
utility.

If you cloned the GitHub repository, you will also need 
`autoconf <https://www.gnu.org/software/autoconf/autoconf.html>`_.


Basic Build
-----------

The simplest type of build does not include MCSAT or third-party SAT solvers.
Start by installing the dependencies:

.. code-block:: sh

   sudo apt-get install libgmp-dev
   sudo apt-get install gperf


Build from a source tarfile
...........................

If you donwloaded the source tarfile from https://yices.csl.sri.com, you can
configure and build Yices as follows:

.. code-block:: sh

   ./configure
   make -j
   sudo make install

This installs the binaries in :file:`/usr/local/bin`, the header files
in :file:`/usr/local/include`, and the library in
:file:`/usr/local/lib`. You can change the installation location by
giving the option ``--prefix=<directory>`` to the
``configure`` script.


Build from a clone of our Git repository
........................................

If you got the source from our `GitHub
<https://github.com/SRI-CSL/yices2.git>`_ repository, the build process is almost
the same as from a tarfile. Make sure ``autoconf`` is installed:

.. code-block:: sh

   sudo apt-get install autoconf


Then build Yices as follows:

.. code-block:: sh

   autoconf
   ./configure
   make -j
   sudo make install


Running the tests
.................

Optionally, you can check that the build was fine by using

.. code-block:: sh

   make -j check

This will run the Yices regression tests.




MCSAT Support
-------------

The MCSAT solver has two more dependencies:

1. The LibPoly library for manipulating polynomials.

2. The CUDD libray for Binary Decision Diagrams.

Install LibPoly
...............

Get LibPoly from our `GitHub repository <https://github.com/SRI-CSL/libpoly>`_ 
and follow the build instructions there.  Make sure to get the latest
LibPoly release.

Install CUDD
............

We recommend clone the CUDD Git repository from https://github.com/ivmai/cudd
CUDD must be built as Position-Independent Code (i.e., with option ``-fPIC``) to be linked 
with Yices.

Here is how you can build CUDD:

.. code-block:: sh

   git clone https://github.com/ivmai/cudd
   cd cudd
   ./configure CFLAGS=-fPIC
   make
   sudo make install

This will install CUDD header files and libraries in /usr/local.

.. note::

   The CUDD Makefile was created with ``automake-1.14``. Compilation may
   fail if you have a different version of ``automake`` with a complaint
   like ``WARNING ’automake-1.14’ is missing on your system``. If this
   happens to you, try this before you type ``make``

   .. code-block:: sh

      aclocal
      automake


Configure and Build Yices with MCSAT Support
............................................

Once you've installed LibPoly and CUDD, you can build Yices as follows:

.. code-block:: sh

   ./configure --enable-mcsat
   make -j
   sudo make install

You may need to set CPPFLAGS and LDFLAGS if the libpoly library is not
in a standard location.


Third-Party SAT Solvers
-----------------------

Yices can use third-party SAT solvers as backends to the bit-vector
solvers. Currently one internal and three third-party solvers are
supported

1. Internal y2sat SAT solver (default solver)

2. Armin Biere's `CaDiCal <https://github.com/arminbiere/cadical>`_

3. Mate Soos' `CryptoMiniSAT <https://www.msoos.org/cryptominisat5>`_

4. Armin Biere's `Kissat (patched version) <https://github.com/BrunoDutertre/kissat>`_

You can also compile Yices with any of these SAT solvers.

Install CaDiCaL
...............

CaDiCaL must be built with option ``-fPIC`` to work with Yices.  It's
also a good idea to install CaDiCaL in a standard location such as
``/usr/local``.  If you use ``bash``, the following instructions
should do:

.. code-block:: sh

   git clone https://github.com/arminbiere/cadical
   cd cadical
   CXXFLAGS=-fPIC ./configure
   make
   make test
   sudo install build/libcadical.a /usr/local/lib
   sudo install build/cadical build/mobical /usr/local/bin
   sudo install -m644 src/ccadical.h /usr/local/include


Install CryptoMiniSAT
.....................

Yices requires a patched version of CryptoMiniSAT 5 that we provide
at https://github.com/BrunoDutertre/cryptominisat. You may also
need to install CryptoMiniSAT's dependencies:

.. code-block:: sh

   sudo apt-get install cmake zlib1g-dev libboost-program-options-dev


Then you can build and install CryptoMiniSAT as follows:

.. code-block:: sh

   git clone https://github.com/BrunoDutertre/cryptominisat
   cd cryptominisat
   mkdir build
   cd build
   cmake .. -DENABLE_PYTHON_INTERFACE=OFF
   make
   sudo make install

This will install CryptoMiniSAT in ``/usr/local/``.

There are more detailed build instructions in the CryptoMiniSAT ``README``.


Install Kissat
..............

We provide a patched version of Kissat that fixes an issue. Download
this patched version at https://github.com/BrunoDutertre/kissat. The
original is at https://github.com/arminbiere/kissat. To compile the
code, follow these instructions:

.. code-block:: sh

   git clone https://github.com/BrunoDutertre/kissat
   cd kissat
   ./configure -fPIC
   make
   sudo install build/libkissat.a /usr/local/lib
   sudo install -m644 src/kissat.h /usr/local/include


Configure and Build Yices with Third-Party Solvers
..................................................

To build Yices with support for all third-party solvers, use the following
configure command in the top-level yices source directory:

.. code-block:: sh

   ./configure CPPFLAGS='-DHAVE_CADICAL -DHAVE_CRYPTOMINISAT -DHAVE_KISSAT' \
        LIBS='-lcryptominisat5 -lcadical -lkissat -lstdc++ -lm'

This form is for non-static builds. If both CaDiCaL and Kissat are built as
shared libraries, their private ``kitten_*`` symbols must be hidden or
namespaced by the delegate builds. Otherwise the dynamic linker may bind one
solver to the other's incompatible embedded kitten implementation. The Yices
Makefile does not verify this automatically, so raw dynamic targets with both
delegates are rejected by default. If you have validated that both shared
libraries hide ``kitten_*`` while still exporting their public APIs, add
``--enable-dynamic-delegates-assuming-hidden-kitten`` to the configure command. This
option is an assertion about shared libraries; it does not fix raw static
archives.

For a static Yices executable build with both CaDiCaL and Kissat, give
``configure`` the directory that contains the raw static delegate archives and
headers:

.. code-block:: sh

   ./configure CPPFLAGS="-I$DELEGATE_PREFIX/include -DHAVE_CADICAL -DHAVE_CRYPTOMINISAT -DHAVE_KISSAT" \
        LDFLAGS="-L$DELEGATE_PREFIX/lib" \
        LIBS="-lcryptominisat5 -lcadical -lkissat -lstdc++ -lm" \
        --with-static-delegates="$DELEGATE_PREFIX/lib" \
        --with-static-delegates-include-dir="$DELEGATE_PREFIX/include"
   make static-bin

``make static-bin`` generates ``libkissat_yices.a`` under
``$(BUILD)/static_deps`` and links the static executables against this
rewritten archive. The public Kissat API and ``kissat.h`` are unchanged. Do not
use ``-Wl,--allow-multiple-definition`` for this collision: it can silently bind
one solver to the other's incompatible ``kitten_*`` functions.
Do not use a bare ``make`` or ``make all`` for this all-delegate static release
configuration: those targets also build dynamic artifacts, and Yices rejects
raw dynamic CaDiCaL + Kissat builds by default.

If you want only CaDiCaL:

.. code-block:: sh

   ./configure CPPFLAGS=-DHAVE_CADICAL LIBS='-lcadical -lstdc++ -lm'

If you want only CryptoMiniSAT:

.. code-block:: sh

   ./configure CPPFLAGS=-DHAVE_CRYPTOMINISAT LIBS='-lcryptominisat5 -lstdc++'

If you want only Kissat, use this command:

.. code-block:: sh

   ./configure CPPFLAGS=-DHAVE_KISSAT LIBS='-lkissat -lm'

After a non-static configure command that does not use the raw unsafe
CaDiCaL + Kissat combination, you can build Yices as usual:

.. code-block:: sh

   make -j
   sudo make install


.. note::

   These third-party solvers are compatible with MCSAT. So you can add
   the flag ``--enable-mcsat`` to also include support for MCSAT.




Thread-Safe Yices Library
-------------------------

By default, the Yices library is not re-entrant and should not be used in multithreaded applications.
If you need a thread-safe version of the library, configure and build Yices as follows:

.. code-block:: sh

   ./configure --enable-thread-safety
   make -j
   sudo make install

When configured in this way, the Yices library allows multiple threads
to operate on separate contexts and models without causing race
conditions. This is useful to call :c:func:`yices_check_context` on
different contexts in parallel. API functions that create terms and
types are automatically serialized by an internal locking mechanism.

.. note::

   It is not safe for distinct threads to operate on the same context
   or model concurrently. It you want to do that, you have to implement
   your own locking mechanism.


.. note::

   The ``--enable-thread-safety`` and ``--enable-mcsat`` options are
   currently incompatible. It is not possible to build a Yices version
   that is both thread-safe and support MCSAT.
