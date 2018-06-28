:tocdepth: 2

.. highlight:: c


Building Yices from Source
==========================

The source for the latest release is at http://yices.csl.sri.com.  If
you prefer, you can clone our `GitHub
<https://github.com/SRI-CSL/yices2.git>`_ repository:

.. code-block:: sh

   git clone https://github.com/SRI-CSL/yices2.git


Dependencies
............

To build Yices, you need a C compiler that supports C99. Any
reasonably recent version of GCC or Clang should work.


You also need the `GNU Multiple Precision <http://gmplib.org>`_
library (GMP) and the `gperf <http://www.gnu.org/software/gperf>`_
utility. 

If you cloned the GitHub repository, you will also need 
`autoconf <https://www.gnu.org/software/autoconf/autoconf.html>`_.


MCSAT and Nonlinear Arithmetic
..............................

Yices includes a solver for nonlinear arithmetic based on the Model
Constructing Satisfiability Calculus (MCSAT). This solver depends on
an external library for manipulating polynomials. If you need
nonlinear arithmetic, you must install this library first. Get it from
our `GitHub repository <https://github.com/SRI-CSL/libpoly>`_ and
follow the build instructions there.  Make sure to get the latest
libpoly release (v0.1.3).


Installing from the Source
..........................

If you got the source tarfiles at http://yices.csl.sri.com, and you
have installed GMP and gperf, then building Yices is straightforward.

.. code-block:: sh

   ./configure
   make -j
   sudo make install

This installs the binaries in :file:`/usr/local/bin`, the header files
in :file:`/usr/local/include`, and the library in
:file:`/usr/local/lib`. You can change the installation location by
giving the option ``--prefix=<directory>`` to the
``configure`` script.


If you also want support for MCSAT:

.. code-block:: sh

   ./configure --enable-mcsat
   make -j
   sudo make install

You may need to set CPPFLAGS and LDFLAGS if the libpoly library is not
in a standard location.

If you cloned the source from our Git repository, you need to run autoconf
first:

.. code-block:: sh

   autoconf
   ./configure
   make -j
   sudo make install

or

.. code-block:: sh

   autoconf
   ./configure --enable-mcsat
   make -j
   sudo make install


For a detailed explanation of the build process and options, check the
file :file:`doc/COMPILING` included in the distribution.
