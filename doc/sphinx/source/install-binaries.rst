:tocdepth: 2

.. highlight:: c


Binary Distributions
====================

You can install Yices 2 with homebrew on Mac OS X or with apt on
Debian-based Linux systems. You can also download precompiled binary
distributions at https://yices.csl.sri.com.

Package Managers
................

On Ubuntu/Debian:

.. code-block:: sh

   sudo add-apt-repository ppa:sri-csl/formal-methods
   sudo apt-get update
   sudo apt-get install yices2


On Mac OS X:

.. code-block:: sh

   brew install SRI-CSL/sri-csl/yices2


Archives (tar or zip files)
...........................

You can download binary distributions for Linux, Mac OS X, and Windows
at https://yices.csl.sri.com. These distributions contain pre-compiled
binaries and libraries, linked statically against GMP and
libpoly. They include support for nonlinear arithmetic and MCSAT.

The binary distributions for Linux and Mac OS X include a shell script
to install the binaries, headers, and library in
:file:`/usr/local`. You can run this script as follows:

.. code-block:: sh

   sudo ./install-yices

If you want a different installation directory, type

.. code-block:: sh

   ./install-yices <directory>

(use *sudo* if necessary).


