.. highlight:: c

Overview
========

The Yices API is defined in three header files:

  - :file:`yices.h` declares all functions and constants
  - :file:`yices_types.h` defines the types and data structures used in the API
  - :file:`yices_limits.h` defines hard-coded limits

For a standard installation of Yices, these files are in director :file:`/usr/local/include`.

To use the APi, you shoud add::

  #include <yices.h>

in your code, and link with the Yices library using option ``-lyices``.

Several functions in the API take GMP numbers (e.g., ``mpq_t`` or ``mpz_t``)
as arguments. To use these functions, make sure to include the GMP header
first, *before* you include ``yices.h``::

  #include <gmp.h>
  #include <yices>

.. note:: Yices requires the C99 header ``<stdint.h>``.
   This C99 header may not be available on old versions of Microsoft's Visual
   Studio. If it is missing, open-source versions of :file:`stdint.h` can be 
   downloaded at

   - https://code.google.com/p/msinttypes (for Visual Studio only)
   - http://www.azillionmonkeys.com/qed/pstdint.h

   A copy of the latter file is included in the Yices distributions (in
   :file:`etc/pstdint.h`).


Minimal Example
---------------

Here is a minimal example::

   #include <stdio.h>
   #include <yices.h>

   int main(void) {
      printf("Testing Yices %s (%s, %s)\n", yices_version,
              yices_build_arch, yices_build_mode);
      return 0;
   }

Assuming that Yices is installed in the standard location, this example
should compile with::

  gcc minimal.c -o minimal -lyices

Other compilers than GCC can be used. If Yices is installed in a different
location, give appropriate flags to the compilation command. For example::

  gcc -I${HOME}/yices-2.3.0/include -L${HOME}/yices-2.3.0/lib minimal.c -o minimal -lyices

Running the program shoud print something like this::

  Testing Yices 2.3.0 (x86_64-unknown-linux-gnu, release)

You may need to play with environment variable ``LD_LIBRARY_PATH`` (or
``DYLD_LIBRARY_PATH`` on Mac OS X) if the runtime Yices library is not
found.
