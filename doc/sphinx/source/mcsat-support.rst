:tocdepth: 2

.. highlight:: c

.. _mcsat_support:

MCSAT Support
=============

The MCSAT solver is an optional component of Yices that requires
the `libpoly <https://github.com/SRI-CSL/libpoly>`_ library.
The MCSAT solver is necessary if you want Yices to handle non-linear
arithmetic constraints.

Some functions in the Yices API convert real values to the
algebraic-number representation used by libpoly (structures of type
``lp_algebraic_number_t``).  To use these functions, you must first 
make sure that Yices is compiled with MCSAT support. You must also 
install libpoly and include the appropriate header in you code
as follows::

   #include <poly/algebraic_number.h>
   #include <yices.h>

It is important to include ``poly/algebraic_number.h`` *before* ``yices.h``.

File :file:`examples/example_mcsat.c` included in the distribution
shows how to use these functions and how to solve a simple problem in
non-linear arithmetic.


.. c:function:: int32_t yices_has_mcsat(void)

   Check whether the Yices library was compiled with MCSAT support.

   This function indicates whether the Yices library you are linking
   against was built with MCSAT support. It returns 1 for Yes and 0 for No.

