:tocdepth: 2

.. highlight:: c

.. _hard_limits:

Hard-coded Limits
=================

The internal data representation used by Yices imposes various limits
on the size of the term and type table, and on the size of composite
terms. Macros defined in header file :file:`yices_limits.h` specify
these limits. These are mostly theoretical limits, and should be
beyond what Yices can actually store and process.

.. c:macro:: YICES_MAX_TYPES

   Maximal number of types that can be stored in Yices's internal type
   table. This limit is more than 500 millions [#f1]_::

     #define YICES_MAX_TYPES (UINT32_MAX/8)

.. c:macro:: YICES_MAX_TERMS

   Maximal number of terms that can be stored in Yices's internal term table.
   This limit has the same value as :c:macro:`YICES_MAX_TYPES`::

     #define YICES_MAX_TERMS (UINT32_MAX/8)

.. c:macro:: YICES_MAX_ARITY

   Maximal number of arguments in a function or tuple type. This also the maximal
   number of arguments that the N-ary term constructors can take::

     #define YICES_MAX_ARITY (UINT32_MAX/16)

.. c:macro:: YICES_MAX_DEGREE

    Maximal degree of arithmetic and bitvector polynomials::

      #define YICES_MAX_DEGREE (UINT32_MAX/2)

.. c:macro:: YICES_MAX_VARS

   Maximal number of variables in quantifiers and lambda terms::
   
      #define YICES_MAX_VARS (UINT32_MAX/16)

.. c:macro:: YICES_MAX_BVSIZE

   Maximal size of a bitvector types and terms::

     #define YICES_MAX_BVSIZE (UINT32_MAX/16)


.. rubric:: Footnotes:

.. [#f1] Constant :c:macro:`UINT32_MAX` is equal to 4294967295 (i.e., 2^32 -1).
