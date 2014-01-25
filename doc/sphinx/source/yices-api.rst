Yices API
=========

.. highlight:: c

Header Files
------------

The API is defined in header files :file:`yices.h`, :file:`yices_types.h`,
and :file:`yices_limits.h`. To use the API, it is sufficient to
include ``yices.h`` in your code::

   #include "yices.h"

This also includes ``yices_types.h`` and ``yices_limits.h``

File :file:`yices_types.h` defines the basic types used by the API.
This includes the types for representing Yices terms and types, and
the other data structures manipulated by Yices.  File
:file:`yices_limits.h` contains macro definitions to specify
hard-coded limits such as maximal term arity, maximal size of a
bitvector type, and so forth.



Types
-----

The following types and macros are defined in :file:`yices_types.h`

.. c:type:: type_t

   An object of type :c:type:`type_t` denotes a Yices type. The type
   is defined as follows::

      typedef int32_t type_t;

   In Yices, a type is identified by an integer index of type
   :c:type:`type_t`.  Such an index denotes a type descriptor that is
   stored in an internal type table.

.. c:macro:: NULL_TYPE

   All type constructors return an index of type :c:type:`type_t`. If
   a constructor fails, it returns the special constant
   :c:macro:`NULL_TYPE` defined by::

      #define NULL_TYPE -1

   More information about the error can be obtained by examining Yices
   :c:type:`error_report_t` structure or error-diagnostic functions of
   the API.

.. c:type:: term_t

   An object ot type :c:type:`term_t` denotes a Yices term. The type
   is defined as::

      typedef int32_t term_t;

   Like types, all terms in Yices are stored in an internal term table,
   and a :c:type:`term_t` is an index in this table.

.. c:macro:: NULL_TERM

   The special value :c:macro:`NULL_TERM` is returned by term
   constructors to report an error. It is defined by::

      #define NULL_TERM -1

   If a term constructor succeeds, it returns a non-negative term
   index.

.. c:type:: context_t

   A :c:type:`context_t` is a data structure internal to Yices that
   represent a context. A context stores a set of assertions, and
   includes one or more solvers to check satisfiability of these
   assertions. API functions are available for creating a
   :c:type:`context_t`, adding and possibly retracting assertions,
   checking satisfiability, and constructing a :c:type:`model_t`.

.. c:type:: model_t

   A :c:type:`model_t` stores a mapping from uninterpreted terms to
   concrete values such as Boolean or bitvector constants, rationals,
   and integers, and more complex values such as tuples or mappings.

.. c:type:: error_report_t

   Yices maintains a global structure that stores information about
   possible errors (such as passing incorrect arguments to an API
   function). The error report stores an error code and additional
   information that can be used to diagnose incorrect operations.
   The list of all error codes is defined in :file:`yices_types.h`.

.. c:type:: ctx_config_t

   This type denotes an opaque data structure that can be used to
   configure the set of solvers present in a context, and the set of
   features supported by a context.

.. c:type:: param_t

   A :c:type:`param_t` structure stores heuristic parameters used by
   solvers. Several functions are available to allocate such a
   parameter structure, and set the value of all parameters.


Version Numbers
---------------

The following macros, defined in :file:`yices.h` encode the version of
the Yices library.

.. c:macro:: __YICES_VERSION
.. c:macro:: __YICES_VERSION_MAJOR
.. c:macro:: __YICES_VERSION_PATCHLEVEL

These three macros define the Yices release. For example, for
Yice 2.2.0, the macros are as follows::

  #define __YICES_VERSION            2
  #define __YICES_VERSION_MAJOR      2
  #define __YICES_VERSION_PATCHLEVEL 0

The version is also available as a constant string.

.. c:var:: const char *yices_version

This character string stores the version in the format such as "2.2.0"

For example, this piece of code prints the Yices version on ``stdout``::

   #include <stdio.h>
   #include <yices.h>

   int main(void) {
     printf("Yices version: %s\n", yices_version);
     return 0;
   }


One can obtain more details about a specific release via the following
character strings.

.. c:var:: const char *yices_build_arch

This stores the architecture on which the Yices release was built, in
a format such as ``"x86_64-unknown-linux-gnu"``.

.. c:var:: const char *yices_build_mode

The build mode can be either ``"release"`` or ``"debug"``. If Yices is
linked statically against GMP, the :c:data:`yices_build_mode` is either
``"release/static"`` or ``"debug/static"``.

.. c:var:: const char *yices_build_date

This strings stores the date on which the release was built, in the format
``"Year-month-day"`` (e.g., ``"2014-01-24"`` for January 24, 2014).


Functions
---------

.. c:function:: void yices_init(void)

   Initialize all internal data structures. This function must be called
   before any other API function.

.. c:function:: void yices_exit(void)

   Delete all internal data structures and allocated objects. This
   must be called to avoid memory leaks.

.. c:function:: void yices_reset(void)

   Full reset: delete all terms and types, and reset the symbol tables.
   Delete all contexts, modesl, configuration descriptors, and
   parameter records.
