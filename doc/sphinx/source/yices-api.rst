Yices API
=========

Header Files
------------

The API is defined in header files :file:`yices.h`, :file:`yices_types.h`,
and :file:`yices_limits.h`. To use the API, it is sufficient to
include ``yices.h`` in your code::

   #include "yices.h"

This also includes ``yices_types.h`` and ``yices_limits.h``

File :file:`yices_types.h` defines the basic types used by the API.
This includes the types for representing Yices terms and types,
and the other data structures manipulated by Yices.

File :file:`yices_limits.h` contains macro definitions to specify
hard-coded limits such as maximal term arity, maximal size of a
bitvector type, and so forth.



Types
-----

The following types are defined in :file:`yices_types.h`

.. c:type:: term_t

.. c:type:: type_t

.. c:type:: context_t

.. c:type:: model_t

.. c:type:: param_t

.. c:type:: error_report_t
   

Macros
------

The following macros are defined in :file:`yices.h`

.. c:macro:: __YICES_VERSION
.. c:macro:: __YICES_VERSION_MAJOR
.. c:macro:: __YICES_VERSION_PATCHLEVEL

These three macros define the Yices release. For example, for 
Yice 2.1.1, the macros are defined as follows::

  #define __YICES_VERSION            2
  #define __YICES_VERSION_MAJOR      1
  #define __YICES_VERSION_PATCHLEVEL 1

The version is also available as a constant string

  

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