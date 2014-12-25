.. highlight:: c

.. _api_types:

API Types
=========

The following types are defined in :file:`yices_types.h` and are used
by the API.


Yices Types
-----------

.. c:type:: type_t

   The type constructors return objects of type :c:type:`type_t`. This
   type is defined as follows::

      typedef int32_t type_t;

   Internally, Yices maintains a global table of types and an element
   of type :c:type:`type_t` is an index in this global table.

.. c:macro:: NULL_TYPE

   This code is returned by type constructors when an error occurs.
   Its definition is::

     #define NULL_TYPE (-1)

   This is not a valid index in the global type table.

.. c:type:: type_vector_t

   Vector of types. This is a structure defined as follows::

     typedef struct type_vector_s {
       uint32_t capacity;
       uint32_t size;
       type_t *data;
     }

   A type vector ``v`` stores a variable-sized array of :c:type:`type_t`
   elements:

   - ``v.capacity`` is the full size of array ``v.data``

   - ``v.size`` is the number of elements stored in ``v.data``

   - ``v.data`` is a dynamically allocated array that contains the elements

   The API provides functions for initializing, emptying, and deleting
   type vectors. See :ref:`vectors`.


Yices Terms
-----------

.. c:type:: term_t

   All term constructors return objects of type :c:type:`term_t`, defined
   as follows::

     typedef int32_t term_t;

   A :c:type:`term_t` is an index in a global term table.

.. c:macro:: NULL_TERM

   This special code is returned by term constructors to report an error.
   It is defined as follows::

     #define NULL_TERM (-1)

.. c:type:: term_vector_t

   Vectors of terms. This is a structure defined as follows::

     typedef struct type_vector_s {
       uint32_t capacity;
       uint32_t size;
       type_t *data;
     }

   A term vector ``v`` stores a variable-sized array of :c:type:`term_t`
   elements:

   - ``v.capacity`` is the full size of array ``v.data``

   - ``v.size`` is the number of elements stored in ``v.data``

   - ``v.data`` is a dynamically allocated array that contains the elements

   See :ref:`vectors`.

.. c:type:: term_constructor_t

   blah blah blah


Contexts
--------

.. c:type:: context_t

   Opaque type of context::

     typedef struct context_s context_t;

   A context is a central data structure in Yices. A context stores a
   set or formulas to check for satisfiability. The API includes
   function to initialize and configure contexts, assert formulas in a
   context, check satisfiability, and construct models.

.. c:type:: ctx_config_t

   Context configuration record::

     typedef struct ctx_config_s ctx_config_t;

   When a context is created, it is possible to configue it to use
   a specific solver or combination of solvers. It is also possible
   to specify whether or not the context supports features such as
   backtracking and removal of formula (via a push/pop mechanism).

   A :c:type:`ctx_config_t` object is a descriptor that defines
   context configuration. It is an opaque data structure that lists
   the solvers to use and the features supported by the context.

.. c:type:: param_t

   Parameter record::

     typedef struct param_s param_t;

   A parameter record stores various parameters that control heuristics
   used by the solvers. For example, heuristic parameters specify the
   restart strategy employed by the CDCL SAT solver. Other parameters
   control the branching heuristics, or the generation of theory lemmas
   by the Simplex-based arithmetic solver.

.. c:type:: smt_status_t

   Context state::

     typedef enum smt_status {
       STATUS_IDLE,
       STATUS_SEARCHING,
       STATUS_UNKNOWN,
       STATUS_SAT,
       STATUS_UNSAT,
       STATUS_INTERRUPTED,
       STATUS_ERROR
     } smt_status_t;

   A context can be in one of the following states:

   .. c:enum:: STATUS_IDLE
      :noindex:

      This is the initial state.

      In this state, it is possible to assert formulas in the context.
      After assertions, the state may change to :c:enum:`STATUS_UNSAT` if
      the assertions are trivially unsatisfiable. Otherwise, the state
      remains :c:enum:`STATUS_IDLE`.

   .. c:enum:: STATUS_SEARCHING

      This is the state during search.

      A context enters this state after a call to one of the *check* functions.
      It remains in this state until either the solver completes or the
      search is interrupted.
      
   .. c:enum:: STATUS_UNKNOWN

      State entered when the search terminates but is inconclusive.

      This may happen if the context's solver is not complete for the specific
      logic used. For example, the logic may have quantifiers.

   .. c:enum:: STATUS_SAT

      State entered when the search terminats and the assertions are satisfiable.

   .. c:enum:: STATUS_UNSAT

      State entered when the search terminats and the assertions are not satisfiable.

   .. c:enum:: STATUS_INTERRUPTED

      State entered when the search is interrupted.

      When a context is in the state :c:enum:`STATUS_SEARCHING` then the search
      can be interrupted through a call to :c:func:`yices_stop_search`. This
      moves the context's state to :c:enum:`STATUS_INTERRUPTED`.

   .. c:enum:: STATUS_ERROR

      This is an error code. It is returned by functions that operate on a
      context when the operation cannot be performed.

   The functions that check for satisfiability return one of the above codes.


Models
------

.. c:type:: model_t

.. c:type:: yval_t

.. c:type:: yval_vector_t

.. c:type:: yices_gen_mode_t

Error Reports
-------------

.. c:type:: error_code_t

.. c:type:: error_report_t
