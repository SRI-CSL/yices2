.. highlight:: c

.. _api_types:

C Types
=======

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

   This type gives access to the internal term representation used by
   Yices.  It enumerates the term constructors used internally, and is
   the return type of function :c:func:`yices_term_constructor`.

   Atomic terms include constants, variables, and uninterpreted terms
   (i.e., all terms that do not have subterms). For such terms,
   function :c:func:`yices_term_constructor` returns on of the
   following codes:

   .. c:enum:: YICES_BOOL_CONSTANT

      Boolean constants: true and false

   .. c:enum:: YICES_ARITH_CONSTANT

      Rational constants

   .. c:enum:: YICES_BV_CONSTANT

      Bitvector constants

   .. c:enum:: YICES_SCALAR_CONSTANT
 
      Constants of uninterpreted or scalar type

   .. c:enum:: YICES_VARIABLE

      Variables in quantifiers and lambda expressions

   .. c:enum:: YICES_UNINTERPRETED_TERM

      Uninterpreted terms (i.e., global variables).

   Composite terms are defined by a constructor and a list of children terms.
   They can have one of the following constructors:

   .. c:enum:: YICES_ITE_TERM

      If-then-else

   .. c:enum:: YICES_APP_TERM

      Application of an unintepreted function

   .. c:enum:: YICES_UPDATE_TERM

      Function update

   .. c:enum:: YICES_TUPLE_TERM

      Tuple

   .. c:enum:: YICES_EQ_TERM

      Binary equality

   .. c:enum:: YICES_DISTINCT_TERM
 
      Distinct

   .. c:enum:: YICES_FORALL_TERM

      Universal quantifier

   .. c:enum:: YICES_LAMBDA_TERM

      Lambda term

   .. c:enum:: YICES_NOT_TERM

      Boolean negation

   .. c:enum:: YICES_OR_TERM

      N-ary OR

   .. c:enum:: YICES_XOR_TERM

      N-ary XOR

   .. c:enum:: YICES_BV_ARRAY

      Bitvector represented as an array of Booleans terms

   .. c:enum:: YICES_BV_DIV

      Unsigned bitvector division

   .. c:enum:: YICES_BV_REM

      Remainder in an unsigned bitvector division

   .. c:enum:: YICES_BV_SDIV

      Signed bitvector division, with rounding to zero

   .. c:enum:: YICES_BV_SREM

      Remainder in a signed bitvector division

   .. c:enum:: YICES_BV_SMOD

      Remainder in signed bitvector division, with rounding to minus
      infinity

   .. c:enum:: YICES_BV_SHL

      Bitvector shift left

   .. c:enum:: YICES_BV_LSHR

      Bivector logical shift right

   .. c:enum:: YICES_BV_ASHR

      Bitvector arithmetic shift right

   .. c:enum:: YICES_BV_GE_ATOM

      Bitvector greater than or equal to (unsigned)

   .. c:enum:: YICES_BV_SGE_ATOM

      Bitvector greater than or equal to (signed)

   .. c:enum:: YICES_ARITH_GE_ATOM

      Arithmetic greater then or equal to

   Two special constructors are used for projections and bit extractions:

   .. c:enum:: YICES_SELECT_TERM

      Projection of a tuple term on one component

   .. c:enum:: YICES_BIT_TERM

      Extraction of the i-th bit of a bitvector (as a Boolean)

   Arithmetic and bitvector polynomials use the following constructors:

   .. c:enum:: YICES_BV_SUM

      Sum of the form ''a_0 t_0 + ... + a_n t_n'' where

        - all coefficients a_i are bitvector constants

        - all terms t_i (except possibly t_0) are bitvector terms

      All terms and coefficients have the same size (i.e., same number of bits).

      As a special case,  t_0 may be :c:macro:`NULL_TERM` to encode a constant term.
      In this case, the sum can be interpreted as

          ''a_0 + a_1 t_1 + ... + a_n t_n''

   .. c:enum:: YICES_ARITH_SUM

      Sum of the form ''a_0 t_0 + ... + a_n t_n'' where

        - all coefficients are rational constants

        - all terms t_i (except possibly t_0) are arithmetic terms

      As in :c:enum:`YICES_BV_SUM`, the term t_0 may be :c:macro:`NULL_TERM` to
      encode a constant term.

   .. c:enum:: YICES_POWER_PRODUCT

      Products of the form ''t_0^d_0 x ... x t_n^d_n'' where

        - all exponents d_i are positive integers

        - the terms t_i are either all arithmetic terms or all bitvector terms

   The last code is used to report errors:

   .. c:enum:: YICES_CONSTRUCTOR_ERROR
 
      This special code is returned by :c:func:`yices_term_constructor` if its
      argument is not a valid term.
   
   See :ref:`access_to_term_representation` for more details on accessing the
   internal term representation.

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

   When a context is created, it is possible to configure it to use
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

      State entered when the search terminates and the assertions are satisfiable.

   .. c:enum:: STATUS_UNSAT

      State entered when the search terminates and the assertions are not satisfiable.

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

   Opaque type of models::

     typedef struct model_s model_t;

   A model is a mapping from uninterpreted terms to constant values
   that can be atomic values, constant tuples, or functions.

   Models can be constructed from a context after checking that the
   context is satisfiable, or using an explicit model-construction
   function.

.. c:type:: yval_t

   The value of a term in a model can be an atomic value, a tuple, or
   a function. The API provides functions to compute and examine these
   values. The different constants are stored in a DAG data structure.
   Leaf nodes in this DAG are atomic values and non-leaf nodes define
   tuples and functions. Every node in this DAG has a unique id and a
   tag of type :c:type:`yval_t` that defines the node type::

      typedef enum yval_tag {
        YVAL_UNKNOWN,
	YVAL_BOOL,
	YVAL_RATIONAL,
	YVAL_BV,
	YVAL_SCALAR,
	YVAL_TUPLE,
	YVAL_FUNCTION,
	YVAL_MAPPING
      } yval_tag_t;

   These codes are interpreted as follows:

   .. c:enum:: YVAL_UNKNOWN

   .. c:enum:: YVAL_BOOL

   .. c:enum:: YVAL_RATIONAL

   .. c:enum:: YVAL_BV

   .. c:enum:: YVAL_SCALAR

   .. c:enum:: YVAL_TUPLE

   .. c:enum:: YVAL_FUNCTION

   .. c:enum:: YVAL_MAPPING

   

.. c:type:: yval_vector_t

.. c:type:: yices_gen_mode_t

Error Reports
-------------

.. c:type:: error_code_t

.. c:type:: error_report_t
