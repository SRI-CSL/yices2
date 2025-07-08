.. include:: macros

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
     } type_vector_t;

   A type vector *v* stores a variable-sized array of types:

   - *v.capacity* is the full size of array *v.data*

   - *v.size* is the number of elements stored in *v.data*

   - *v.data* is a dynamically allocated array that contains the elements

   The API provides functions for initializing, emptying, and deleting
   type vectors. See :ref:`vectors`.


.. _types_for_terms:

Yices Terms
-----------

.. c:type:: term_t

   All term constructors return objects of type :c:type:`term_t`, which is defined
   as follows::

     typedef int32_t term_t;

   Internally, Yices stores terms in a global term table and an object of type 
   :c:type:`term_t` is an index in this table.

.. c:macro:: NULL_TERM

   This special code is returned by term constructors to report an error.
   It is defined as follows::

     #define NULL_TERM (-1)

.. c:type:: term_vector_t

   Vector of terms. This is a structure defined as follows::

     typedef struct term_vector_s {
       uint32_t capacity;
       uint32_t size;
       term_t *data;
     } term_vector_t;

   A term vector *v* stores a variable-sized array of terms:

   - *v.capacity* is the full size of array *v.data*

   - *v.size* is the number of elements stored in *v.data*

   - *v.data* is a dynamically allocated array that contains the elements

   See :ref:`vectors`.

.. _term_constructors:

.. c:type:: term_constructor_t

   This type gives access to the internal term representation used by
   Yices.  It enumerates the term constructors used internally, and it is
   the return type of function :c:func:`yices_term_constructor`. ::

    typedef enum term_constructor {
      YICES_CONSTRUCTOR_ERROR = -1,
      // atomic terms
      YICES_BOOL_CONSTANT,
      YICES_ARITH_CONSTANT,
      YICES_BV_CONSTANT,
      YICES_SCALAR_CONSTANT,
      YICES_VARIABLE,
      YICES_UNINTERPRETED_TERM,
      // composite terms
      YICES_ITE_TERM,
      YICES_APP_TERM,
      YICES_UPDATE_TERM,
      YICES_TUPLE_TERM,
      YICES_EQ_TERM,
      YICES_DISTINCT_TERM,
      YICES_FORALL_TERM,
      YICES_LAMBDA_TERM,
      YICES_NOT_TERM,
      YICES_OR_TERM,
      YICES_XOR_TERM,
      YICES_BV_ARRAY,
      YICES_BV_DIV,
      YICES_BV_REM,
      YICES_BV_SDIV,
      YICES_BV_SREM,
      YICES_BV_SMOD,
      YICES_BV_SHL,
      YICES_BV_LSHR,
      YICES_BV_ASHR,
      YICES_BV_GE_ATOM,
      YICES_BV_SGE_ATOM,
      YICES_ARITH_GE_ATOM,
      YICES_ARITH_ROOT_ATOM,
      YICES_ABS,
      YICES_CEIL,
      YICES_FLOOR,
      YICES_RDIV,
      YICES_IDIV,
      YICES_IMOD,
      YICES_IS_INT_ATOM,
      YICES_DIVIDES_ATOM,
      // projections
      YICES_SELECT_TERM,
      YICES_BIT_TERM,
      // sums
      YICES_BV_SUM,
      YICES_ARITH_SUM,
      // products
      YICES_POWER_PRODUCT
    } term_constructor_t;


   Atomic terms include constants, variables, and uninterpreted terms
   (i.e., all terms that do not have subterms). For such terms,
   function :c:func:`yices_term_constructor` returns one of the
   following codes:

   .. c:enum:: YICES_BOOL_CONSTANT

      Boolean constants

   .. c:enum:: YICES_ARITH_CONSTANT

      Rational constants

   .. c:enum:: YICES_BV_CONSTANT

      Bitvector constants

   .. c:enum:: YICES_SCALAR_CONSTANT
 
      Constants of uninterpreted or scalar type

   .. c:enum:: YICES_VARIABLE

      Variables in quantifiers and lambda expressions

   .. c:enum:: YICES_UNINTERPRETED_TERM

      Uninterpreted terms (i.e., global variables)

   Composite terms are defined by a constructor and a list of children terms.
   They can have one of the following constructors:

   .. c:enum:: YICES_ITE_TERM

      If-then-else

   .. c:enum:: YICES_APP_TERM

      Application of an uninterpreted function

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

      Remainder in the unsigned bitvector division

   .. c:enum:: YICES_BV_SDIV

      Signed bitvector division, with rounding to zero

   .. c:enum:: YICES_BV_SREM

      Remainder in the signed bitvector division

   .. c:enum:: YICES_BV_SMOD

      Remainder in the signed bitvector division with rounding to
      minus infinity

   .. c:enum:: YICES_BV_SHL

      Bitvector shift left

   .. c:enum:: YICES_BV_LSHR

      Bivector logical shift right

   .. c:enum:: YICES_BV_ASHR

      Bitvector arithmetic shift right

   .. c:enum:: YICES_BV_GE_ATOM

      Unsigned bitvector inequality (greater than or equal to)

   .. c:enum:: YICES_BV_SGE_ATOM

      Signed bitvector inequality

   .. c:enum:: YICES_ARITH_GE_ATOM

      Arithmetic inequality (greater than or equal to)

   .. c:enum:: YICES_ARITH_ROOT_ATOM

      Nonlinear arithmetic atom.

   .. c:enum:: YICES_ABS

      Absolute value

   .. c:enum:: YICES_CEIL

      Ceiling (i.e., rounding up to the nearest integer)

   .. c:enum:: YICES_FLOOR

      Floor (i.e., rounding down to the nearest integer)

   .. c:enum:: YICES_RDIV

      Division

   .. c:enum:: YICES_IDIV

      Integer division

   .. c:enum:: YICES_IMOD

      Modulo

   .. c:enum:: YICES_IS_INT_ATOM

      Integrality test

   .. c:enum:: YICES_DIVIDES_ATOM

      Divisibility test

   Two special constructors are used for projection and bit extraction:

   .. c:enum:: YICES_SELECT_TERM

      Projection of a tuple term on one component

   .. c:enum:: YICES_BIT_TERM

      Extraction of the i-th bit of a bitvector (as a Boolean)

   Arithmetic and bitvector polynomials use the following constructors:

   .. c:enum:: YICES_BV_SUM

      Sum of the form *a*\ |_0| *t*\ |_0| + |...| + *a*\ |_n| *t*\ |_n| where

        - all the coefficients *a*\ |_i| are bitvector constants

        - all the terms *t*\ |_i| (except possibly *t*\ |_0|) are bitvector terms

      All terms and coefficients have the same size (i.e., same number of bits).

      As a special case, *t*\ |_0| may be equal to :c:macro:`NULL_TERM` to
      encode a constant term.  In this case, the sum can be
      interpreted as *a*\ |_0| + *a*\ |_1| *t*\ |_1| + |...| + *a*\ |_n| *t*\ |_n|.

   .. c:enum:: YICES_ARITH_SUM

      Sum of the form *a*\ |_0| *t*\ |_0| + |...| + *a*\ |_n| *t*\ |_n| where

        - the coefficients are rational constants

        - all the terms *t*\ |_i| (except possibly *t*\ |_0|) are arithmetic terms

      As in :c:enum:`YICES_BV_SUM`, the term *t*\ |_0| may be :c:macro:`NULL_TERM` to
      encode a constant term.

   .. c:enum:: YICES_POWER_PRODUCT


      Products of the form *t*\ |_0|\ ^\ *d*\ |_0| |times| |...| |times| *t*\ |_n|\ ^\ *d*\ |_n| where

        - the exponents *d*\ |_i| are positive integers

        - the terms *t*\ |_i| are either all arithmetic terms or all bitvector terms

   The last code is used to report errors:

   .. c:enum:: YICES_CONSTRUCTOR_ERROR
 
      This special code is returned by :c:func:`yices_term_constructor` if its
      argument is not a valid term.
   
   See :ref:`access_to_term_representation` for more details.


Contexts
--------

.. c:type:: context_t

   Opaque type of contexts::

     typedef struct context_s context_t;

   A context is a central data structure in Yices. A context stores a
   set of formulas to check for satisfiability. The API includes
   function to initialize and configure contexts, assert formulas in a
   context, check satisfiability, and construct models from a context.

.. c:type:: ctx_config_t

   Context-configuration record::

     typedef struct ctx_config_s ctx_config_t;

   When a context is created, it can be configured to use a specific
   solver or combination of solvers. One can also specify whether or
   not the context supports features such as backtracking and removal
   of formulas (via a push/pop mechanism).

   A :c:type:`ctx_config_t` object describes a context
   configuration. It is an opaque data structure that lists the
   solvers to use and the features supported by the context.

.. c:type:: param_t

   Parameter record::

     typedef struct param_s param_t;

   A parameter record stores various parameters that control the
   heuristics used by the solvers. For example, heuristic parameters
   can specify the restart strategy employed by the CDCL SAT solver. Other
   parameters control the branching heuristics, or the generation of
   theory lemmas by the Simplex-based arithmetic solver.

.. c:type:: smt_status_t

   Context state::

     typedef enum smt_status {
       YICES_STATUS_IDLE,
       YICES_STATUS_SEARCHING,
       YICES_STATUS_UNKNOWN,
       YICES_STATUS_SAT,
       YICES_STATUS_UNSAT,
       YICES_STATUS_INTERRUPTED,
       YICES_STATUS_ERROR
     } smt_status_t;

   The type :c:type:`smt_status_t` enumerates the possible states of a
   context. It is also the type returned by the function that checks
   whether a context is satisfiable. The following codes are defined:

   .. c:enum:: YICES_STATUS_IDLE

      Initial context state.

      In this state, it is possible to assert formulas in the context.
      After assertions, the state may change to :c:enum:`YICES_STATUS_UNSAT` if
      the assertions are trivially unsatisfiable. Otherwise, the state
      remains :c:enum:`YICES_STATUS_IDLE`.

   .. c:enum:: YICES_STATUS_SEARCHING

      State during search.

      A context enters this state after a call function
      :c:func:`yices_check_context`.  It remains in this state until
      either the solver completes or the search is interrupted.
      
   .. c:enum:: YICES_STATUS_UNKNOWN

      State entered when the search terminates but is inconclusive.

      This may happen if the context's solver is not complete for the specific
      logic used. For example, the logic may have quantifiers.

   .. c:enum:: YICES_STATUS_SAT

      State entered when the search terminates and the assertions are satisfiable.

   .. c:enum:: YICES_STATUS_UNSAT

      State entered when the assertions are known to be unsatisfiable.

      An unsatisfiability can be detected either when a formula is
      asserted (if the inconsistency is detected by formula
      simplification), or when the search terminates.

   .. c:enum:: YICES_STATUS_INTERRUPTED

      State entered when the search is interrupted.

      When a context is in the state :c:enum:`YICES_STATUS_SEARCHING` then the search
      can be interrupted through a call to :c:func:`yices_stop_search`. This
      moves the context's state to :c:enum:`YICES_STATUS_INTERRUPTED`.

   .. c:enum:: YICES_STATUS_ERROR

      This is an error code. It is returned by functions that operate on a
      context when the operation cannot be performed.


Models
------

.. c:type:: model_t

   Opaque type of models::

     typedef struct model_s model_t;

   A model is a mapping from uninterpreted terms to constant values.
   Models can be constructed from a context after checking that the
   context is satisfiable, or using an explicit model-construction
   function.

.. c:type:: yval_tag_t

   The value of a term in a model can be an atomic value, a tuple, or
   a function. Internally, Yices represents tuple and function values
   as nodes in a DAG. The API provides functions to compute and
   examine these nodes, which gives access to the values of terms of
   function or tuple types.  Every node in this DAG has a unique id
   and a tag of type :c:type:`yval_tag_t` that defines the node type::

      typedef enum yval_tag {
        YVAL_UNKNOWN,
	YVAL_BOOL,
	YVAL_RATIONAL,
	YVAL_ALGEBRAIC,
	YVAL_BV,
	YVAL_SCALAR,
	YVAL_TUPLE,
	YVAL_FUNCTION,
	YVAL_MAPPING
      } yval_tag_t;

   These codes are interpreted as follows:

   .. c:enum:: YVAL_UNKNOWN

      Special tag for the unknown value

   .. c:enum:: YVAL_BOOL

      Boolean constants

   .. c:enum:: YVAL_RATIONAL

      Rational constants

   .. c:enum:: YVAL_ALGEBRAIC

      Algebraic numbers

   .. c:enum:: YVAL_BV

      Bitvector constants

   .. c:enum:: YVAL_SCALAR

      Constants of scalar or uninterpreted type
    
   .. c:enum:: YVAL_TUPLE

      Tuples of constants

   .. c:enum:: YVAL_FUNCTION

      Functions
 
   .. c:enum:: YVAL_MAPPING

      Mappings of the form [tuple |->| value] used to represent functions 

   The tags :c:enum:`YVAL_UNKNOWN`, :c:enum:`YVAL_BOOL`,
   :c:enum:`YVAL_RATIONAL`, :c:enum:`YVAL_BV`,
   :c:enum:`YVAL_ALGEBRAIC` and :c:enum:`YVAL_SCALAR` are attached to
   leaf nodes in the DAG. The non-leaf nodes have tags
   :c:enum:`YVAL_TUPLE`, :c:enum:`YVAL_FUNCTION`, and
   :c:enum:`YVAL_MAPPING`.

   The nodes with tag :c:enum:`YVAL_MAPPING` are auxiliary nodes that
   occur in the definition of functions.  In a model, all function
   values are defined by a finite set of mappings, and a default
   value. For example, if we have

      - *f(0, 0) = 0*

      - *f(0, 1) = 1*

      - *f(1, 0) = 1*

      - *f(x, y) = 2* for all other *x* and *y*

   then *f* is represented as follows:

      - set of mappings:
         | [0, 0 |->| 0]
         | [0, 1 |->| 1]
         | [1, 0 |->| 1]

      - default value: 2

   The DAG contains a node for *f*, a node for the default value, and
   three nodes for each of the three mappings.


.. c:type:: yval_t

   This data structure describes a node in the DAG. It consists of a
   *node_id* and a *node_tag*::

      typedef struct yval_s {
        int32_t node_id;
        yval_tag_t node_tag;
      } yval_t;

   The *node_id* is a non-negative integer; all the nodes have
   different *node_ids*. The API includes functions for extracting the
   value encoded in a leaf node and for collecting the children of a
   non-leaf nodes.

.. c:type:: yval_vector_t

   Vector of node descriptors::

      typedef struct yval_vector_s {
        uint32_t capacity;
	uint32_t size;
	yval_t *data;
      } yval_vector_t;

   This record is similar to :c:type:`type_vector_t` and :c:type:`term_vector_t`:

   - *capacity* is the full size of the *data* array
   - *size* is the number of nodes stored in *data*
   - *data* is a dynamically allocated array.

   This type is used by function :c:func:`yices_val_expand_function`, which expands a function node.

   Section :ref:`vectors` explains how to initialize, reset, and delete these vectors.

.. c:type:: yices_gen_mode_t

   Yices includes functions for generalizing a model. Given a model of
   a formula *F(X,Y)*, generalization is a simplified form of quantifier
   elimination. It constructs a formula *G(X)* such that
 
   - *G(X)* is true in the model
   - *G(X)* implies (exists *Y* *F(X, Y)*)

   The type :c:type:`yices_gen_mode_t` lists the different
   generalization methods implemented in Yices::

     typedef enum yices_gen_mode {
       YICES_GEN_DEFAULT,
       YICES_GEN_BY_SUBST,
       YICES_GEN_BY_PROJ
     } yices_gen_mode_t;

   .. c:enum:: YICES_GEN_DEFAULT

      The default generalization method. This is a either *generalization by substitution*
      or *generalization by projection*, depending on the type of variables to eliminate.

   .. c:enum:: YICES_GEN_BY_SUBST

      Generalization by substitution. This replaces the variables to eliminate by
      their value in the model.

   .. c:enum:: YICES_GEN_BY_PROJ

      Generalization by projection. This is a hybrid of Fourier-Motzkin elimination
      and a model-based variant of virtual term substitution.

   See :c:func:`yices_generalize_model` for more details. 
      

.. _error_types:

Error Reports
-------------

.. c:type:: error_code_t

   When a function in the API fails for some reason, it returns a
   special value (typically a negative number or the :c:macro:`NULL`
   pointer) and stores an error code in a global record of type :c:type:`error_report_t`.

   The following error codes are defined:

   .. c:enum:: YICES_NO_ERROR

      Everything is fine.

   .. c:enum:: INVALID_TYPE

      Invalid type argument (not a valid index in the internal type table).

   .. c:enum:: INVALID_TERM

      Invalid term argument (not a valid index in the internal term table).

   .. c:enum:: INVALID_CONSTANT_INDEX

      Attempt to create a constant of uninterpreted type with a negative index,
      or a constant of scalar type with an index that's larger than the type's cardinality.

   .. c:enum:: INVALID_TUPLE_INDEX

      Components of a tuple are indexed from 1 to N. This error code
      signals that an operation to extract or update a tuple
      component was given an index outside the interval [1 .. N].

   .. c:enum:: INVALID_RATIONAL_FORMAT

      The input to :c:func:`yices_parse_rational` does not have the right format.

   .. c:enum:: INVALID_FLOAT_FORMAT

      The input to :c:func:`yices_parse_float` does not have the right format.

   .. c:enum:: INVALID_BVBIN_FORMAT

      The input to :c:func:`yices_parse_bvbin` does not have the right format.

   .. c:enum:: INVALID_BVHEX_FORMAT

      The input to :c:func:`yices_parse_bvhex` does not have the right format.

   .. c:enum:: INVALID_BITSHIFT

      Invalid shift amount for a bitvector shift or rotate operation.

   .. c:enum:: INVALID_BVEXTRACT

      Invalid indices given to function :c:func:`yices_bvextract`.

   .. c:enum:: INVALID_BITEXTRACT

      Invalid index given to function :c:func:`yices_bitextract`.

   .. c:enum:: TOO_MANY_ARGUMENTS

      Attempt to create a type or term of arity larger than :c:macro:`YICES_MAX_ARITY`

   .. c:enum:: TOO_MANY_VARS

      Attempt to create a quantified term or a lambda term with more
      than :c:macro:`YICES_MAX_VARS` variables.

   .. c:enum:: MAX_BVSIZE_EXCEEDED

      Attempt to create a bitvector type or term with more than :c:macro:`YICES_MAX_BVSIZE` bits.

   .. c:enum:: DEGREE_OVERFLOW

      Attempt to create a polynomial of degree higher than :c:macro:`YICES_MAX_DEGREE`.

   .. c:enum:: DIVISION_BY_ZERO

      Zero divider in a rational constant.

   .. c:enum:: POS_INT_REQUIRED

      Bad integer argument: the function expects a positive argument.

   .. c:enum:: NONNEG_INT_REQUIRED

      Bad integer argument: the function expects a non-negative argument.

   .. c:enum:: SCALAR_OR_UTYPE_REQUIRED

      Bad type argument: the function expects either an uninterpreted type or a scalar type.

   .. c:enum:: FUNCTION_REQUIRED

      Bad term argument: a term of function type is expected.

   .. c:enum:: TUPLE_REQUIRED

      Bad term argument: a term of tuple type is expected.

   .. c:enum:: VARIABLE_REQUIRED

      Bad term argument: a variable is expected. Some functions also report this error
      when they expect an argument that can be either a variable or an uninterpreted term.

   .. c:enum:: ARITHTERM_REQUIRED

      Bad term argument: an arithmetic term (of type Int or Real) is expected.

   .. c:enum:: BITVECTOR_REQUIRED

      Bad term argument: a bitvector term is expected.

   .. c:enum:: SCALAR_TERM_REQUIRED

      Bad term argument: a term of scalar type is expected.

   .. c:enum:: WRONG_NUMBER_OF_ARGUMENTS

      Wrong number of arguments in a function application or function
      update.

   .. c:enum:: TYPE_MISMATCH

      Type error in various term constructor.

   .. c:enum:: INCOMPATIBLE_TYPES

      Error in functions that require terms of compatible types. The
      `Yices manual <https://yices.csl.sri.com/papers/manual.pdf>`_
      explains what this means.

   .. c:enum:: DUPLICATE_VARIABLE

      Error in quantifier or lambda term constructors: the same
      variable occurs twice or more.

   .. c:enum:: EMPTY_BITVECTOR

      Attempt to create a bitvector term of type *(bitvector 0)*.

   .. c:enum:: ARITHCONSTANT_REQUIRED

      Invalid term: an arithmetic constant is expected.

   .. c:enum:: BVTYPE_REQUIRED

      Bad type parameter: a bitvector type is expected.

   .. c:enum:: BAD_TERM_DECREF

      Error in reference counting: attempt to decrement the reference counter of
      a term when the counter is already zero.

   .. c:enum:: BAD_TYPE_DECREF

      Error in reference counting: attempt to decrement the reference counter of
      a type when the counter is already zero.

   .. c:enum:: INVALID_TYPE_OP

      Error in a type-exploration function.

   .. c:enum:: INVALID_TERM_OP

      Error in a term-exploration function.

   .. c:enum:: INVALID_TOKEN

      Error in the lexer.

   .. c:enum:: SYNTAX_ERROR

      Syntax error.

   .. c:enum:: UNDEFINED_TYPE_NAME

      A name is not defined in the symbol table for types.

   .. c:enum:: UNDEFINED_TERM_NAME

      A name is not defined in the symbol table for terms.

   .. c:enum:: REDEFINED_TYPE_NAME

      Attempt to redefine an existing type name.

   .. c:enum:: REDEFINED_TERM_NAME

      Attempt to redefine an existing term name.

   .. c:enum:: DUPLICATE_NAME_IN_SCALAR

      A scalar-type definition contains the same element name twice (or more).

   .. c:enum:: DUPLICATE_VAR_NAME

      Error in quantifiers or lambda term definition: the same variable name occurs twice or more.

   .. c:enum:: INTEGER_OVERFLOW

      Integer constant can't be converted to a signed 32bit integer.

   .. c:enum:: INTEGER_REQUIRED

      Rational constant provided when an integer is expected.

   .. c:enum:: RATIONAL_REQUIRED

      Invalid argument: a rational constant is expected.

   .. c:enum:: SYMBOL_REQUIRED

      Error in a definition or local declaration: a symbol is expected.

   .. c:enum:: TYPE_REQUIRED

      Error in a definition or declaration: a type is expected.

   .. c:enum:: NON_CONSTANT_DIVISOR

      Attempt to divide by a non-constant arithmetic term.

   .. c:enum:: NEGATIVE_BVSIZE

      Error while parsing ``(bitvector size)``: the size is negative.

   .. c:enum:: INVALID_BVCONSTANT

      Error while parsing ``(mk-bv size value)``: the value is negative.

   .. c:enum:: TYPE_MISMATCH_IN_DEF

      Error in a term definition: the term value does not have the declared type.

   .. c:enum:: ARITH_ERROR

      Error in an arithmetic operation: an argument is not an arithmetic term.

   .. c:enum:: BVARITH_ERROR

      Error in a bitvector operation: an argument is not a bitvector.


   .. c:enum:: CTX_FREE_VAR_IN_FORMULA

      An assertion contains free variables.

   .. c:enum:: CTX_LOGIC_NOT_SUPPORTED

      An assertion is not in a logic for which the context was configured.

   .. c:enum:: CTX_UF_NOT_SUPPORTED

      An assertion contains uninterpreted functions but the context does not support them.

   .. c:enum:: CTX_ARITH_NOT_SUPPORTED

      An assertion contains arithmetic terms but the context does not support arithmetic.

   .. c:enum:: CTX_BV_NOT_SUPPORTED

      An assertion contains bitvector terms but the context does not support bitvectors.

   .. c:enum:: CTX_ARRAYS_NOT_SUPPORTED

      An assertion contains array or function updates but the context does not support arrays.

   .. c:enum:: CTX_QUANTIFIERS_NOT_SUPPORTED

      An assertion contains quantifiers but the context does not support them.

   .. c:enum:: CTX_LAMBDAS_NOT_SUPPORTED

      An assertion contains lambda terms but the context does not support them.

   .. c:enum:: CTX_NONLINEAR_ARITH_NOT_SUPPORTED

      An assertion contains non-linear polynomials but the context supports only linear arithmetic.

   .. c:enum:: CTX_FORMULA_NOT_IDL

      The context is configured for integer difference logic but an assertion is not in this
      fragment.

   .. c:enum:: CTX_FORMULA_NOT_RDL

      The context is configured for real difference logic but an assertion is not in this
      fragment.

   .. c:enum:: CTX_TOO_MANY_ARITH_VARS

      An internal limit of the arithmetic solver is exceeded.

   .. c:enum:: CTX_TOO_MANY_ARITH_ATOMS

      An internal limit of the arithmetic solver is exceeded.

   .. c:enum:: CTX_TOO_MANY_BV_VARS

      An internal limit of the bitvector solver is exceeded.

   .. c:enum:: CTX_TOO_MANY_BV_ATOMS

      An internal limit of the bitvector solver is exceeded.

   .. c:enum:: CTX_ARITH_SOLVER_EXCEPTION

      General error reported by the arithmetic solver.

   .. c:enum:: CTX_BV_SOLVER_EXCEPTION

      General error reported by the bitvector solver.

   .. c:enum:: CTX_ARRAY_SOLVER_EXCEPTION

      General error reported by the array/function solver.

   .. c:enum:: CTX_SCALAR_NOT_SUPPORTED

      An assertion contains terms of scalar type but the context does not support them.

   .. c:enum:: CTX_TUPLE_NOT_SUPPORTED

      An assertion contains terms of tuple type but the context does not support them.

   .. c:enum:: CTX_UTYPE_NOT_SUPPORTED

      An assertion contains terms of uninterpreted type but the context does not support them.

   .. c:enum:: CTX_INVALID_OPERATION

      Invalid operation on a context: the context is in a state that
      does not allow the operation to be performed.

   .. c:enum:: CTX_OPERATION_NOT_SUPPORTED

      Invalid operation on a context: the context is not configured to support
      this operation.

   .. c:enum:: CTX_UNKNOWN_DELEGATE

      A delegate name is not recognized. See :c:func:`yices_check_formula` and :c:func:`yices_check_formulas` .

   .. c:enum:: CTX_DELEGATE_NOT_AVAILABLE

      Attempt to use a delegate that was not included in the Yices library at compilation time.

   .. c:enum:: CTX_EF_ASSERTIONS_CONTAIN_UF

      Uninterpreted functions not supported by the exists/forall solver.

   .. c:enum:: CTX_EF_NOT_EXISTS_FORALL

      Assertions are not in the exists/forall fragment.

   .. c:enum:: CTX_EF_HIGH_ORDER_VARS

      High-order and tuple variables are not supported.

   .. c:enum:: CTX_EF_INTERNAL_ERROR

      The exists/forall solver failed.

   .. c:enum:: CTX_INVALID_CONFIG

      Reported by :c:func:`yices_new_context` if the requested
      configuration is not supported. This means that the combination
      of solvers does not implement the set of features requested.

   .. c:enum:: CTX_UNKNOWN_PARAMETER

      Invalid parameter name.

   .. c:enum:: CTX_INVALID_PARAMETER_VALUE

      Invalid value for a parameter.

   .. c:enum:: CTX_UNKNOWN_LOGIC

      A logic name is not recognized.

   .. c:enum:: EVAL_UNKNOWN_TERM

      The model does not assign a value to the specified term.

   .. c:enum:: EVAL_FREEVAR_IN_TERM

      A term value cannot be computed because the term contains free variables.

   .. c:enum:: EVAL_QUANTIFIER

      A term value cannot be computed because the term contains quantifiers.

   .. c:enum:: EVAL_LAMBDA

      A term value cannot be computed because the term contains lambdas.

   .. c:enum:: EVAL_FAILED

      A term value cannot be computed for another reason.

   .. c:enum:: EVAL_OVERFLOW

      The value of a term is known but it does not fit in the given
      variable. For example, :c:func:`yices_get_int32_value` will
      report this error if the term value does not fit in a signed,
      32bit integer.

   .. c:enum:: EVAL_CONVERSION_FAILED

      Failed to convert the value of a term in a model into a constant term.
      This error can be reported by :c:func:`yices_get_value_as_term` and 
      :c:func:`yices_term_array_value`.

   .. c:enum:: EVAL_NO_IMPLICANT

      Error reported by :c:func:`yices_implicant_for_formula` and variants
      when the input formula is false in the model.

   .. c:enum:: EVAL_NOT_SUPPORTED

      Reported by function :c:func:`yices_get_algebraic_number_value`
      when the library is compiled without MCSAT support.

   .. c:enum:: MDL_UNINT_REQUIRED

      Invalid map for :c:func:`yices_model_from_map`: an element in the domain is 
      not an uninterpreted term.

   .. c:enum:: MDL_CONSTANT_REQUIRED

      Invalid map for :c:func:`yices_model_from_map`: an element in the range is
      not a constant term.

   .. c:enum:: MDL_DUPLICATE_VAR

      Invalid map for :c:func:`yices_model_from_map`: the domain contains duplicate terms.

   .. c:enum:: MDL_FTYPE_NOT_ALLOWED

      Invalid map for :c:func:`yices_model_from_map`: one element in the domain
      has a function type.

   .. c:enum:: MDL_CONSTRUCTION_FAILED

      Function :c:func:`yices_model_from_map` failed for some other reason.
  
   .. c:enum:: MDL_GEN_TYPE_NOT_SUPPORTED

      Model generalization failed because variables to eliminate have a type that's not
      supported.

   .. c:enum:: MDL_GEN_NONLINEAR

      Model generalization failed because the input formula(s) include non-linear arithmetic.

   .. c:enum:: MDL_GEN_FAILED

      Model generalization failed for some other reason.


   .. c:enum:: YVAL_INVALID_OP
 
      Invalid operation on a value descriptor (node in the model DAG).

   .. c:enum:: YVAL_OVERFLOW

      The value of a leaf node does not fit in the given input variable.

   .. c:enum:: YVAL_NOT_SUPPORTED

      Reported by function :c:func:`yices_val_get_algebraic_number`
      when the library is compiled without MCSAT support.

   .. c:enum:: MCSAT_ERROR_UNSUPPORTED_THEORY

      A formula asserted in the MCSAT solver is not in a theory that this
      solver can process.

   .. c:enum:: OUTPUT_ERROR

      Error when attempting to write to a stream. This error can be reported
      by the pretty-printing functions if they fail to write to the specified 
      file.

      If this error is reported, then system variables and functions
      (e.g., ``errno``, ``perror``, ``strerror``) can be used for
      diagnosis.


   .. c:enum:: INTERNAL_EXCEPTION

      Catch-all code for any other error.

      If you ever see this error code, please report a bug at https://github.com/SRI-CSL/yices2

   A few more error codes are defined in :file:`yices_types.h`. They
   are related to type macros that Yices uses to support the SMT-LIB 2
   sort constructors. Type macros are not exposed in the API.


.. c:type:: error_report_t

   A global record stores information about the errors reported by the API.
   The data includes the error code as defined previously (cf. :c:type:`error_code_t`)
   and additional information that can be used for diagnosis::

     typedef struct error_report_s {
       error_code_t code;
       uint32_t line;
       uint32_t column;
       term_t term1;
       type_t type1;
       term_t term2;
       type_t type2;
       int64_t badval;
     } error_report_t;

   The *code* is always set. The other meaningful fields depend on the error code:

   - the parsing functions :c:func:`yices_parse_type` and :c:func:`yices_parse_term`
     set the *line* and *column* fields to help locate the error in the input string.

   - the field *badval* is set when an incorrect integer argument is provided

   - the other fields are set by terms and type constructors

