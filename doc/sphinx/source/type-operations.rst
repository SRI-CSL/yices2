:tocdepth: 2

.. include:: macros

.. highlight:: c

.. _type_operations:

Types
=====

Yices has primitive types for Booleans, integers, reals, and
bitvectors. Other atomic types can be created by declaring new
*uninterpreted types* and new *scalar types*. In addition, the type
system includes tuple and function types.

The API provides functions for accessing the primitive types, creating
uninterpreted and scalar types, and for building tuple and function
types. The API also includes various functions for examining types.
Functions for printing types are documented in :ref:`pretty_printing`.

All type constructors return an object of type :c:type:`type_t`, which
is either a type or the special value :c:macro:`NULL_TYPE` if there is
an error. For error diagnostic, use the functions documented in
section :ref:`error_reports`.

**Common error reports**

  - All functions set the error report as follows if they receive a
    type parameter *tau* that is not valid:
 
    -- error code: :c:enum:`INVALID_TYPE`

    -- type1 := *tau* (i.e., the invalid type)

  - If an integer parameter must be positive, the functions will
    report the following error when the input is zero:

    -- error code: :c:enum:`POS_INT_REQUIRED`

    -- badval := 0


Other error reports are possible. They are listed for each function.


Type Constructors
-----------------

.. c:function:: type_t  yices_bool_type(void)

   Returns the Boolean type.

.. c:function:: type_t  yices_int_type(void)

   Returns the integer type.

.. c:function:: type_t  yices_real_type(void)

   Returns the real type.

.. c:function:: type_t  yices_bv_type(uint32_t size)

   Constructs a bitvector type.

   **Parameter**

   - *size* is the number of bits. It must be positive and no more than
     :c:macro:`YICES_MAX_BVSIZE`

   **Error report**

   - If *size* is more than :c:macro:`YICES_MAX_BVSIZE`:

     -- error code: :c:enum:`MAX_BVSIZE_EXCEEDED`

     -- badval := *size*


.. c:function:: type_t yices_new_scalar_type(uint32_t card)

   Creates a new scalar type.

   **Parameter**

   - *card* is the type cardinality. It must be positive.

.. c:function:: type_t yices_new_uninterpreted_type(void)

   Creates a new uninterpreted type.


.. c:function:: type_t yices_tuple_type(uint32_t n, const type_t tau[])

   Creates the tuple type: *(tuple tau[0] ... tau[n-1])*.

   **Parameters**

   - *n*: number of components.

   - *tau*: array of *n* types

   *n* must be positive and no more than :c:macro:`YICES_MAX_ARITY`
  
   **Error report**

   - If *n* is more than :c:macro:`YICES_MAX_ARITY`:

     -- error code: :c:enum:`TOO_MANY_ARGUMENTS`

     -- badval := *n*

.. c:function:: type_t yices_tuple_type1(type_t tau1)

   Creates the tuple type *(tuple tau1)*.

   This function is equivalent to :c:func:`yices_tuple_type` with *n=1*.

.. c:function:: type_t yices_tuple_type2(type_t tau1, type_t tau2)

   Creates the tuple type *(tuple tau1 tau2)*.

   This function is equivalent to :c:func:`yices_tuple_type` with *n=2*.

.. c:function:: type_t yices_tuple_type3(type_t tau1, type_t tau2, type_t tau3)

   Creates the tuple type *(tuple tau1 tau2 tau3)*.

   This function is equivalent to :c:func:`yices_tuple_type` with *n=3*.


.. c:function:: type_t yices_function_type(uint32_t n, const type_t dom[], type_t range)

   Creates the function type *(-> dom[0] ... dom[n-1] range)*.

   **Parameters**

   - *n*: function arity (i.e., size of array *dom*)

   - *dom*: array of domain types

   - *range*: range type

   *n* must be positive and no more than :c:macro:`YICES_MAX_ARITY`

   **Error report**

   - If *n* is more than :c:macro:`YICES_MAX_ARITY`:

     -- error code: :c:enum:`TOO_MANY_ARGUMENTS`

     -- badval := *n*
   
.. c:function:: type_t yices_function_type1(type_t tau1, type_t range)
 
   Creates the unary function type: *(-> tau1 range*).

   This function is equivalent to :c:func:`yices_function_type` with *n=1*.

.. c:function:: type_t yices_function_type2(type_t tau1, type_t tau2, type_t range)

   Creates the binary function type: *(-> tau1 tau2 range*).

   This function is equivalent to :c:func:`yices_function_type` with *n=2*.

.. c:function:: type_t yices_function_type3(type_t tau1, type_t tau2, type_t tau3, type_t range)

   Creates the ternary function type: *(-> tau1 tau2 tau3 range*).

   This function is equivalent to :c:func:`yices_function_type` with *n=3*.



Tests on Types
--------------

The following functions check a property of a type *tau*. They return
0 for false and 1 for true. 

If *tau* is not a valid type, these functions return false (i.e., 0)
and set the error report (error code: :c:enum:`INVALID_TYPE`).

.. c:function:: int32_t yices_type_is_bool(type_t tau)

   Checks whether *tau* is the Boolean type.

.. c:function:: int32_t yices_type_is_int(type_t tau)

   Checks whether *tau* is the integer type.

.. c:function:: int32_t yices_type_is_real(type_t tau)

   Checks whether *tau* is the real type.

.. c:function:: int32_t yices_type_is_arithmetic(type_t tau)

   Checks whether *tau* is an arithmetic type (i.e., either integer or real).

.. c:function:: int32_t yices_type_is_bitvector(type_t tau)

   Checks whether *tau* is a bitvector type.

.. c:function:: int32_t yices_type_is_scalar(type_t tau)

   Checks whether *tau* is a scalar type.

.. c:function:: int32_t yices_type_is_uninterpreted(type_t tau)

   Checks whether *tau* is uninterpreted.

.. c:function:: int32_t yices_type_is_tuple(type_t tau)

   Checks whether *tau* is a tuple type.

.. c:function:: int32_t yices_type_is_function(type_t tau)

   Checks whether *tau* is a function type.


.. c:function:: int32_t yices_test_subtype(type_t tau, type_t sigma)

   Checks whether *tau* is a subtype of *sigma*.

   The function returns 1 for true and 0 for false. If *tau* or
   *sigma* is not a valid type, the function returns false and sets
   the error report.

.. c:function:: int32_t yices_compatible_types(type_t tau, type_t sigma)

   Checks whether *tau* and *sigma* are compatible.

   The function returns 1 for true and 0 for false. If *tau* or
   *sigma* is not a valid type, the function returns false and sets
   the error report.

   Two types are compatible if they have a common supertype. For
   example, *real* and *int* are compatible because their common
   supertype is *real*. Consult the `manual
   <https://yices.csl.sri.com/papers/manual.pdf>`_ for more details.




Access to Type Components
-------------------------

The following functions give access to attributes and components of a type.

.. c:function:: uint32_t yices_bvtype_size(type_t tau)

   Returns the number of bits of type *tau*, or 0 if there's an error.

   **Error report**

   - If *tau* is not a bitvector type:

     -- error code: :c:enum:`BVTYPE_REQUIRED`

     -- type1 := *tau*


.. c:function:: uint32_t yices_scalar_type_card(type_t tau)

   Returns the cardinality of type *tau*, or 0 if there's an error.

   **Error report**

   - If *tau* is not a scalar type:

     -- error code: :c:enum:`INVALID_TYPE_OP`


.. c:function:: int32_t yices_type_num_children(type_t tau)

   Number of children of type *tau*. or -1 if there's an error.

   - If *tau* is a tuple type (tuple |tau|\ |_1| |...| |tau|\ |_n|\ ), the function returns *n*

   - If *tau* is a function type (-> |tau|\ |_1| |...| |tau|\ |_n| |sigma|\ ), the function returns *n+1*

   - If *tau* is any other type, the function returns 0


.. c:function:: type_t yices_type_child(type_t tau, int32_t i)

   Returns the *i*-th child of type *tau*.

   - If *tau* has *n* children then index *i* must be in the interval [0 ... *n*-1].

   - For a tuple type (tuple |tau|\ |_1| |...| |tau|\ |_n|),

     -- the first child (with index *i*\ =0) is |tau|\ |_1|,

     -- the last child (with index *i*\ =\ *n*-1) is |tau|\ |_n|.

   - For a function type (-> |tau|\ |_1| |...| |tau|\ |_n| |sigma|\ ),

     -- the first child (with index *i*\ =0) is |tau|\ |_1|,

     -- the last child (with index *i*\ =\ *n*) is |sigma|.

   - For any other type, the function returns :c:enum:`NULL_TYPE` as the type has no children.

   **Error report**

   - If *i* is negative or larger than the number of children minus one:

     -- error code: :c:enum:`INVALID_TYPE_OP`


.. c:function:: int32_t yices_type_children(type_t tau, type_vector_t *v)

   Collects the children of a type.

   The children of type *tau* are collected in vector *v*. The vector
   must be initialized first by calling function :c:func:`yices_init_type_vector`.

   If *tau* is not a valid type, this function returns -1, sets the error
   report, and leaves *v* unchanged.

   Otherwise, the children are stored in *v* in the same order as given
   by :c:func:`yices_type_child`.

   - *v->size* is the number of children of *tau*

   - *v->data[i]* contains the *i*-th child.

   If *tau* is an atomic type, then *v->size* is set to 0 and *v->data* is empty.

Type Macros
-----------

Yices supports type macros and type constructors, which are uninterpreted type 
constructors that can be instantiated with type arguments.

The following functions are available for working with type macros:

.. c:function:: type_t yices_type_variable(uint32_t id)

   Creates a type variable with the given id.

   **Parameter**

   - *id* is the identifier for the type variable

   **Returns**

   A type variable of type :c:type:`type_t`

.. c:function:: int32_t yices_type_constructor(const char *name, uint32_t n)

   Creates a type constructor with the given name and arity.

   **Parameters**

   - *name* is the name of the type constructor
   - *n* is the arity (number of type parameters). It must be positive and no more than
     :c:macro:`TYPE_MACRO_MAX_ARITY`

   **Returns**

   The constructor's id (a non-negative integer) or -1 if there's an error

   **Error reports**

   - If *n* is zero:

     -- error code: :c:enum:`POS_INT_REQUIRED`

     -- badval := 0

   - If *n* is more than :c:macro:`TYPE_MACRO_MAX_ARITY`:

     -- error code: :c:enum:`TOO_MANY_MACRO_PARAMS`

     -- badval := *n*

.. c:function:: int32_t yices_type_macro(const char *name, uint32_t n, type_t *vars, type_t body)

   Creates a type macro with the given name, arity, type variables, and body.

   **Parameters**

   - *name* is the name of the type macro
   - *n* is the arity (number of type parameters)
   - *vars* is an array of *n* distinct type variables
   - *body* is the type expression that defines the macro

   **Returns**

   The macro's id (a non-negative integer) or -1 if there's an error

   **Error reports**

   - If *n* is zero:

     -- error code: :c:enum:`POS_INT_REQUIRED`

     -- badval := 0

   - If *n* is more than :c:macro:`TYPE_MACRO_MAX_ARITY`:

     -- error code: :c:enum:`TOO_MANY_MACRO_PARAMS`

     -- badval := *n*

   - If *body* or one of *vars[i]* is not a valid type:

     -- error code: :c:enum:`INVALID_TYPE`

     -- type1 := *body* or *vars[i]*

   - If *vars[i]* is not a type variable:

     -- error code: :c:enum:`TYPE_VAR_REQUIRED`

     -- type1 := *vars[i]*

   - If the same variable occurs twice or more in *vars*:

     -- error code: :c:enum:`DUPLICATE_TYPE_VAR`

     -- type1 := the duplicate variable

.. c:function:: type_t yices_instance_type(int32_t cid, uint32_t n, type_t tau[])

   Creates an instance of a type macro or constructor by applying it to type arguments.

   **Parameters**

   - *cid* is the constructor or macro id
   - *n* is the number of arguments
   - *tau* is an array of *n* argument types

   **Returns**

   The resulting type or :c:macro:`NULL_TYPE` if there's an error

   **Error reports**

   - If *cid* is not a valid macro or constructor id:

     -- error code: :c:enum:`INVALID_MACRO`

     -- badval := *cid*

   - If *n* is not the same as the macro/constructor arity:

     -- error code: :c:enum:`WRONG_NUMBER_OF_ARGUMENTS`

     -- badval := *n*

   - If one of *tau[i]* is not a valid type:

     -- error code: :c:enum:`INVALID_TYPE`

     -- type1 := *tau[i]*

.. c:function:: int32_t yices_get_macro_by_name(const char *name)

   Gets the macro id for a given name.

   **Parameter**

   - *name* is the name of the macro or constructor

   **Returns**

   The macro's id (a non-negative integer) or -1 if there's no macro or constructor with that name

.. c:function:: void yices_remove_type_macro_name(const char *name)

   Removes the mapping of a name to a macro id.

   **Parameter**

   - *name* is the name of the macro or constructor

   No change is made if no such mapping exists.

.. c:function:: void yices_delete_type_macro(int32_t id)

   Removes a macro with the given id.

   **Parameter**

   - *id* must be a valid macro index (non-negative)

.. c:macro:: TYPE_MACRO_MAX_ARITY

   The maximum arity allowed for type macros and constructors. This is defined as 128.
