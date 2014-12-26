:tocdepth: 2

.. highlight:: c

.. _type_operations:

Operations on Types
===================

The Yices types include primitive types for Booleans, integers, reals,
and bitvectors. Other atomic types can be extended by declaring new
*uninterpreted types* and new *scalar types*. In addition, Yices
includes tuple and function types. 

The API includes functions for accessing the primitive types, creating
uninterpreted and scalar types, and for building tuple and function
types, and various functions for examining types.


Type Constructors
-----------------

All type constructors return an object of type :c:type:`type_t`, which
is either a type or the special value :c:macro:`NULL_TYPE` if there is
an error. For error diagnostic, use the functions documented in
section :ref:`error_reports`.

.. c:function:: type_t  yices_bool_type(void)

   Returns the Boolean type

.. c:function:: type_t  yices_int_type(void)

   Returns the integer type

.. c:function:: type_t  yices_real_type(void)

   Returns the real type


.. c:function:: type_t  yices_bv_type(uint32_t size)

   Constructor for bitvector types.

   **Parameter**

   - *size* is the number of bits. It must be positive and no more than
     :c:macro:`YICES_MAX_BVSIZE`

   **Error reports**

   - if *size* is 0:

     -- error code: :c:enum:`POS_INT_REQUIRED`

     -- badval := 0

   - if *size* is more than :c:macro:`YICES_MAX_BVSIZE`:

     -- error code: :c:enum:`MAX_BVSIZE_EXCEEDED`

     -- badval := *size*


.. c:function:: type_t yices_new_uninterpreted_type(void)

   This creates a new uninterpreted type.

.. c:function:: type_t yices_new_scalar_type(uint32_t card)

   Creates a new scalar type.

   **Parameter**

   - *card* is the type cardinality. It must be positive.

   **Error Reports**

   - if *card* is zero:

     -- error code: :c:enum:`POS_INT_REQUIRED`

     -- badval := 0


.. c:function:: type_t yices_tuple_type(uint32_t n, const type_t tau[])

.. c:function:: type_t yices_tuple_type1(type_t tau1)

.. c:function:: type_t yices_tuple_type2(type_t tau1, type_t tau2)

.. c:function:: type_t yices_tuple_type3(type_t tau1, type_t tau2, type_t tau3)


.. c:function:: type_t yices_function_type(uint32_t n, const type_t dom[], type_t range)

.. c:function:: type_t yices_function_type1(type_t tau1, type_t range)

.. c:function:: type_t yices_function_type2(type_t tau1, type_t tau2, type_t range)

.. c:function:: type_t yices_function_type3(type_t tau1, type_t tau2, type_t tau3, type_t range)


Access to Type Components
-------------------------
