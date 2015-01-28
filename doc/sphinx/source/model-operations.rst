:tocdepth: 2

.. include:: macros

.. highlight:: c

.. _model_operations:

Models
======

If a context is satisfiable, Yices can build a model of the context's
assertions. Functions are provided to extract the values of terms in a
model. Atomic values (e.g., integer or bitvector constants) can be
obtained directly. Non-atomic values---that is, tuples or
functions---are represented internally as nodes in a DAG. The API
includes functions to explore this DAG and get the values of tuples or
functions.


Model Construction
------------------

.. c:function:: model_t* yices_get_model(context_t* ctx, int32_t keep_subst)

   Builds a model from a satisfiable context.

   If there's an error, the function returns :c:macro:`NULL`. Otherwise, it
   constructs a model of the assertions in *ctx* and returns a pointer to this
   model. The model must be deleted when it is no longer used by calling
   :c:func:`yices_free_model`.

   **Parameters**

   - *ctx*: context

   - *keep_subst*: flag to indicates whether the model should include
     eliminated variables

   The context's status must be either :c:enum:`STATUS_SAT` or :c:enum:`STATUS_UNKNOWN`.
   
   When assertions are added to a context, the simplification
   procedures may eliminate variables by substitution (see
   :c:func:`yices_context_enable_option`). If *keep_subst* is true
   (i.e. non-zero), then :c:func:`yices_get_model` keeps track of
   eliminated variables so that their values can be computed. If
   *keep_subst* if false (i.e., zero), then the model does not include
   the eliminated variables.

   It is better to set *keep_susbt* to true. The only reason not to do
   it is to save the memory and computation cost of storing the
   eliminated variables. This cost is usually low but there are
   exceptions.

   **Error report**

   - if *ctx*'s status is not :c:enum:`STATUS_SAT` or :c:enum:`STATUS_UNKNOWN`

     -- error code: :c:enum:`CTX_INVALID_OPERATION`
  

.. c:function:: model_t* yices_model_from_map(uint32_t n, const term_t var[], const term_t map[])

   Builds a model from a term-to-term mapping.

   **Parameters**

   - *n*: number of terms in arrays *var* and *map*

   - *var*: array of *n* uninterpreted terms

   - *map*: array of *n* constant terms

   The two arrays *var* and *map* define the mapping: *map[i]* is the
   value of term *var[i]* in the model. There must not be duplicates
   in array *var*, and the type of term *map[i]* must be a subtype of
   *var[i]*'s type.

   This function returns :c:macro:`NULL` if something goes wrong. It
   allocates and creates a model otherwise, and returns a pointer to
   this model. When the model is no longer used, it must be deleted
   by calling :c:func:`yices_free_model`.

   Currently, function types are not supported. Every term in *map[i]*
   must either be an atomic constant, or a tuple of atomic constants,
   or a tuple or tuples of constants, and so forth. The term *var[i]*
   cannot have a function type.

   **Error report**

   - if a term in *var* or *map* is not valid:

     -- error code: :c:enum:`INVALID_TERM`

     -- term1 := the invalid term

   - if *map[i]*'s type is not a subtype of *var[i]*'s type:

     -- error code: :c:enum:`TYPE_MISMATCH`

     -- term1 := *map[i]*

     -- type1 := type of *var[i]* (expected type)

   - if *var[i]* is not an uninterpreted term:

     -- error code: :c:enum:`MDL_UNINT_REQUIRED`

   - if *map[i]* is not a constant:

     -- error code: :c:enum:`MDL_CONSTANT_REQUIRED`

   - if *var* contains duplicate terms:

     -- error code: :c:enum:`MDL_DUPLICATE_VAR`

   - if *map[i]* has function type or has a function subterm:

     -- error code: :c:enum:`MDL_FTYPE_NOT_ALLOWED`

   - if the construction fails for some other reason:

     -- error code: :c:enum:`MDL_CONSTRUCTION_FAILED`

.. c:function::  void yices_free_model(model_t* mdl)

   Deletes a model.

   This function deletes model *mdl*, which must be a pointer returned
   by either :c:func:`yices_get_model` or :c:func:`yices_model_from_map`.

   .. note:: If this function is not called, Yices will automatically free
             the model on a call to :c:func:`yices_exit` or :c:func:`yices_reset`.



Value of a Term in a Model
--------------------------

The following functions compute the value of a term in a model. For
terms of atomic types, the value can be extracted directly. Non-atomic
valued (i.e., tuples or functions) can be extracted by traversing the
model's DAG.

Many functions in this section attempt to evaluate a term *t* in a
model. If the value can't be computed, these functions return -1 and
report one of the following errors:

   - If *t* is not a valid term:
 
     -- error code: :c:enum:`INVALID_TERM`

     -- term1 := *t*

   - If *t*'s value is not defined in the model:

     -- error code: :c:enum:`EVAL_UNKNOWN_TERM`

   - If *t* contains free variables:

     -- error code :c:enum:`EVAL_FREEVAR_IN_TERM`

   - If *t* contains quantifiers:

     -- error code :c:enum:`EVAL_QUANTIFIER`

   - If *t* contains lambda terms:

     -- error code :c:enum:`EVAL_LAMBDA`

   - If the evaluation fails for other reasons:

     -- error code :c:enum:`EVAL_FAILED`

Other error codes are possible, depending on the function.



Atomic Values
.............

The following functions return the value of an atomic term.

.. c:function:: int32_t yices_get_bool_value(model_t *mdl, term_t t, int32_t *val)

   Value of a Boolean term.

   This function stores the value of term *t* in *mdl* in variable
   *\*val* as either 0 (for false) or 1 (for true).

   If *t*'s value can't be computed or if *t* is not a Boolean term, the function
   leaves *\*val* unchanged, updates the error report, and returns -1. Otherwise,
   it returns 0.

   **Error report**

   - if *t* is not a Boolean term:

     -- error code: :c:enum:`TYPE_MISMATCH`

     -- term1 := *t*
 
     -- type1 := Bool type

 
.. c:function:: int32_t yices_get_int32_value(model_t *mdl, term_t t, int32_t *val)

   Value of an integer (32 bits).

   This function stores the value of *t* in model *mdl* in variable
   *\*val*. It fails and returns -1 if *t*'s value can't be computed,
   if it is not an integer, or if it is too large or too small to be
   represented as a 32bit signed integer.

   **Error report**

   - If *t* is not an arithmetic term:

     -- error code: :c:enum:`ARITHTERM_REQUIRED`

     -- term1 := *t*

   - If *t*'s value is not an integer or does not fit in 32 bits:

     -- error code: :c:enum:`EVAL_OVERFLOW`


.. c:function:: int32_t yices_get_int64_value(model_t *mdl, term_t t, int64_t *val)

   Value as an integer (64 bits).

   This function is similar to :c:func:`yices_get_int64_value` but it succeeds if *t*'s
   value can be represented as a 64bit signed integer.

.. c:function:: int32_t yices_get_rational32_value(model_t *mdl, term_t t, int32_t *num, uint32_t *den)

   Value as a rational (32 bits).

   This function computes the value of *t* in *mdl* and returns it as
   a rational number.  The numerator is stored in *\*num* and the
   denominator is stored in *\*den*. If *t*'s value can't be computed
   or does not fit in this representation, the function returns -1 and
   leaves both *\*num* and *\*den* unchanged.

   **Error report**
  
   - If *t* is not an arithmetic term:

     -- error code: :c:enum:`ARITHTERM_REQUIRED`

     -- term1 := *t*

   - If *t*'s value can't be represented as a 32bit numerator divided by a 32bit numerator:

     -- error code: :c:enum:`EVAL_OVERFLOW`


.. c:function:: int32_t yices_get_rational64_value(model_t *mdl, term_t t, int64_t *num, uint64_t *den)

   Value as a rational (64 bits).

   This function is similar to :c:func:`yices_get_rational32_value`
   except that it uses a 64bit numerator and a 64bit denominator.

.. c:function:: int32_t yices_get_double_value(model_t *mdl, term_t t, double *val)

   Value as a floating-point number.

   This function stores the value of *t* in *mdl* in the
   floating-point variable *\*val*.  It fails (and returns -1) if
   *t*'s value can't be computed or if *t* is not an arithmetic
   term. It returns 0 otherwise.

    **Error report**
  
   - If *t* is not an arithmetic term:

     -- error code: :c:enum:`ARITHTERM_REQUIRED`

     -- term1 := *t*


.. c:function:: int32_t yices_get_mpz_value(model_t *mdl, term_t t, mpz_t val)

   Value as a GMP integer.

   This function store *t*'s value in the GMP integer *val*. The
   variable *val* must be initialized (see the `GMP
   <http://gmplib.org>`_ documentation). This function fails if *t*'s
   value can't be computed or if it's not an integer.

    **Error report**
  
   - If *t* is not an arithmetic term:

     -- error code: :c:enum:`ARITHTERM_REQUIRED`

     -- term1 := *t*

   - If *t*'s value is not an integer

     -- error code: :c:enum:`EVAL_OVERFLOW`

   **Note**

   This function is not declared unless you include :file:`gmp.h`
   before :file:`yices.h` in your code, as in::

         #include <gmp.h>
         #include <yices.h>


.. c:function:: int32_t yices_get_mpq_value(model_t *mdl, term_t t, mpq_t val)

   Value as a GMP rational.

   This function store *t*'s value in the GMP rational *val*. The
   variable *val* must be initialized (see the `GMP
   <http://gmplib.org>`_ documentation). This function fails if *t*'s
   value can't be computed or if *t* is not an arithmetic term.

   **Error report**

   - If *t* is not an arithmetic term:

     -- error code: :c:enum:`ARITHTERM_REQUIRED`

     -- term1 := *t*

   **Note**

   Like :c:func:`yices_get_mpz_value`, this function is declared if
   header file :file:`gmp.h` is included before :file:`yices.h`.

.. c:function:: int32_t yices_get_bv_value(model_t *mdl, term_t t, int32_t val[])

   Value of a bitvector term.

   This function computes *t*'s value in *mdl* and stores it in array
   *val*. The value is returned using the little-endian
   convention: the least significant bit is stored in *val[0]* and the
   most significant bit is stored in *val[n-1]* (where *n* is the
   number of bits). The array *val* must be large enough to store
   these *n* bits.

   The number of bits in *t* can be found by calling :c:func:`yices_term_bitsize`.

   The function fails if *t*'s value can't be computed or if *t* is
   not a bitvector term. It leaves *val* unchanged and returns -1 in
   this case. Otherwise, it returns 0.

   **Error report**

   - If *t* is not a bitvector term:

     -- error code: :c:enum:`BITVECTOR_REQUIRED`

     -- term1 := *t*.

.. c:function:: int32_t yices_get_scalar_value(model_t *mdl, term_t t, int32_t *val)

   Value of a scalar or uninterpreted term.

   The value of *t* is returned as an integer index in *\*val*. The index has the same
   meaning as in function :c:func:`yices_constant`:

   - If *t* has type *tau* and *tau* is a scalar type of cardinality *n* then
     *\*val* is an integer between 0 and *n-1*.

   - If *t* has an uninterpreted type, then the returned index can be
     any non-negative integer.

   The returned index is a unique identifier. If two terms *t1* and *t2* are not
   equal in the model *mdl* then their values are distinct integer indices.

   The function returns -1 if there's an error or 0 otherwise.

   **Error report**

   - If *t* does not have a scalar or uninterpreted type:

     -- error code: :c:enum:`SCALAR_TERM_REQUIRED`

     -- term1 := *t*



General Values
..............

The preceding functions are sufficient to extract atomic values from a
model, but the value of a term may be a tuple or a function. To deal
with the general case, Yices provides functions to access values as
nodes in a DAG. Function :c:func:`yices_get_value` returns a node
descriptor and the value can be constructed by exploring the DAG
rooted at this node.

Within a model, each node has an integer identifier and a tag that
specifies the node type. All DAG-exploration functions store this
information in a record of type :c:type:`yval_t` defined as follows::

   typedef struct yval_s {
     int32_t node_id;
     yval_tag_t node_tag;
   } yval_t;

Distinct nodes in a model have distinct node_ids. The type
:c:type:`yval_tag_t` lists the possible tags of a node.

Leaf nodes represent atomic values. They can have the following tags:

   - :c:enum:`YVAL_BOOL`: Boolean value

   - :c:enum:`YVAL_RATIONAL`: Rational or integer constants

   - :c:enum:`YVAL_BV`: Bitvector constant

   - :c:enum:`YVAL_SCALAR`: Constants of scalar or uninterpreted type

The following tags are used for non-leaf nodes:

   - :c:enum:`YVAL_TUPLE`: Constant tuple

   - :c:enum:`YVAL_FUNCTION`: Function descriptor

   - :c:enum:`YVAL_MAPPING`: Mapping

A node of tag :c:enum:`YVAL_TUPLE` has *n* children nodes, each
representing the value of a tuple component.  For example, tuple *(1,
true, 0b00)* is represented by a node with three children. The first
child is an atomic node with tag :c:enum:`YVAL_RATIONAL` and value *1*;
the second child has tag :c:enum:`YVAL_BOOL` and value *true*; and
the third child has tag :c:enum:`YVAL_BV` and value *0b00*.

A node of tag :c:enum:`YVAL_FUNCTION` represents a function. In a
model, all functions have a simple form. They are defined by a finite
enumeration of mappings that specify the function value at distinct
points in its domain, and a default value for all other points in the
domain. Each mapping in the enumeration is represented by a node of
tag :c:enum:`YVAL_MAPPING`.  For a function *f* with *n* arguments, a
mapping is a tuple of *n+1* nodes (written [ k\ |_1| |...| k\ |_n|
|->| v ]).  The *n* nodes k\ |_1| |...| k\ |_n| define a point in
*f*'s domain, and the value of *f* at this point is represented by
node *v*.

For example, consider the function *f* such that:

.. code-block:: none

   f(0, 0) = 0
   f(3, 1) = 1
   f(x, y) = -2 in all other cases.

Then the node that represents this function has three children. Two
children are mapping nodes for [ 0, 0 |->| 0 ] and [ 3, 1 |->| 1 ], and
the third child is an atomic node representing the default value -2. 



.. c:function:: int32_t yices_get_value(model_t *mdl, term_t t, yval_t *val)

   Value as a node reference.

   This function evaluates *t* in model *mdl*. If this succeeds, it
   stores a node descriptor for *t*'s value in the record *\*val*:

    - *val->node_id* contains the node id

    - *val->node_tag* contains the tag

   The function returns 0 in this case.

   If *t*'s evaluation fails, the function returns -1 and
   leaves *\*val* unchanged.

The following functions provide more information about the node and give
access the node's value (if it is a leaf node) or to its children (if it
is not a leaf node).

.. c:function:: int32_t yices_val_is_int32(model_t *mdl, const yval_t *v)

   Checks whether a node's value is a signed 32bit integer.

   This function returns true (i.e., 1) if *v->node_tag* is
   :c:enum:`YVAL_RATIONAL` and the node value is an integer that can
   be represented using 32 bits. It returns false (i.e., 0) if the tag
   is not :c:enum:`YVAL_RATIONAL` or if the value does not fit into a
   signed 32bit integer.

   See also :c:func:`yices_val_get_int32`.

.. c:function:: int32_t yices_val_is_int64(model_t *mdl, const yval_t *v)

   Checks whether a node's value is a signed 64bit integer.

   This function is similar to :c:func:`yices_val_is_int32` except that it
   returns true if the node has tag :c:enum:`YVAL_RATIONAL` and its value
   is an integer that can be represented using 64 bits.

   See also :c:func:`yices_val_get_int64`.

.. c:function:: int32_t yices_val_is_rational32(model_t *mdl, const yval_t *v)
 
   Checks whether a node's value is a 32bit rational.

   This function returns true if the node described by *\*v* has tag
   :c:enum:`YVAL_RATIONAL` and if its value can be written as a 32bit
   signed numerator divided by a 32bit unsigned denominator. If returns false otherwise.

   See also :c:func:`yices_val_get_rational32`.

.. c:function:: int32_t yices_val_is_rational64(model_t *mdl, const yval_t *v)

   Checks whether a node's value is a 64bit rational.

   This function returns true if the node described by *\*v* has tag
   :c:enum:`YVAL_RATIONAL` and if its value can be written as a 64bit
   signed numerator divided by a 64bit unsigned denominator. If returns false otherwise.

   See also :c:func:`yices_val_get_rational64`.

.. c:function:: int32_t yices_val_is_integer(model_t *mdl, const yval_t *v)

   Checks whether a node's value is an integer.

   This function returns true if the node described by *\*v* has tag
   :c:enum:`YVAL_RATIONAL` and the node's value is an integer. It
   returns false otherwise.

   See also :c:func:`yices_val_get_mpz`.

.. c:function:: uint32_t yices_val_bitsize(model_t *mdl, const yval_t *v)

   Number of bits in a bitvector constant node.

   If the node described by *\*v* has tag :c:enum:`YVAL_BV`, then this function 
   returns the number of bits in the node's value. Otherwise, it returns 0.

   See also :c:func:`yices_val_get_bv`.

.. c:function:: uint32_t yices_val_tuple_arity(model_t *mdl, const yval_t *v)

   Number of components in a tuple node.

   If the node described by *\*v* has tag :c:enum:`YVAL_TUPLE`, then
   this function returns the number of components in the tuple (i.e.,
   the number of children of the node). It returns 0 otherwise.

   See also :c:func:`yices_val_expand_tuple`.

.. c:function:: uint32_t yices_val_mapping_arity(model_t *mdl, const yval_t *v)

   Arity of a mapping node.

   If the node described by *\*v* has tag :c:enum:`YVAL_MAPPING`, then
   this function returns the node's arity (i.e, if the node stores a
   mapping [ k\ |_1| |...| k\ |_n| |->| v ], then the function returrns
   *n*). Otherwise, it returns 0.

   See also :c:func:`yices_val_expand_mapping`.

.. c:function:: int32_t yices_val_get_bool(model_t *mdl, const yval_t *v, int32_t *val)

   Value of a Boolean node.

.. c:function:: int32_t yices_val_get_int32(model_t *mdl, const yval_t *v, int32_t *val)

   Value of an integer node (32 bits).

.. c:function:: int32_t yices_val_get_int64(model_t *mdl, const yval_t *v, int64_t *val)

   Value of an integer node (64 bits).

.. c:function:: int32_t yices_val_get_rational32(model_t *mdl, const yval_t *v, int32_t *num, uint32_t *den)

   Value of a rational node (32 bits).

.. c:function:: int32_t yices_val_get_rational64(model_t *mdl, const yval_t *v, int64_t *num, uint64_t *den)

   Value of a rational node (64 bits).

.. c:function:: int32_t yices_val_get_double(model_t *mdl, const yval_t *v, double *val)

   Node value as a floating-point number.

.. c:function:: int32_t yices_val_get_mpz(model_t *mdl, const yval_t *v, mpz_t val)

   Node value as a GMP integer.

.. c:function:: int32_t yices_val_get_mpq(model_t *mdl, const yval_t *v, mpq_t val)

   Node value as a GMP rational.

.. c:function:: int32_t yices_val_get_bv(model_t *mdl, const yval_t *v, int32_t val[])

   Value of a bitvector node.

.. c:function:: int32_t yices_val_get_scalar(model_t *mdl, const yval_t *v, int32_t *val, type_t *tau)

   Value of a scalar node.

.. c:function:: int32_t yices_val_expand_tuple(model_t *mdl, const yval_t *v, yval_t child[])

   Components of a tuple node.

.. c:function:: int32_t yices_val_expand_function(model_t *mdl, const yval_t *f, yval_t *def, yval_vector_t *v)

   Components of a function node.

.. c:function:: int32_t yices_val_expand_mapping(model_t *mdl, const yval_t *m, yval_t tup[], yval_t *val)

   Components of a mapping node.


Values as Terms
...............

.. c:function:: term_t yices_get_value_as_term(model_t *mdl, term_t t)

.. c:function:: int32_t yices_term_array_value(model_t *mdl, uint32_t n, const term_t a[], term_t b[])



Implicants and Model Generalization
-----------------------------------

.. c:function:: int32_t yices_implicant_for_formula(model_t *mdl, term_t t, term_vector_t *v)

.. c:function:: int32_t yices_implicant_for_formulas(model_t *mdl, uint32_t n, const term_t a[], term_vector_t *v)

.. c:function:: int32_t yices_generalize_model(model_t *mdl, term_t t, uint32_t nelims, const term_t elim[], yices_gen_mode_t mode, term_vector_t *v)

.. c:function:: int32_t yices_generalize_model_array(model_t *mdl, uint32_t n, const term_t a[], uint32_t nelims, const term_t elim[], yices_gen_mode_t mode, term_vector_t *v)

