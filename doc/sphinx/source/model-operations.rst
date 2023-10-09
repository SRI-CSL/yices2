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

   The context's status must be either :c:enum:`SMT_STATUS_SAT` or :c:enum:`SMT_STATUS_UNKNOWN`.

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

   - if *ctx*'s status is not :c:enum:`SMT_STATUS_SAT` or :c:enum:`SMT_STATUS_UNKNOWN`

     -- error code: :c:enum:`CTX_INVALID_OPERATION`

   **Note**

   The returned model captures a snapshot of the context's current
   state. Future operations on *ctx* (including deleting or resetting
   *ctx*) do not change the model.


.. c:function:: model_t* yices_model_from_map(uint32_t n, const term_t var[], const term_t map[])

   Builds a model from a term-to-term mapping.

   **Parameters**

   - *n*: number of terms in arrays *var* and *map*

   - *var*: array of *n* uninterpreted terms

   - *map*: array of *n* constant terms

   The two arrays *var* and *map* define the mapping. Every element of
   array *var* must be an uninterpreted term; every element of array
   *map* must be a constant term. The constant *map[i]* specifies the
   value of *var[i]* in the resulting model. There must not be
   duplicates in array *var*, and the type of term *map[i]* must be a
   subtype of *var[i]*'s type.

   This function returns :c:macro:`NULL` if something goes wrong. It
   allocates and creates a model otherwise, and returns a pointer to
   this model. When the model is no longer used, it must be deleted
   by calling :c:func:`yices_free_model`.

   Currently, function types are not supported. Every term in *map[i]*
   must either be an atomic constant, or a tuple of atomic constants,
   or a tuple of tuples of constants, and so forth. The term *var[i]*
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


.. c:function::  void yices_model_collect_defined_terms(model_t *mdl, term_vector_t *v)

   Collect all the uninterpreted terms that have a value in *mdl* and store them in
   vector *v*.

   - *v* must be an initialized term vector (see :c:func:`yices_init_term_vector`).

   The set of terms is returned as follows:

   - *v->size* is the number of uninterpreted terms

   - *v->data[0 ... v->size - 1]* contains the terms

   Here is an example use of this function::

      yices_assert_formula(ctx, f);
      if (yices_check(ctx, ...) == SMT_STATUS_SAT) {
         term_vector_t v;
         model_t *m = yices_get_model(ctx, true);
	 yices_init_term_vector(&v);
	 yices_model_collect_defined_terms(m, &v);
	 ....
      }

   At the end of this code fragment, vector *v* typically contains all
   the uninterpreted terms that occur in *f*. In some rare cases,
   terms may be eliminated during preprocessing and assertion simplifications.
   These terms will not be defined in model *m* and will not be stored in
   vector *v*.


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
values (i.e., tuples or functions) can be extracted by traversing the
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

.. c:function:: int32_t yices_get_bool_value(model_t *mdl, term_t t, int32_t *val)

   Value of a Boolean term.

   This function computes the value of term *t* in *mdl* and stores
   the result in *\*val* as either 0 (for false) or 1 (for true).

   If *t*'s value can't be computed or if *t* is not a Boolean term, the function
   leaves *\*val* unchanged, updates the error report, and returns -1. Otherwise,
   it returns 0.

   **Error report**

   - if *t* is not a Boolean term:

     -- error code: :c:enum:`TYPE_MISMATCH`

     -- term1 := *t*

     -- type1 := Bool type

   See also :c:func:`yices_formula_true_in_model` and :c:func:`yices_formulas_true_in_model`.


.. c:function:: int32_t yices_get_int32_value(model_t *mdl, term_t t, int32_t *val)

   Value of an integer (32 bits).

   This function computes the value of *t* in model *mdl* and stores
   it in *\*val*. It fails and returns -1 if *t*'s value can't be
   computed, if it is not an integer, or if it is too large or too
   small to be represented as a signed 32bit integer.

   **Error report**

   - If *t* is not an arithmetic term:

     -- error code: :c:enum:`ARITHTERM_REQUIRED`

     -- term1 := *t*

   - If *t*'s value is not an integer or does not fit in 32 bits:

     -- error code: :c:enum:`EVAL_OVERFLOW`


.. c:function:: int32_t yices_get_int64_value(model_t *mdl, term_t t, int64_t *val)

   Value as an integer (64 bits).

   This function is similar to :c:func:`yices_get_int32_value` but it succeeds if *t*'s
   value can be represented as a signed 64bit integer.


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

   This function computes the value of *t* in *mdl*, converts it to a
   floating-point number, and stores the result in variable *\*val*.
   It fails (and returns -1) if *t*'s value can't be computed or if
   *t* is not an arithmetic term. It returns 0 otherwise.

    **Error report**

   - If *t* is not an arithmetic term:

     -- error code: :c:enum:`ARITHTERM_REQUIRED`

     -- term1 := *t*


.. c:function:: int32_t yices_get_mpz_value(model_t *mdl, term_t t, mpz_t val)

   Value as a GMP integer.

   This function stores *t*'s value in the GMP integer *val*. The
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

   This function stores *t*'s value in the GMP rational *val*. The
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


.. c:function:: int32_t yices_get_algebraic_number_value(model_t *mdl, term_t t, lp_algebraic_number_t *a)

   Value as an algebraic number.

   This function stores *t*'s value in the structure *\*a*.  The type `lp_algebraic_number_t` is defined in the `libpoly
   <https://github.com/SRI-CSL/libpoly>`_ library, and represents an
   algebraic number.

   This function fails if *t*'s value cannot be computed, or if it is not an algebraic number.
   It will also fail if the Yices library was compiled without support for MCSAT (cf. :ref:`mcsat_support`).

   **Error report**

   - If MCSAT is not supported:

     -- error code: :c:enum:`EVAL_NOT_SUPPORTED`

   - If *t* is not an arithmetic term:

     -- error code: :c:enum:`ARITH_TERM_REQUIRED`

   - If *t* is an arithmetic term and has a rational value (i.e., not
     an algebraic number):

     -- error code: :c:enum:`EVAL_CONVERSION_FAILED`

   **Note**

   This function is not declared unless you include the libpoly header
   :file:`algebraic_number.h` before :file:`yices.h` in your code::

         #include <poly/algebraic_number.h>
         #include <yices.h>


   **Example**

   The following code fragment prints the value of a term *t*, using
   libpoly's functions. This works if *t* has an algebraic value in model *mdl*::

     static void show_algebraic_value(model_t *mdl, term_t t) {
       lp_algebraic_number_t n;
       int32_t code;

       code = yices_get_algebraic_number_value(mdl, t, &n);
       if (code < 0) {
         yices_print_error(stderr);
       } else {
         lp_algebraic_number_print(&n, stdout);
         fflush(stdout);
         lp_algebraic_number_destruct(&n);
       }
     }


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

   The value of *t* is returned as an integer index in *\*val*. This index has the same
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



Value of Formulas
.................

.. c:function:: int32_t yices_formula_true_in_model(model_t* mdl, term_t f)

   Checks whether a formula is true in a model.

   This function checks whether *f* is true in *mdl*. It returns 1 if *f* is true in the model,
   0 if *f* is false in the model, or -1 if *f* is not a Boolean term or if it can't be evaluated.

   This function reports the same error codes as :c:func:`yices_get_bool_value`.

.. c:function:: int32_t yices_formulas_true_in_model(model_t* mdl, uint32_t n, const term_t f[])

   Checks whether an array of formulas is true in a model.

   This function checks whether the formulas *f[0]* to *f[n-1]* are all true in *mdl*. It returns
   1 if all *f[i]*s are true, 0 if an *f[i]* is false, or -1 of an *f[i]* is not Boolean or can't be
   evaluated.

   This function reports the same errors as :c:func:`yices_get_bool_value`.

   It is more efficient to call this function that to call
   :c:func:`yices_formula_true_in_model` *n* times.



General Values
..............

The preceding functions are sufficient to extract atomic values from a
model, but the value of a term may be a tuple or a function. To deal
with the general case, Yices provides functions to access values by
exploring the model DAG. Function :c:func:`yices_get_value` evaluates
a term and returns a node descriptor from which the term value can be
constructed.

Within a model, each node has an integer identifier and a tag that
specifies the node's type. All DAG-exploration functions store this
information in records of type :c:type:`yval_t` defined as follows::

   typedef struct yval_s {
     int32_t node_id;
     yval_tag_t node_tag;
   } yval_t;

Distinct nodes in a model have distinct node_ids.

The type :c:type:`yval_tag_t` lists the possible tags of a node.
Leaf nodes represent atomic values. They can have the following tags:

   - :c:enum:`YVAL_BOOL`: Boolean value

   - :c:enum:`YVAL_RATIONAL`: Rational or integer constant

   - :c:enum:`YVAL_ALGEBRAIC`: Algebraic number

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
points in its domain, and a default value for all other points. Each
mapping in the enumeration is represented by a node of tag
:c:enum:`YVAL_MAPPING`.  For a function *f* with *n* arguments, a
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


To support partially-defined values, the following tag is also defined:

   - :c:enum:`YVAL_UNKNOWN`: Unknown value

A node with this tag may be returned as the default value of a
function *f*. In such a case, the model stores a finite list of
mappings for *f* but does not assign a value to *f* outside the points
listed in the mappings.


The DAG-exploration API includes a function that returns the node
for a term value, functions that provide information about a node,
functions that return the value of leaf nodes, and functions that return
the children of non-leaf nodes.

.. c:function:: int32_t yices_get_value(model_t *mdl, term_t t, yval_t *val)

   Value as a node reference.

   This function evaluates *t* in model *mdl*. If this succeeds, it
   stores a node descriptor for *t*'s value in the record *\*val*:

    - *val->node_id* contains the node id

    - *val->node_tag* contains the tag

   The function returns 0 in this case.

   If *t*'s evaluation fails, the function returns -1 and
   leaves *\*val* unchanged.


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

.. c:function:: uint32_t yices_val_function_arity(model_t *mdl, const yval_t *v)

   Arity of a function node.

   If the node described by *\*v* has tag :c:enum:`YVAL_FUNCTION`, then this
   function returns the function's arity (i.e., number of parameters to the function).
   If the node has another tag, this function returns 0.


.. c:function:: uint32_t yices_val_mapping_arity(model_t *mdl, const yval_t *v)

   Arity of a mapping node.

   If the node described by *\*v* has tag :c:enum:`YVAL_MAPPING`, then
   this function returns the node's arity (i.e, if the node stores a
   mapping [ k\ |_1| |...| k\ |_n| |->| v ], then the function returns
   *n*). Otherwise, it returns 0.

   See also :c:func:`yices_val_expand_mapping`.

.. c:function:: type_t yices_val_function_type(model_t *mdl, const yval_t *v)

   Type of a function node.

   If the node described by *\*v* has tag :c:enum:`YVAL_FUNCTION`, then
   this function returns the type of the node. This is a function type.
   Otherwise, the function returns -1 (i.e., :c:enum:`NULL_TYPE`).

   **Error report**

   - If the node is not a function

     -- error code: :c:enum:`YVAL_INVALID_OP`


.. c:function:: int32_t yices_val_get_bool(model_t *mdl, const yval_t *v, int32_t *val)

   Value of a Boolean node.

   This function checks whether node *v* has tag
   :c:enum:`YVAL_BOOL`. If so, it stores the node's value into *\*val*
   and returns 0. Otherwise, it returns -1 and leaves *\*val*
   unchanged.

   **Error report**

   - If the node is not Boolean

     -- error code: :c:enum:`YVAL_INVALID_OP`


.. c:function:: int32_t yices_val_get_int32(model_t *mdl, const yval_t *v, int32_t *val)

   Value of an integer node (32 bits).

   This function checks whether node *v* has tag
   :c:enum:`YVAL_RATIONAL` and whether its value can be represented as
   a 32bit signed integer.  If so, it stores the node's value into
   *\*val* and returns 0. Otherwise, it returns -1 and leaves *\*val*
   unchanged.

   **Error report**

   - If the node does not have tag :c:enum:`YVAL_RATIONAL`

     -- error code: :c:enum:`YVAL_INVALID_OP`

   - If the node's value does not fit in a 32bit integer:

     -- error code: :c:enum:`YVAL_OVERFLOW`


.. c:function:: int32_t yices_val_get_int64(model_t *mdl, const yval_t *v, int64_t *val)

   Value of an integer node (64 bits).

   This function is similar to :c:func:`yices_val_get_int32` except
   that it succeeds if the node's value fits in a 64bit signed integer.

.. c:function:: int32_t yices_val_get_rational32(model_t *mdl, const yval_t *v, int32_t *num, uint32_t *den)

   Value of a rational node (32 bits).

   This function checks whether node *v* has tag
   :c:enum:`YVAL_RATIONAL` and whether its value can be represented as
   a 32bit numerator divided by a 32bit denominator.  If so, it stores
   the numerator in *\*num* and the denominator in *\*den* and returns 0.
   Otherwise, it returns -1 and leaves *\*num* and *\*den* unchanged.

   **Error report**

   - If the node does not have tag :c:enum:`YVAL_RATIONAL`

     -- error code: :c:enum:`YVAL_INVALID_OP`

   - If the node's value does not fit num/den:

     -- error code: :c:enum:`YVAL_OVERFLOW`


.. c:function:: int32_t yices_val_get_rational64(model_t *mdl, const yval_t *v, int64_t *num, uint64_t *den)

   Value of a rational node (64 bits).

   This function is similar to :c:func:`yices_val_get_rational32` except that it succeeds if the node's value
   can be represented as a 64bit numerator divided by a 64bit denominator.

.. c:function:: int32_t yices_val_get_double(model_t *mdl, const yval_t *v, double *val)

   Node value as a floating-point number.

   This function checks whether node *\*v* has tag
   :c:enum:`YVAL_RATIONAL` or :c:enum:`YVAL_ALGEBRAIC`. If so it
   converts the node's value to a double-precision floating point
   number and stores it in *\*val*.  The function returns 0 in this
   case, If *\*v* has a different tag, the function returns -1 and
   leaves *\*val* unchanged.

   **Error report**

   - If the node does not have tag :c:enum:`YVAL_RATIONAL`

     -- error code: :c:enum:`YVAL_INVALID_OP`


.. c:function:: int32_t yices_val_get_mpz(model_t *mdl, const yval_t *v, mpz_t val)

   Node value as a GMP integer.

   This function checks whether node *\*v* has tag
   :c:enum:`YVAL_RATIONAL` and if its value is an integer. If so, it
   copies the node value in the GMP integer *val* and
   returns 0. Otherwise, it leaves *val* unchanged and returns -1.

   The variable *val* must be initialized (see the `GMP
   <http://gmplib.org>`_ documentation).

   **Error report**

   - If the node does not have tag :c:enum:`YVAL_RATIONAL`

     -- error code: :c:enum:`YVAL_INVALID_OP`

   - If the node's value is not an integer:

     -- error code: :c:enum:`YVAL_OVERFLOW`

   **Note**

   This function is not declared unless you include :file:`gmp.h`
   before :file:`yices.h` in your code.


.. c:function:: int32_t yices_val_get_mpq(model_t *mdl, const yval_t *v, mpq_t val)

   Node value as a GMP rational.

   This function checks whether node *v* has tag :c:enum:`YVAL_RATIONAL`. If so,
   it copies the node's value in the GMP rational *val* and returns 0. Otherwise,
   it leaves *val* unchanged and returns -1.

   The variable *val* must be initialized (see the `GMP
   <http://gmplib.org>`_ documentation).

   **Error report**

   - If the node does not have tag :c:enum:`YVAL_RATIONAL`

     -- error code: :c:enum:`YVAL_INVALID_OP`

   **Note**

   This function is not declared unless you include :file:`gmp.h`
   before :file:`yices.h` in your code.


.. c:function:: int32_t yices_val_get_algebraic_number(model_t *mdl, const yval_t *v, lp_algebraic_number_t *a)

   Node value as an algebraic number.

   This function checks whether node *v* has tag :c:enum:`YVAL_ALGEBRAIC`. If so,
   it copies the node's value in the structure *\*a* and returns 0. Otherwise,
   it leaves the structure unchanged and returns -1.

   This function fails if the Yices library was compiled without
   support for MCSAT (cf. :ref:`mcsat_support`).

   **Error report**

   - If MCSAT is not supported:

     -- error code: :c:enum:`YVAL_NOT_SUPPORTED`

   - If MCSAT is supported but the node does not have tag :c:enum:`YVAL_ALGEBRAIC`

     -- error code: :c:enum:`YVAL_INVALID_OP`

   **Note**

   This function is not declared unless you include the libpoly header
   :file:`algebraic_number.h` before :file:`yices.h` in your code::

         #include <poly/algebraic_number.h>
         #include <yices.h>



.. c:function:: int32_t yices_val_get_bv(model_t *mdl, const yval_t *v, int32_t val[])

   Value of a bitvector node.

   This function checks whether node *v* has tag :c:enum:`YVAL_BV`. If
   so, it copies the node value into array *val* and
   returns 0. Otherwise, it leaves *val* unchanged and returns -1.

   The array *val* must be large enough to store *n* integers, where
   *n* is the number of bits in the bitvector value. The number of
   bits can be found by calling function :c:func:`yices_val_bitsize`.
   The value is returned using the little-endian convention: the
   least-significant bit is stored in *val[0]* and the most
   significant bit is in *val[n-1]*.

   **Error report**

   - If the node does not have tag :c:enum:`YVAL_BV`

     -- error code: :c:enum:`YVAL_INVALID_OP`


.. c:function:: int32_t yices_val_get_scalar(model_t *mdl, const yval_t *v, int32_t *val, type_t *tau)

   Value of a scalar node.

   This function checks whether *v* has tag :c:enum:`YVAL_SCALAR`. If
   so, it copies the node's value (an integer index) into *\*val* and
   the node's type into *\*tau*. The function returns 0 in this
   case. It returns -1 and leaves *\*val* and *\*tau* unchanged
   otherwise.

   **Error report**

   - If the node does not have tag :c:enum:`YVAL_SCALAR`

     -- error code: :c:enum:`YVAL_INVALID_OP`


.. c:function:: int32_t yices_val_expand_tuple(model_t *mdl, const yval_t *v, yval_t child[])

   Components of a tuple node.

   If node *v* has tag :c:enum:`YVAL_TUPLE`, then this function copies the node's children into
   array *child*. The array must be large enough to store all the children descriptors. The number of
   children is given by function :c:func:`yices_val_tuple_arity`. The first child is stored in
   *child[0]* and the last child is in *child[n-1]* where *n* is the node's arity.

   The function returns 0 if *v*'s tag is :c:enum:`YVAL_TUPLE` or -1 otherwise.

   **Error report**

   - If node *v* does not have tag :c:enum:`YVAL_TUPLE`

     -- error code: :c:enum:`YVAL_INVALID_OP`


.. c:function:: int32_t yices_val_expand_function(model_t *mdl, const yval_t *f, yval_t *def, yval_vector_t *v)

   Components of a function node.

   If node *f* has tag :c:enum:`YVAL_FUNCTION`, this function extracts the node's components:

   - the default node for *f* is stored in *\*def*

   - the set of mappings for *f* is copied in vector *v*

   The vector must be initialized by calling
   :c:func:`yices_init_yval_vector`. The function sets *v->size* to
   the number of mappings for *f* and it copies the mapping nodes into
   *v->data[0]* |...| *v->data[v->size-1]*. All the nodes in the
   vector have tag :c:enum:`YVAL_MAPPING` and have the same arity as
   the function node *f*.

   The function returns 0 if there's no error, or -1 if *f*'s tag is not :c:enum:`YVAL_FUNCTION`.

   **Error report**

   - If node *f* does not have tag :c:enum:`YVAL_FUNCTION`

     -- error code: :c:enum:`YVAL_INVALID_OP`


.. c:function:: int32_t yices_val_expand_mapping(model_t *mdl, const yval_t *m, yval_t tup[], yval_t *val)

   Components of a mapping node.

   This function checks whether *m* has tag :c:enum:`YVAL_MAPPING`. If
   so, it copies the node's components in array *tup* and in *val*.
   The function returns 0 in this case. It returns -1 and leaves *tup*
   and *val* unchanged otherwise.

   For a mapping [ k\ |_1| |...| k\ |_n| |->| v ], the nodes k\ |_1|
   |...| k\ |_n| are copied in *tup[0]* to *tup[n-1]*, and the node v
   is copied into *\*val*. Array *tup* must be large enough to store
   the *n* node descriptors. The arity *n* can be found by calling
   :c:func:`yices_val_mapping_arity` (or using :c:func:`yices_val_function_arity`).

   **Error report**

   - If node *m* does not have tag :c:enum:`YVAL_MAPPING`

     -- error code: :c:enum:`YVAL_INVALID_OP`


Values as Terms
...............

.. c:function:: term_t yices_get_value_as_term(model_t *mdl, term_t t)

   Value as a constant term.

   This function evaluates term *t* in model *mdl* and returns *t*'s
   value as a constant term.

   For a term *t* of atomic types, this function is equivalent to extracting *t*'s value
   then converting it to a constant:

   - If *t* is a Boolean term, the returned value is either true or false, as
     constructed by :c:func:`yices_true` or :c:func:`yices_false`.

   - If *t* is an arithmetic term, the returned value is constant term as
     constructed with :c:func:`yices_mpq`.

   - If *t* has uninterpreted or scalar type, the returned value is a constant
     term of that type as built by function :c:func:`yices_constant`.

   - If *t* is a bitvector term, the returned value is a bitvector
     constant as built with :c:func:`yices_bvconst_from_array`.

   If *t* is a tuple, then the function returns a constant tuple.

   Function types are not supported. The function fails and returns :c:enum:`NULL_TERM`
   if *t* has a function type. It also returns :c:enum:`NULL_TERM` if *t*'s value can't
   be computed.

   **Error report**

   - If *t*'s value can't be converted to a constant term:

     -- error code: :c:enum:`EVAL_CONVERSION_FAILED`

     This happens if *t* has a function type or if *t* has tuple type
     and some subterm of *t* has a function type.

.. c:function:: int32_t yices_term_array_value(model_t *mdl, uint32_t n, const term_t a[], term_t b[])

   Values as constant terms.

   This function computes the values of terms *a[0 ... n-1]*, converts these values to constant terms,
   and stores the results in array *b*.

   **Parameters**

   - *mdl*: model

   - *n*: size of arrays *a* and *b*

   - *a*: array of *n* terms

   - *b*: array to store the result as *n* constant terms.

   This function has the same behavior as calling :c:func:`yices_get_value_as_term` *n* times.
   It returns 0 if all values can be computed, or -1 if there's an error. The possible error
   codes are the same as for :c:func:`yices_get_value_as_term`.


Supports
--------

Given a term *t* and a model *M*, one may be intersted in the set of
uninterpreted terms on which the value assigned to *t* depends. We call this set a support of *t* in *M*.
For example, if *t* is the term *(ite (> x 0) (+ x z) y)* then and *x* has positive value in *M* then
the value of *t* in *M* does not depend on *y*. In this case, the support of *t* in *M* is the set *{ x, z }*.
If we have a different model *R* and *x* has a negative value in *R* then the support of *t* in *R* is
the set *{ x, y }*. In *R*, the value of *t* does not depend on *z*'s value.

The following two functions compute the support of a term or a set of terms in a model.

.. c:function:: int32_t yices_model_term_support(model_t *mdl, term_t t, term_vector_t *v)

   Get the support of *t* in *mdl*

   The function computes a support for *t*  in *mdl* and store the result in vector *v*.

   **Parameters**

   - *mdl*: model

   - *t*: term

   - *v*: term vector

   Vector *v* must be initialized by :c:func:`yices_init_term_vector`. The support set is returned in *v*
   as follows:

   - *v->size* stores the number of uninterpreted terms in the support set

   - *v0->data[0]* |...| *v->data[n-1]* store *n* distinct uninterpreted terms (where *n = v->size*).


   **Error report**

   - if *t* is not a valid term:

     -- error code: :c:enum:`INVALID_TERM`

     -- term1 := *t*



.. c:function:: int32_t yices_model_term_array_support(model_t *mdl, uint32_t n, const term_t a[], term_vector_t *v)

   Get the support of *n* terms in *mdl*

   **Parameters**

   - *mdl*: model

   - *n*: size of array *a*

   - *a*: array of *n* terms

   - *v*: term vector

   This is similar to the :c:func:`yices_model_term_support` but it computes a support for *n* terms stored in
   array *a*. The set is returned in vector *v*.



Implicants
----------

.. c:function:: int32_t yices_implicant_for_formula(model_t *mdl, term_t t, term_vector_t *v)

   Computes an implicant.

   This function constructs an implicant of *t* based on model
   *mdl*. The term *t* must be a Boolean term that's true in
   *mdl*. The implicant is a list of Boolean terms a\ |_1| |...| a\
   |_n| such that

   - a\ |_i| is a literal (atom or negation of an atom)

   - a\ |_i| is true in *mdl*

   - the conjunction (a\ |_1| |and| |...| |and| a\ |_n|) implies *t*

   The implicant is returned in vector *v*, which must be initialized by :c:func:`yices_init_term_vector`:

   - *v->size* stores the number of literals in the implicant (i.e., *n*).

   - *v->data[0]* |...| *v->data[n-1]* store the *n* literals

   The function  returns 0 if the implicant can be computed. Otherwise, it returns -1 and resets
   *v* to the empty vector (i.e., it sets *v->size* to 0).

   **Error report**

   - if *t* is not a valid term

     -- error code: :c:enum:`INVALID_TERM`

     -- term1 := *t*

   - if *t* is not a Boolean term

     -- error code: :c:enum:`TYPE_MISMATCH`

     -- term1 := *t*

     -- type1 := Bool type

   - if *t* is false in the model

     -- error code: :c:enum:`EVAL_NO_IMPLICANT`

   Other errors are possible if *t* or a subterm of *t* can't be evaluated. These are the same
   error codes as for any term-evaluation function.

.. c:function:: int32_t yices_implicant_for_formulas(model_t *mdl, uint32_t n, const term_t a[], term_vector_t *v)

   Implicant for an array of formulas.

   This function constructs an implicant for the conjunction of formulas *a[0]* |and| ... |and| *a[n-1]*.
   The result is stored in vector *v* as explained for :c:func:`yices_implicant_for_formula`. This function
   has returns 0 if the implicant can be constructed or -1 otherwise. It has the same behavior and reports
   the same errors as :c:func:`yices_implicant_for_formula`.


Model Generalization
--------------------

Given a model for a formula *F(X, Y)*, the following two functions compute a formula *G(X)* that generalizes
the model. The formula  *G(X)* satisfies two properties:

  1) *G(X)* is true in the model

  2) *G(X)* implies (exists *y* *F(x, y)*)


Yices supports two generalization methods:

  - **Generalization by substitution:** This is the simplest method. It eliminates the
    variables *Y* by replacing them by their values in the model.

  - **Generalization by projection:** This first computes an implicant of formula *F(X, Y)*
    then eliminates the *Y* variables from this implicant by projection. The projection is
    a cheap form of quantifier elimination. It is a hybrid a Fourier-Motzkin elimination
    and virtual term substitution.

The two generalization functions take a parameter that specifies the generalization method.
This parameter takes a value of type :c:type:`yices_gen_mode_t`:

  - :c:enum:`YICES_GEN_BY_SUBST` selects generalization by substitution;

  - :c:enum:`YICES_GEN_BY_PROJ` selects generalization by projection;

  - :c:enum:`YICES_GEN_DEFAULT` automatically chooses the
    generalization method based on the type of variables to
    eliminate. If any variable to eliminate is an arithmetic variable,
    then generalization by projection is used. Otherwise, the default
    is generalization by substitution.

.. c:function:: int32_t yices_generalize_model(model_t *mdl, term_t t, uint32_t nelims, const term_t elim[], yices_gen_mode_t mode, term_vector_t *v)

   Model generalization for a single formula.

   This function computes a generalization of *mdl* for formula *t*.

   **Parameters**

   - *mdl*: model

   - *t*: Boolean term that's true in *mdl*

   - *nelims*: number of variables to eliminate

   - *elim*: variables to eliminate

   - *mode*: generalization method

   - *v*: term vector to store the result

   Every term in array *elim* must be an uninterpreted term (cf. :c:func:`yices_new_uninterpreted_term`),
   of type Boolean, Real, or bitvector.

   The generalization formula *G(X)* is returned in vector *v*. The vector must be initialized
   using :c:func:`yices_init_term_vector`. *G(X)* is the conjunction of all formulas in *v*:

   - *v->size*: number of formulas returned

   - *v->data[0]* |...| *v->data[v->size-1]* contain the formulas themselves

   If *mode* is :c:enum:`YICES_GEN_BY_PROJ` then every formula in *v* is guaranteed to be a literal.

   The function returns 0 if the generalization succeeds or -1 if there's an error.

.. c:function:: int32_t yices_generalize_model_array(model_t *mdl, uint32_t n, const term_t a[], uint32_t nelims, const term_t elim[], yices_gen_mode_t mode, term_vector_t *v)

   Model generalization for an array of formulas.

   **Parameters**

   - *mdl*: model

   - *n*: number of formulas in array *a*

   - *a*: array of *n* Boolean term that are true in *mdl*

   - *nelims*: number of variables to eliminate

   - *elim*: variables to eliminate

   - *mode*: generalization method

   - *v*: term vector to store the result

   This function is equivalent to calling :c:func:`yices_generalize_model` with
   argument (*a[0]* |and| |...| |and| *a[n-1]*).

