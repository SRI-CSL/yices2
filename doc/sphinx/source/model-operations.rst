:tocdepth: 2

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
   (i.e. non-zero), then this function will keep track of eliminated
   variables and include their value in the model. If *keep_subst* if false 
   (i.e., zero), then the model does not include the eliminated variables.

   It is better to set *keep_susbt* to true. The only reason not to do
   it is to save the memory and computation cost of storing the
   eliminated variables and their values. This cost is usually low but
   there are exceptions.

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

   Currently, function types are not supported. Every term in *map[i]*
   must either be an atomic constant, or a tuple of atomic constants,
   or a tuple or tuples, etc. The term *var[i]* cannot have a function type.

   This function returns :c:macro:`NULL` if something goes wrong. It
   allocates and creates a model otherwise, and returns a pointer to
   this model. When the model is no longer used, it must be deleted
   by calling :c:func:`yices_free_model`.

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

The following functions give access to the value of a term in a model.

Atomic Values
.............

.. c:function:: int32_t yices_get_bool_value(model_t *mdl, term_t t, int32_t *val)

.. c:function:: int32_t yices_get_int32_value(model_t *mdl, term_t t, int32_t *val)

.. c:function:: int32_t yices_get_int64_value(model_t *mdl, term_t t, int64_t *val)

.. c:function:: int32_t yices_get_rational32_value(model_t *mdl, term_t t, int32_t *num, uint32_t *den)

.. c:function:: int32_t yices_get_rational64_value(model_t *mdl, term_t t, int64_t *num, uint64_t *den)

.. c:function:: int32_t yices_get_double_value(model_t *mdl, term_t t, double *val)

.. c:function:: int32_t yices_get_mpz_value(model_t *mdl, term_t t, mpz_t val)

.. c:function:: int32_t yices_get_mpq_value(model_t *mdl, term_t t, mpq_t val)

.. c:function:: int32_t yices_get_bv_value(model_t *mdl, term_t t, int32_t val[])

.. c:function:: int32_t yices_get_scalar_value(model_t *mdl, term_t t, int32_t *val)


General Values
..............

.. c:function:: int32_t yices_get_value(model_t *mdl, term_t t, yval_t *val)

.. c:function:: int32_t yices_val_is_int32(model_t *mdl, const yval_t *v)

.. c:function:: int32_t yices_val_is_int64(model_t *mdl, const yval_t *v)

.. c:function:: int32_t yices_val_is_rational32(model_t *mdl, const yval_t *v)

.. c:function:: int32_t yices_val_is_rational64(model_t *mdl, const yval_t *v)

.. c:function:: int32_t yices_val_is_integer(model_t *mdl, const yval_t *v)

.. c:function:: uint32_t yices_val_bitsize(model_t *mdl, const yval_t *v)

.. c:function:: uint32_t yices_val_tuple_arity(model_t *mdl, const yval_t *v)

.. c:function:: uint32_t yices_val_mapping_arity(model_t *mdl, const yval_t *v)

.. c:function:: int32_t yices_val_get_bool(model_t *mdl, const yval_t *v, int32_t *val)

.. c:function:: int32_t yices_val_get_int32(model_t *mdl, const yval_t *v, int32_t *val)

.. c:function:: int32_t yices_val_get_int64(model_t *mdl, const yval_t *v, int64_t *val)

.. c:function:: int32_t yices_val_get_rational32(model_t *mdl, const yval_t *v, int32_t *num, uint32_t *den)

.. c:function:: int32_t yices_val_get_rational64(model_t *mdl, const yval_t *v, int64_t *num, uint64_t *den)

.. c:function:: int32_t yices_val_get_double(model_t *mdl, const yval_t *v, double *val)

.. c:function:: int32_t yices_val_get_mpz(model_t *mdl, const yval_t *v, mpz_t val)

.. c:function:: int32_t yices_val_get_mpq(model_t *mdl, const yval_t *v, mpq_t val)

.. c:function:: int32_t yices_val_get_bv(model_t *mdl, const yval_t *v, int32_t val[])

.. c:function:: int32_t yices_val_get_scalar(model_t *mdl, const yval_t *v, int32_t *val, type_t *tau)

.. c:function:: int32_t yices_val_expand_tuple(model_t *mdl, const yval_t *v, yval_t child[])

.. c:function:: int32_t yices_val_expand_function(model_t *mdl, const yval_t *f, yval_t *def, yval_vector_t *v)

.. c:function:: int32_t yices_val_expand_mapping(model_t *mdl, const yval_t *m, yval_t tup[], yval_t *val)


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

