:tocdepth: 2

.. highlight:: c

.. _model_operations:

Models
======

Model Construction
------------------

.. c:function:: model_t* yices_get_model(context_t* ctx, int32_t keep_subst)

.. c:function:: model_t* yices_model_from_map(uint32_t n, const term_t var[], const term_t map[])

.. c:function::  void yices_free_model(model_t* mdl)


Value of a Term in a Model
--------------------------

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

