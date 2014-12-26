.. highlight:: c

.. _vectors:

Operations on Vectors
=====================

Several functions in the API return arrays of terms, types, or value
descriptors in a vector object. The vector structures are defined in
:file:`yices_types.h` and explained in :ref:`api_types`.

Before calling any function that fills in a vector ``v``. The vector
must be initialized using a function ``yices_init_.._vector``.  When
the vector is no longer used, it must be deleted by a call to a
function ``yices_delete_.._vector``. It is also possible to empty the
vector using function ``yices_reset_.._vector``

A typical use pattern is then as follows::

  term_vector_t v;

  yices_init_term_vector(&v);

  // call a function that fills in vector v
  yices_implicant_for_formula(mdl, t, &v);

  // the number of elements returned is v.size
  // the elements themselves are stored in v.data[0 ... v.size-1]
  // so we can scan them like this
  for (i=0; i<v.size; i++) {
     // do something with v.data[i]
  }
  
  yices_delete_term_vector(&v);


Type Vectors
------------

.. c:function:: void yices_init_type_vector(type_vector_t *v)

   Initialize type vector *v*. This allocates an array *v->data* with a default
   capacity and sets *v->size* to 0.

.. c:function:: void yices_reset_type_vector(type_vector_t *v)

   Reset type vector *v*. This sets *v->size* to 0.

.. c:function:: void yices_delete_type_vector(type_vector_t *v)

   Delete type vector *v*. This frees array *v->data*.


Term Vectors
------------

.. c:function:: void yices_init_term_vector(term_vector_t *v)

   Initialize term vector *v*. This allocates an array *v->data* with a default
   capacity and sets *v->size* to 0.

.. c:function:: void yices_reset_term_vector(term_vector_t *v)

   Reset term vector *v*. This sets *v->size* to 0.

.. c:function:: void yices_delete_term_vector(term_vector_t *v)

   Delete term vector *v*. This frees array *v->data*.


Vectors of Node Descriptors
---------------------------

.. c:function:: void yices_init_yval_vector(yval_vector_t *v)

   Initialize vector *v*. This allocates an array *v->data* with a default
   capacity and sets *v->size* to 0.

.. c:function:: void yices_reset_yval_vector(yval_vector_t *v)

   Reset vector *v*. This sets *v->size* to 0.

.. c:function:: void yices_delete_yval_vector(yval_vector_t *v)

   Delete vector *v*. This frees array *v->data*.

