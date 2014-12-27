:tocdepth: 2

.. highlight:: c

.. _vectors:

Vectors
=======

Several functions in the API return a set of terms, types, or value
descriptors in a vector object. The vector structures are defined in
:file:`yices_types.h` and explained in :ref:`api_types`.

Before calling a function that fills in a vector *v*, the vector must
be initialized. When the vector is no longer used, it must be deleted
to avoid memory leaks.  It is also possible to empty the vector using
a reset function.

The following code fragment illustrates the typical use pattern for a
term vector. The pattern is the same for the other types of vectors::

  term_vector_t v;

  // initialize v
  yices_init_term_vector(&v);

  // call a function that fills in vector v
  yices_implicant_for_formula(mdl, t, &v);

  // the number of elements returned is v.size
  // the elements themselves are stored in v.data[0 ... v.size-1]
  // so we can scan them like this
  for (i=0; i<v.size; i++) {
     // do something with v.data[i]
  }
  
  // delete v
  yices_delete_term_vector(&v);

.. note:: 

   Unlike the data structures that are internal to Yices (e.g.,
   contexts and models), a vector *v* is not freed by a call to
   :c:func:`yices_exit` or :c:func:`yices_reset`.

The operations for initializing, deleting, and resetting vectors are
listed in the next sections.


Type Vectors 
-------------

.. c:function:: void yices_init_type_vector(type_vector_t* v)

   Initialize type vector *v*. This allocates an array *v->data* with a default
   capacity and sets *v->size* to 0.

.. c:function:: void yices_reset_type_vector(type_vector_t* v)

   Reset type vector *v*. This sets *v->size* to 0.

.. c:function:: void yices_delete_type_vector(type_vector_t* v)

   Delete type vector *v*. This frees array *v->data*.


Term Vectors
------------

.. c:function:: void yices_init_term_vector(term_vector_t* v)

   Initialize term vector *v*. This allocates an array *v->data* with a default
   capacity and sets *v->size* to 0.

.. c:function:: void yices_reset_term_vector(term_vector_t* v)

   Reset term vector *v*. This sets *v->size* to 0.

.. c:function:: void yices_delete_term_vector(term_vector_t* v)

   Delete term vector *v*. This frees array *v->data*.


Vectors of Node Descriptors
---------------------------

.. c:function:: void yices_init_yval_vector(yval_vector_t* v)

   Initialize vector *v*. This allocates an array *v->data* with a default
   capacity and sets *v->size* to 0.

.. c:function:: void yices_reset_yval_vector(yval_vector_t* v)

   Reset vector *v*. This sets *v->size* to 0.

.. c:function:: void yices_delete_yval_vector(yval_vector_t* v)

   Delete vector *v*. This frees array *v->data*.

