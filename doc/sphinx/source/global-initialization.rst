.. highlight:: c

.. _global_initialization:

Global Initialization and Cleanup
=================================

.. c:function:: void yices_init(void)

   Global initialization.

   This function must be called before anything else to initialize
   Yices's internal data structures.

.. c:function:: void yices_exit(void)

   Global cleanup.

   This function deletes all internal data structures allocated by
   Yices (including all contexts, models, configuration and parameter
   records). It must be called when the API is no longer used to
   avoid memory leaks.

.. c:function:: void yices_reset(void)

   Full reset.

   This function deletes all the terms and types defined in Yices and
   resets the symbol tables. It also deletes all contexts, models,
   configuration descriptors, and other records allocated in Yices.


.. c:function:: void yices_free_string(char *s)

   Frees a string *s* returned by Yices.

   Several API functions build and return a character string that is
   allocated by Yices. To avoid memory leaks, this string must be
   freed when it is no longer used by calling this function.

   .. note::

      The strings returned by Yices are not automatically freed by functions
      :c:func:`yices_exit` or :c:func:`yices_reset`.

