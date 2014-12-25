.. highlight:: c

.. _global_initialization:

Global Initialization and Cleanup
=================================

.. c:function:: void yices_init(void)

   Global initialization. This function must be called before anything
   else to initialize Yices's internal data structure.

.. c:function:: void yices_exit(void)

   This function deletes all internal data structures allocated by
   Yices (including all contexts, models, configuration and parameter
   records). It must be called when the API is no longer used to
   avoid memory leaks.

.. c:function:: void yices_reset(void)

   Full reset. This function deletes all the terms and types defined
   in Yices and resets the symbol tables. It also deletes all
   contexts, models, configuration descriptors, and other records
   allocated in Yices.
