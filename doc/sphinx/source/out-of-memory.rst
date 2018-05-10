.. highlight:: c

.. _out_of_memory:

Catching "Out of Memory" Errors
===============================

Handling "Out of Memory" errors is tricky for Yices. When memory
cannot be allocated, the internal data structures maintained by Yices
may be left in an inconsistent state, and there is little one can do
to recover from such a state.

When memory allocation fails, the default behavior of the Yices
library is to print an error message on ``stderr`` and then call
``exit(YICES_EXIT_OUT_OF_MEMORY)``.  This kills the whole process.

Since Yices 2.4.2, it is possible to change this behavior. One can
register a callback function to be invoked if Yices runs out or
memory. The callback function is called when memory allocation fails
and can do something less brutal than killing the process.

To install an out-of-memory callback, use the following function:

.. c:function:: void yices_set_out_of_mem_callback(void (*callback)(void))

   The unique argument is a pointer to the callback function. This
   function takes no argument and returns nothing.


The code that handles out-of-memory errors stores the function pointer in a
global variable. If memory allocation fails, the following function is called::

   void out_of_memory(void) {
     if (__out_of_mem_callback != NULL) {
        __out_of_mem_callback();
     } else {
       fprintf(stderr, "Out of memory\n");
     }
     exit(YICES_EXIT_OUT_OF_MEMORY);
   }

If there's no callback, then Yices kills the whole process as
mentioned before, otherwise, Yices invokes the callback function. This
function is not expected to return. If it does, Yices will call
``exit``.


.. warning::

   The callback function must not make any call to the Yices API. Even
   a call to :c:func:`yices_exit` could cause a segmentation fault.


.. note::

   Yices depends on the GMP library, which also makes use of ``malloc``
   and may also call ``exit`` if ``malloc`` fails. Consult the GMP
   documentation if you want to also intercept out-of-memory errors
   triggered by GMP.
