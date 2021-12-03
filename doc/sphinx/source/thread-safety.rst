:tocdepth: 2

.. highlight:: c

.. _thread_safe:

Thread-Safe API
===============

The Yices library is not re-entrrant by default, but it can be compiled to
be re-entrant if Yices is configured with option ``--thread-safety``.

The following function can be called to determine whether the library
was compiled with this option or not.

.. c:function:: int32_t yices_is_thread_safe(void)

   Check whether the Yices library is re-entrant.

   This function indicates whether the Yices library you are linking
   against was built with optoin ``--thread-safety``. 
   It returns 1 for Yes and 0 for No.


If Yices is compiled with this option, it is possible to use the library in
multi-threaded applications.  All calls to API functions that create
terms or types are protected by a global lock, but it is possible to
operate on separate contexts and models in parallel. In particular,
distinct threads can call :c:func:`yices_check_context` on different
contexts in parallel without locking.

You still have to ensure that distinct threads do not operate on the same
context or model at the same time.

