:tocdepth: 2

.. highlight:: c

.. _context_operations:

Contexts
========

Contexts are one of the most important data structures in Yices. A
context contains one or more solvers and provides functions for
manipulating assertions and for checking whether these assertions are
satisfiable. If they are, a model can be constructed from the context.

Yices allows several context to be created and manipulated
independently. The API provides functions for

- creating and configuring a context

- asserting formulas in a context

- checking whether a context is satisfiable

- building a model from a satisfiable context

- deleting a context

A context can be configured to support a push/pop mechanism, which
organizes the assertions in a stack to support incremental solving and
backtracking.



Creation and Configuration
--------------------------

The simplest way to create a context is as follows::

   context_t *ctx = yices_new_context(NULL);

This creates a new context in the default configuration. This context
includes theory solvers for linear arithmetic, bitvector,
uninterpreted functions, and arrays. The context supports the push/pop
mechanism and the arithmetic solver can handle mixed integer real
linear arithmetic.

To use a more specialized set of solvers, one can configure the
context for a specific logic. Here is an example::

   ctx_config_t *config = yices_new_config();
   yices_default_config_for_logic(config, "QF_LRA");
   context_t *ctx = yices_new_context(config);

In this case, we pass a non-NULL configuration descriptor to function
:c:func:`yices_new_context` to specify the logic we want to support.
Logics are identified by their SMT-LIB name. In this example, QF_LRA
means quantifier-free linear real arithmetic. This configuration
creates a context with a single theory solver, namely, the
simplex-based solver for linear arithmetic. As previously, this solver
supports the push/pop mechanism.

If the push and pop features are not needed, we can modify the configuration
as follows::

   ctx_config_t *config = yices_new_config();
   yices_default_config_for_logic(config, "QF_LRA");
   yices_set_config(config, "mode", "one-shot");
   context_t *ctx = yices_new_context(config);

The call to :c:func:`yices_set_config` changes the context's mode of
operation from the default (i.e., support for push and pop) to a more
restricted mode where push and pop are not supported. In this mode,
the context can use aggressive simplification and preprocessing
procedures, which can improve solver performance.


The general process to configure a context is as follows:

1) allocate a configuration descriptor by a call to :c:func:`yices_new_config`.

2) set configuration parameters by repeated calls to :c:func:`yices_set_config` or by
   calling :c:func:`yices_default_config_for_logic`.

3) create one or more contexts with this configuration by passing the descriptor to
   function :c:func:`yices_new_context`

4) delete the configuration descriptor when it is no longer needed.


Configuration parameters specify the theory solvers to use, the
arithmetic fragment, and the context's operating mode.


**Solver Combinations**

Currently the following theory solvers are available:

   ============================= =============================
    Solver name                    Theory
   ============================= =============================
    egraph                         uninterpreted functions
    array solver                   arrays + extensionality
    simplex                        linear arithmetic
    integer Floyd-Warshall (IFW)   integer difference logic
    real Floyd-Warshall (RFW)      real difference logic
    bitvector                      bitvector theory
   ============================= =============================
   

A configuration selects a subset of these solvers. Not all
combinations make sense. For example, there can be only one arithmetic
solver so it's not possible to have both a Floyd-Warshal solver and
the Simplex solver in the same context. The following table lists the
combinations of theory solvers currently supported by Yices.

   +-----------------------------------------------+
   |  Combination                                  |
   +===============================================+
   |  no solvers at all                            |
   +-----------------------------------------------+
   |  egraph alone                                 |
   +-----------------------------------------------+
   |  bitvector alone                              |
   +-----------------------------------------------+
   |  simplex alone                                |
   +-----------------------------------------------+
   |  IFW alone                                    |
   +-----------------------------------------------+
   |  RFW alone                                    |
   +-----------------------------------------------+
   |  egraph + bitvector                           |
   +-----------------------------------------------+
   |  egraph + array solver                        |
   +-----------------------------------------------+
   |  egraph + simplex solver                      |
   +-----------------------------------------------+
   |  egraph + bitvector + array solver            |
   +-----------------------------------------------+
   |  egraph + simplex + array solver              |
   +-----------------------------------------------+
   |  egraph + bitvector + simplex + array solver  |
   +-----------------------------------------------+


If no solvers are used, the context can deal only with Boolean formulas.


**Arithmetic Fragment**

When the simplex solver is used, it is also possible to specify
an arithmetic fragment:

   ============ ==========================================
     Fragment     Meaning
   ============ ==========================================
     IDL          Integer Difference Logic
     RDL          Real Difference Logic
     LRA          Real Linear Arithmetic
     LIA          Integer Linear Arithmetic
     LIRA         Mixed Linear Arithmetic (Integer/Real)
   ============ ==========================================

The arithmetic fragment is ignored if there is no arithemtic solver at
all, or if the arithmetic solver is one of the Floyd-Warshall solvers.



**Operating Mode**


In addition to the solver combination, a context can be configured
for different usages.

   ==================== =================================================
     Mode                 Meaning
   ==================== =================================================
     ONE-SHOT             Check satisfiability of one set of assertions
     MULTI-CHECKS         Repeated calls to assert/check are allowed
     PUSH-POP             Push and Pop are supported
     INTERACTIVE          Gracefully recovers from interrupted searches
   ==================== =================================================

These four different modes are explained in the Yices manual.

Currently, the Floyd-Warshall solvers can only be used in mode ONE-SHOT.

By default, a new solver is configured as follows:

- solvers: egraph + simplex + bitvector + array solver

- usage: push/pop supported

To specify another configuration, one must pass a configuration
descriptor to function yices_new_context. A configuration descriptor
is an opaque structure that includes the following fields:

- arith-fragment: either IDL, RDL, LRA, LIA, or LIRA

- uf-solver: either NONE, DEFAULT

- bv-solver: either NONE, DEFAULT

- array-solver: either NONE, DEFAULT

- arith-solver: either NONE, DEFAULT, IFW, RFW, SIMPLEX

- mode: either ONE-SHOT, MULTI-CHECKS, PUSH-POP, INTERACTIVE

This is done as follows:

1) allocate a configuration descriptor via yices_new_config

2) set the configuration parameters by repeated calls to yices_set_config or using yices_default_config_for_logic

3) create one or more context with this configuration by passing the descriptor to yices_new_context

4) free the configuration descriptor when it's no longer needed

.. c:function:: ctx_config_t* yices_new_config(void)

.. c:function:: void yices_free_config(ctx_config_t* config)

.. c:function:: int32_t yices_set_config(ctx_config_t* config, const char* name, const char* value)

.. c:function:: int32_t yices_default_config_for_logic(ctx_config_t* config, const char* logic)

.. c:function:: context_t* yices_new_context(const ctx_config_t* config)

.. c:function:: void yices_free_context(context_t* ctx)

.. c:function:: smt_status_t yices_context_status(context_t* ctx)

.. c:function:: int32_t yices_context_enable_option(context_t* ctx, const char* option)

.. c:function:: int32_t yices_context_disable_option(context_t* ctx, const char* option)


Assertions
----------
.. c:function:: int32_t yices_assert_formula(context_t* ctx, term_t t)

.. c:function:: int32_t int32_t yices_assert_formulas(context_t* ctx, uint32_t n, const term_t t[])

.. c:function:: smt_status_t yices_check_context(context_t* ctx, const param_t* params)

.. c:function:: void yices_stop_search(context_t* ctx)

.. c:function:: int32_t yices_assert_blocking_clause(context* ctx)


Push and Pop
------------

.. c:function:: void yices_reset_context(context_t* ctx)

.. c:function:: int32_t yices_push(context_t* ctx)

.. c:function:: int32_t yices_pop(context_t* ctx)



Search Parameters
-----------------

.. c:function:: param_t* yices_new_param_record(void)

.. c:function:: int32_t yices_set_param(param_t* p, const char* name, const char* value)

.. c:function:: void yices_free_param_record(param_t* param)
