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

1) creating and configuring a context

2) asserting formulas in a context

3) checking whether a context is satisfiable

4) building a model from a satisfiable context

5) deleting a context

A push/pop mechanism allows one to organize the assertions in a stack
to support incremental solving and backtracking.






Creation and Configuration
--------------------------

When a context is created, it is possible to configure it to use a
specific solver or a specific combination of solvers.  It is also
possible to specify whether or not the context should support
features such as push and pop.

The following theory solvers are currently available:

- egraph (solver for uninterpreted functions)

- bitvector solver

- array solver

- solver for linear arithmetic based on simplex

- solver for integer difference logic (based on Floyd-Warshall)

- solver for real difference logic (also based on Floyd-Warshall)

The following combinations of theory solvers can be used:

- no solvers at all

- egraph alone

- bitvector solver alone

- simplex solver alone

- integer Floyd-Warshall solver alone

- real Floyd-Warshall solver alone

- egraph + bitvector solver

- egraph + simplex solver

- egraph + array solver

- egraph + bitvector + array solver

- egraph + simplex + array solver

- egraph + simplex + bitvector + array solver

If no solvers are used, the context can deal only with Boolean
formulas.

When the simplex solver is used, it's also possible to
specify which arithmetic fragment is intended, namely:

- integer difference logic              (IDL)

- real difference logic                 (RDL)

- real linear arithmetic                (LRA)

- integer linear arithmetic             (LIA)

- mixed integer/real linear arithmetic  (LIRA)

In addition to the solver combination, a context can be configured
for different usages:

- one-shot mode: check satisfiability of one set of formulas

- multiple checks: repeated calls to assert/check are allowed

- push/pop: push and pop are supported (implies multiple checks)

- clean interrupts are supported (implies push/pop)

Currently, the Floyd-Warshall solvers can only be used in one-shot mode.

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
