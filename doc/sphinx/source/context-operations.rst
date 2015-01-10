:tocdepth: 2

.. highlight:: c

.. _context_operations:

Contexts
========

Contexts are one of the most important data structures in Yices. A
context contains one or more solvers and provides functions for
manipulating assertions and for checking whether these assertions are
satisfiable. If they are, a model can be constructed from the context.

Yices allows several contexts to be created and manipulated
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
includes theory solvers for linear arithmetic, bitvectors,
uninterpreted functions, and arrays. The context supports the push/pop
mechanism and the arithmetic solver can handle mixed integer and real
linear arithmetic.

To use a more specialized set of solvers, one can configure the
context for a specific logic. Here is an example::

   ctx_config_t *config = yices_new_config();
   yices_default_config_for_logic(config, "QF_LRA");
   context_t *ctx = yices_new_context(config);
   yices_free_config(config)

In this case, we pass a non-NULL configuration descriptor to function
:c:func:`yices_new_context` to specify the logic. Logics are
identified by their SMT-LIB name. In this example, QF_LRA means
quantifier-free linear real arithmetic. This configuration creates a
context with a single theory solver, namely, the simplex-based solver
for linear arithmetic. As previously, the context supports the
push/pop mechanism.

If the push and pop features are not needed, we can change the configuration
as follows::

   ctx_config_t *config = yices_new_config();
   yices_default_config_for_logic(config, "QF_LRA");
   yices_set_config(config, "mode", "one-shot");
   context_t *ctx = yices_new_context(config);
   yices_free_config(config)

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

4) delete the configuration descriptor when it is no longer needed using :c:func:`yices_free_config`.


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
solver so it's not possible to have both a Floyd-Warshall solver and
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


If no solvers are used, the context can deal only with Boolean
formulas.  By default, a context uses egraph, bitvector, simplex, and
the array solver (last row in the table).


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

The arithmetic fragment is ignored if there is no arithmetic solver or
if the arithmetic solver is one of the Floyd-Warshall solvers.  The
default fragment is LIRA.


**Operating Mode**

In addition to the solver combination, a context can be configured
for different usages.

   - In mode *one-shot*, assertions are not allowed after a call to function
     :c:func:`yices_check_context`. This mode is useful to check
     satisfiability of a single block of assertions and possibly construct
     a model if the assertions are satisfiable.

   - In mode *multi-check*, the context can be used to check incremental
     blocks of assertions. It is possible to add assertions after a call to
     :c:func:`yices_check_context` but it is not possible to retract
     assertions.

   - In mode *push-pop*, the context maintains assertions in a stack and it
     is possible to add and later retract assertions.

   - The mode *interactive* provides the same functionalities as
     push-pop. In addition, the context can recover gracefully if a
     search is interrupted.

In the first two modes, Yices employs more aggressive simplifications
when processing assertions, which can lead to better performance. In
the interactive mode, the current state of the context is saved before
each call to :c:func:`yices_check_context`.  This introduces overhead,
but the context can be restored to a clean state if the search is
interrupted.

The default mode is push-pop.

Currently, the Floyd-Warshall solvers can only be used in mode one-shot.


Configuration Descriptor
........................

To specify a context configuration other than the default, one must
pass a configuration descriptor to function yices_new_context. A
configuration descriptor is a record that stores operating mode,
arithmetic fragment, and solver combination. 

The record stores four configuration parameters that describe the theory solvers:

   +--------------+---------------+---------------------------------------+
   | Name         | Value         |  Meaning                              |
   +==============+===============+=======================================+
   | uf-solver    | none          |  no UF solver                         |
   |              +---------------+---------------------------------------+
   |              | default       |  use the egraph                       |
   +--------------+---------------+---------------------------------------+
   | bv-solver    | none          |  no bitvector solver                  |
   |              +---------------+---------------------------------------+
   |              | default       |  use the bitvector solver             |
   +--------------+---------------+---------------------------------------+
   | array-solver | none          |  no array solver                      |
   |              +---------------+---------------------------------------+
   |              | default       |  use the array solver                 |
   +--------------+---------------+---------------------------------------+       
   | arith-solver | none          |  no arithmetic solver                 |
   |              +---------------+---------------------------------------+
   |              | ifw           |  integer Floyd-Warshall               |
   |              +---------------+---------------------------------------+
   |              | rfw           |  real Floyd-Warshall                  |
   |              +---------------+---------------------------------------+
   |              | simplex       |  simplex solver                       |
   |              +---------------+---------------------------------------+
   |              | default       |  same as simplex                      |
   |              +---------------+---------------------------------------+
   |              | auto          |  same as simplex unless mode=one-shot |
   |              |               |  and logic is QF_IDL or QF_RDL        |
   +--------------+---------------+---------------------------------------+


Two more parameters in the configuration descriptor specifies the
arithmetic fragment and the operating mode:

   +--------------------+-----------------------------------------------------+
   | Name               |  Possible values                                    |          
   +====================+=====================================================+
   | arith-fragment     |  IDL, RDL, LRA, LIA, or LIRA                        |
   +--------------------+-----------------------------------------------------+
   | mode               |  one-shot, multi-checks, push-pop, or interactive   |
   +--------------------+-----------------------------------------------------+

  

A configuration descriptor also stores a logic flag, which can either
be *unknown* (i.e., no logic specified), or the name of an SMT-LIB
logic, or the special name *NONE*. If this logic flag is set (i.e.,
not *unknown*), it takes precedence over the four solver-selection
parameters listed in the previous table. The solver combination is
determined by the logic.  The special logic name *NONE* means no
theory solvers.

If the logic is QF_IDL or QF_RDL and the mode is one-shot, then one
can set the arith-solver to *auto*. In this setting, the actual
arithmetic solver is selected when :c:func:`yices_check_context` is
called, based on the assertions. Depending on the number of
constraints and variables, Yices will either pick the Floyd-Warshall
solver for IDL or RDL, or the generic Simplex-based solver.


The following functions allocate configuration records and set
parameters and logic.

.. c:function:: ctx_config_t* yices_new_config(void)

   Allocates a new context configuration record.

   This functions returns a new configuration record, initialized for the default
   configuration.

.. c:function:: void yices_free_config(ctx_config_t* config)

   Deletes a configuration record.

.. c:function:: int32_t yices_set_config(ctx_config_t* config, const char* name, const char* value)

   Sets a context-configuration parameter.

   **Parameters**

   - *config* must be a pointer to a configuration record returned by :c:func:`yices_new_config`

   - *name* must be the name of a configuration parameter

   - *value* is the value for the parameter

   The *name* and *value* must be spelled as shown in the previous two tables. For example,
   to set the arithmetic solver to the Floyd-Warshall solver for QF_IDL, call::

      yices_set_config(config, "arith-solver", "ifw");

   The function returns -1 if there's an error or 0 otherwise.

   **Error report**

   - if *name* is not a known parameter name

     -- error code: :c:enum:`CTX_UNKNOWN_PARAMETER`

   - if *value* is not valid for the parameter *name*

     -- error code: :c:enum:`CTX_INVALID_PARAMETER_VALUE`


.. c:function:: int32_t yices_default_config_for_logic(ctx_config_t* config, const char* logic)

   Prepares a context-configuration for a specified logic.

   **Parameters**

   - *config* must be a pointer to a configuration parameter returned by :c:func:`yices_new_config`

   - *logic* must be either the name of a logic or the string ``"NONE"``

   If *logic* is ``"NONE"`` then no theory solvers are included, and
   the context can only process purely Boolean assertions. Otherwse
   *logic* must be the name of an SMT-LIB logic.  The logics
   recognized and supported by Yices are listed in :ref:`smt_logics`.

   If the logic is unrecognized or unsupported, the function leaves
   the configuration record unchanged and returns -1.  It returns 0
   otherwise.

   **Error code**

   - if the *logic* is not recognized

     -- error code: :c:enum:`CTX_UNKNOWN_LOGIC`
 
   - if the *logic* is known but not supported

     -- error code: :c:enum:`CTX_LOGIC_NOT_SUPPORTED`




Context Creation and Deletion
.............................

.. c:function:: context_t* yices_new_context(const ctx_config_t* config)

   Creates a new context.

   This function allocates and initializes a new context and returns (a pointer to) it.

   **Parameter**

   - *config*: configuration record or :c:macro:`NULL`

   If *config* is :c:macro:`NULL`, the returned context is configured
   to use the default solver combination, arithmetic fragment, and
   operating mode.

   Otherwise, the function checks whether the specified configuration
   is valid and supported. If it is, the context is configured as
   specified.  If the configuration is not valid, the function returns
   :c:macro:`NULL` and sets the error report.

   A configuration may be invalid if it requests a solver combination that
   is not supported (for example, the array solver but no egraph), or if
   the operating mode is not supported by the solvers (e.g., mode is push-pop
   and arith-solver is ifw).

   **Error report**

   - if *config* is not valid

     -- error code: :c:enum:`CTX_INVALID_CONFIG`

.. c:function:: void yices_free_context(context_t* ctx)

   Deletes a context.

   This function should be called when *ctx* is no longer used to free
   the memory allocated to this context.

   .. note:: If this function is not called, Yices will automatically free
             the context on a call to :c:func:`yices_exit`.



Preprocessing Options
.....................

.. c:function:: int32_t yices_context_enable_option(context_t* ctx, const char* option)

.. c:function:: int32_t yices_context_disable_option(context_t* ctx, const char* option)



Assertions and Satisfiability Checks
------------------------------------

.. c:function:: smt_status_t yices_context_status(context_t* ctx)

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
