:tocdepth: 2

.. include:: macros

.. highlight:: c

.. _context_operations:

Contexts
========

Contexts are one of the most important data structures in Yices. A
context contains one or more solvers and supports operations for
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
   yices_free_config(config);

In this case, we pass a non-NULL configuration descriptor to function
:c:func:`yices_new_context` to specify the logic. Logics are
identified by their SMT-LIB name. In this example, QF_LRA means
quantifier-free linear real arithmetic. This configuration creates a
context with a single theory solver, namely, the Simplex-based solver
for linear arithmetic. As previously, the context supports the
push/pop mechanism.

If push and pop are not needed, we can change the configuration as
follows::

   ctx_config_t *config = yices_new_config();
   yices_default_config_for_logic(config, "QF_LRA");
   yices_set_config(config, "mode", "one-shot");
   context_t *ctx = yices_new_context(config);
   yices_free_config(config);

The call to :c:func:`yices_set_config` changes the context's mode of
operation from the default (i.e., support for push and pop) to a more
restricted mode where push and pop are not supported. In this mode,
the context can use more aggressive simplification and preprocessing
procedures, which can improve solver performance.


The general process to configure a context is as follows:

1) Allocate a configuration descriptor by a call to :c:func:`yices_new_config`.

2) Set configuration parameters by repeated calls to :c:func:`yices_set_config` or by
   calling :c:func:`yices_default_config_for_logic`.

3) Create one or more contexts with this configuration by passing the descriptor to
   function :c:func:`yices_new_context`.

4) Delete the configuration descriptor when it is no longer needed using :c:func:`yices_free_config`.


Configuration Parameters
........................

Configuration parameters specify the theory solvers to use, the
arithmetic fragment, and the context's operating mode.


**Solver Types**

Yices includes two main types of solvers. One is based on the DPLL(T)
approach to SMT solving [NOT2006]_. The other relies on the
Model-Constructing Satisfiability Calculus (MCSat) [dMJ2013]_.

Currently, DPLL(T) is the default, except for logics that include
nonlinear arithmetic.  MCSat is required for nonlinear arithmetic and
for combination of nonlinear arithmetic and uninterpreted functions.
If you configure a context for a logic such as ``"QF_NRA"`` or ``"QF_UFNIA"``
then MCSat will be automatically selected.


**Theory Solvers**

A context that uses DPLL(T) can be further configured to select one or
more theory solvers.  Currently the following theory solvers are
available:

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
formulas.  By default, a DPLL(T) context uses egraph, bitvector, simplex, and
the array solver (last row in the table).


**Arithmetic Fragment**

When the Simplex solver is used, it is possible to specify an
arithmetic fragment:

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

For DPLL(T), the four operating modes can be used, except if a
Floyd-Warshal theory solver is used. The Floyd-Warshal solvers are
specialized for difference logic and support only mode one-shot.


The default mode is push-pop.



Configuration Descriptor
........................

A configuration descriptor is a record that stores solver type,
operating mode, arithmetic fragment, and solver combination.

A first parameter specifies the solver type:

   +--------------+---------------+---------------------------------------+
   | Name         | Value         |  Meaning                              |
   +==============+===============+=======================================+
   | solver-type  | dpllt         |  use DPLL(T) approach                 |
   |              +---------------+---------------------------------------+
   |              | mcsat         |  use MCSat                            |
   +--------------+---------------+---------------------------------------+


Four configuration parameters describe the theory solvers:

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


Two more parameters in the configuration descriptor specify the
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
not *unknown*), it takes precedence over solver type and the four
solver-selection parameters listed in the previous table. If the logic
involves nonlinear arithmetic, then MCSat is automatically selected.
Otherwise, DPLL(T) is selected and the solver combination is
determined by the logic.

The special logic name *NONE* means no theory solvers. If this logic
is chosen, the context is configured to deal with purely Boolean
problems, using DPLL.

If the logic is QF_IDL or QF_RDL and the mode is one-shot, then one
can set the arith-solver to *auto*. In this setting, the actual
arithmetic solver is selected when :c:func:`yices_check_context` is
called, based on the assertions. Depending on the number of
constraints and variables, Yices will either pick the Floyd-Warshall
solver for IDL or RDL, or the generic Simplex-based solver.


The following functions allocate configuration records and set
parameters and logic.

.. c:function:: ctx_config_t* yices_new_config(void)

   Allocates a context-configuration record.

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

   Prepares a context configuration for a specified logic.

   **Parameters**

   - *config* must be a pointer to a configuration record returned by :c:func:`yices_new_config`

   - *logic* must be either the name of a logic or the string ``"NONE"``

   If *logic* is ``"NONE"`` then no theory solvers are included, and
   the context can only process purely Boolean assertions. Otherwise
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
             the context on a call to :c:func:`yices_exit` or :c:func:`yices_reset`.



Preprocessing Options
.....................

Several options determine the simplifications performed when formulas
are asserted. It is best to leave these unchanged, but in case you
need fine control, the following functions selectively enable or
disable a preprocessing option.

The current options include:

   +----------------------+---------------------------------------------------------+
   | Option               | Meaning                                                 |
   +======================+=========================================================+
   | var-elim             | Eliminate variables by substitution                     |
   +----------------------+---------------------------------------------------------+
   | arith-elim           | Gaussian elimination                                    |
   +----------------------+---------------------------------------------------------+
   | bvarith-elim         | Variable elimination for bitvector arithmetic           |
   +----------------------+---------------------------------------------------------+
   | eager-arith-lemmas   | Eager lemma generation for the Simplex solver           |
   +----------------------+---------------------------------------------------------+
   | flatten              | Flattening of nested (or ...)                           |
   +----------------------+---------------------------------------------------------+
   | learn-eq             | Heuristic to learn equalities in QF_UF problems         |
   +----------------------+---------------------------------------------------------+
   | keep-ite             | Keep if-then-else terms in the egraph                   |
   +----------------------+---------------------------------------------------------+
   | break-symmetries     | Heuristic to detect and break symmetries in             |
   |                      | QF_UF problems                                          |
   +----------------------+---------------------------------------------------------+
   | assert-ite-bounds    | Attempt to learn and assert upper/lower bounds          |
   |                      | on if-then-else terms                                   |
   +----------------------+---------------------------------------------------------+


   If *eager-arith-lemmas* is enabled, the Simplex solver will eagerly generate lemmas such
   as (x |ge| 1) |implies| (x |ge| 0), that is, lemmas that involve two atoms that contain
   the same variable. See [DdM2006]_ for more details.

   The *flatten* option converts a term such as (or (or a b) (or b c d)) to (or a b c d).

   The *break-symmetries* option enables symmetry breaking as described in [DFMW2011]_.

   If *assert-ite-bounds* is enabled, Yices tries to compute upper and
   lower bounds on arithmetic if-then-else terms, and asserts these
   bounds. For example, if *t* is defined as *(ite c 10 (ite d 3 20))*
   then the context will include the bounds: 3 |le| t |le| 20.


.. c:function:: int32_t yices_context_enable_option(context_t* ctx, const char* option)

   Enables a preprocessing option.

   **Parameters**

   - *ctx* context

   - *option*: option name

   The option name must be given as a string, as listed in the previous table.

   For example to enable symmetry breaking::

     yices_context_enable_option(ctx, "break-symmetries");

   This function returns -1 if the option is not recognized, or 0 otherwise.

   **Error report**

   - if the option is not recognized:

     -- error code: :c:enum:`CTX_UNKNOWN_PARAMETER`


.. c:function:: int32_t yices_context_disable_option(context_t* ctx, const char* option)

   Disables a preprocessing option.

   The parameters and error conditions are the same as for :c:func:`yices_context_enable_option`.


Assertions and Satisfiability Checks
------------------------------------

Once a context is initialized, the following functions can be used to
assert formulas, check satisfiability, and query the context's status.

.. c:function:: smt_status_t yices_context_status(context_t* ctx)

   Returns a context's status.

   An internal flag stores the context's current state. This function
   reads this flag and returns it.

   The returned value is one of the following codes:

   - :c:enum:`STATUS_IDLE`. This is the initial state.

     In this state, it is possible to assert formulas. The state may
     then change to :c:enum:`STATUS_UNSAT` if the assertions are
     trivially unsatisfiable Otherwise, the state remains
     :c:enum:`STATUS_IDLE`.

   - :c:enum:`STATUS_SEARCHING`. This is the context state during search.

     The context enters this state on a call to :c:func:`yices_check_context` and remains
     in this state until the solver completes or the search is interrupted.

   - :c:enum:`STATUS_SAT`, :c:enum:`STATUS_UNSAT`, :c:enum:`STATUS_UNKNOWN`.

     These are the states after a search completes. :c:enum:`STATUS_UNKNOWN` means
     that the search was inconclusive, which may happen if the solver is not complete.

   - :c:enum:`YICES_STATUS_INTERRUPTED`.

     This state is entered if a search is interrupted.

   These codes are defined in :file:`yices_types.h` (see :c:type:`smt_status_t`).


.. c:function:: int32_t yices_assert_formula(context_t* ctx, term_t t)

   Asserts a formula.

   This function asserts formula *t* in context *ctx*.

   The term *t* must be Boolean.

   The context *ctx* must be in one of the following states:
   :c:enum:`STATUS_IDLE`, :c:enum:`STATUS_UNSAT`,
   :c:enum:`STATUS_SAT`, or :c:enum:`STATUS_UNKNOWN`.

   - if the current state is :c:enum:`STATUS_UNSAT`, this function does nothing.

   - otherwise, the formula *t* is simplified and asserted in the context. The context's state
     is then changed to :c:enum:`STATUS_UNSAT` if the assertion simplifies to false, or to
     :c:enum:`STATUS_IDLE` otherwise.

   If the context is in mode *one-shot*, this function fails if the state is either
   :c:enum:`STATUS_SAT` or :c:enum:`STATUS_UNKNOWN`.

   The function returns 0 if there's no error, or -1 otherwise.

   **Error report**

   - if *t* is invalid

     -- error code: :c:enum:`INVALID_TERM`

     -- term1 := t

   - if *t* is not Boolean

     -- error code: :c:enum:`TYPE_MISMATCH`

     -- term1 := t

     -- type1 := bool

   - if *ctx*'s state is :c:enum:`YICES_STATUS_INTERRUPTED`

     -- error code: :c:enum:`CTX_INVALID_OPERATION`

   - if *ctx*'s mode is *one-shot* and *ctx*'s state is neither :c:enum:`STATUS_IDLE` nor :c:enum:`STATUS_UNSAT`

     -- error code: :c:enum:`CTX_OPERATION_NOT_SUPPORTED`

   Other error codes are possible if *t* is outside the logic supported by the context.
   See :ref:`error_types`.


.. c:function:: int32_t yices_assert_formulas(context_t* ctx, uint32_t n, const term_t t[])

   Asserts an array of formula.

   This function adds assertions *t[0]* |...| *t[n-1]* to *ctx*.

   **Parameters**

   - *n* is the number of formulas to assert

   - *t* must be an array of *n* Boolean terms.

   The context must be in state :c:enum:`STATUS_IDLE`,
   :c:enum:`STATUS_UNSAT`, :c:enum:`STATUS_SAT`, or
   :c:enum:`STATUS_UNKNOWN`.

   This function is equivalent to calling
   :c:func:`yices_assert_formula` with input *(and t[0] ... t[n-1])*.
   In particular, if *n* is 0, this function is equivalent to
   asserting true in *ctx*.

   The returned value and error conditions are as in :c:func:`yices_assert_formulas`.


.. c:function:: smt_status_t yices_check_context(context_t* ctx, const param_t* params)

   Checks whether a context is satisfiable.

   **Parameters**

   - *ctx* is a context

   - *params* is an optional pointer to a search-parameter structure

   The *params* data structure can be used to control the heuristics
   used by the solvers. See :ref:`params`. If *params* is
   :c:macro:`NULL`, default settings are used.


   This function's behavior and returned value depend on *ctx*'s current state.

   - If the state is :c:enum:`STATUS_SAT`, :c:enum:`STATUS_UNSAT`, or :c:enum:`STATUS_UNKNOWN`,
     the function just returns this status.

   - If the state is :c:enum:`STATUS_IDLE`, then the context's solver
     (as defined by the context's configuration) searches for a
     satisfying assignment to all the assertions stored in *ctx*.
     If *params* is not :c:macro:`NULL`, the solver uses the
     heuristic parameters specified by *params*.

     Then the function returns one of the following codes:

     - :c:enum:`STATUS_UNSAT`: the context is not satisfiable.

     - :c:enum:`STATUS_SAT`: the context is satisfiable.

     - :c:enum:`STATUS_UNKNOWN`: the solver can't prove whether the context is
       satisfiable or not.

     - :c:enum:`YICES_STATUS_INTERRUPTED`: the search was interrupted by a
       call to :c:func:`yices_stop_search`.

     This returned value is also stored as the context's status flag, with the following exception:

     - If the context is configured for mode *interactive* and the search is interrupted,
       then the function returns :c:enum:`YICES_STATUS_INTERRUPTED` but the context's state is
       restored to what it was before the call to :c:func:`yices_check_context`, and the
       internal status flag is reset to  :c:enum:`STATUS_IDLE`.

   - If *ctx* is in another state, the function
     returns :c:enum:`STATUS_ERROR`.

   **Error report**

   - if *ctx*'s states is wrong:

     -- error code: :c:enum:`CTX_INVALID_OPERATION`


.. c:function:: void yices_stop_search(context_t* ctx)

   Interrupts the search.

   This function can be called from a signal handler to stop the
   search after at call to :c:func:`yices_check_context`. If the
   context's state is :c:enum:`STATUS_SEARCHING` then the search is
   interrupted, otherwise the function does nothing.

   .. note:: If the search is interrupted and the context's mode is
             not *interactive* then the context's enters state
             :c:enum:`YICES_STATUS_INTERRUPTED`. The only way to recover is
             then to call :c:func:`yices_reset_context` or
             :c:func:`yices_pop` (assuming the context supports push and pop).


.. c:function:: void yices_reset_context(context_t* ctx)

   Resets a context.

   This function removes all the assertions stored in *ctx* and resets
   the context's state to :c:enum:`STATUS_IDLE`.


.. c:function:: int32_t yices_assert_blocking_clause(context_t* ctx)

   Adds a blocking clause.

   This function is intended to enumerate different models for a set
   of assertions.

   - If *ctx*'s status is either :c:enum:`STATUS_SAT` or
     :c:enum:`STATUS_UNKNOWN`, then a new clause is asserted in *ctx*
     to remove the current truth assignment.  After this clause is
     added, the next call to :c:func:`yices_check_context` will either
     produce a different truth assignment (hence a different model) or
     return :c:enum:`STATUS_UNSAT`.

     After adding the clause, the context's state is updated to either
     :c:enum:`STATUS_IDLE` (if the clause is not empty) or to
     :c:enum:`STATUS_UNSAT` if the blocking clause is empty.


   - If *ctx*'s status is not :c:enum:`STATUS_SAT` or :c:enum:`STATUS_UNKNOWN`,
     the function reports an error.

   This function is not supported if the context's mode is *one-shot*.

   The returned value is 0 if the operation succeeds or -1 otherwise.

   **Error report**

   - if *ctx*'s status is different from :c:enum:`STATUS_SAT` and :c:enum:`STATUS_UNKNOWN`

     -- error code: :c:enum:`CTX_INVALID_OPERATION`

   - if *ctx*'s mode is *one-shot*

     -- error code: :c:enum:`CTX_OPERATION_NOT_SUPPORTED`



Push and Pop
------------

If a context is configured to support push and pop (i.e., if the mode
is either *push-pop* or *interactive*) then the context maintains a
stack of assertions organized in levels.The push operation starts a
new level and the pop operation removes all assertions added at the
current level. Push can be thought of as setting a backtracking point
and pop restores the context's state to a previous backtracking point.

Initially, the assertion level is zero.  Assertions at level zero
cannot be retracted. For example, any formula asserted before the
first call to :c:func:`yices_push` is part of the context and cannot
be removed by :c:func:`yices_pop`.

.. c:function:: int32_t yices_push(context_t* ctx)

   Marks a backtracking point.

   This function starts a new assertion level. The *ctx* must be
   configured to support push and pop, and its state must be either
   :c:enum:`STATUS_IDLE`, or :c:enum:`STATUS_SAT`, or
   :c:enum:`STATUS_UNKNOWN`.

   The function returns 0 if the operation succeeds or -1 otherwise.

   **Error report**

   - if *ctx* is not configured for push and pop:

     -- error code: :c:enum:`CTX_OPERATION_NOT_SUPPORTED`

   - if *ctx* supports push and pop but its status is :c:enum:`STATUS_UNSAT`,
     :c:enum:`STATUS_SEARCHING`, or :c:enum:`YCIES_STATUS_INTERRUPTED`:

     -- error code: :c:enum:`CTX_INVALID_OPERATION`

.. c:function:: int32_t yices_pop(context_t* ctx)

   Backtracks.

   This function removes all assertions at the current level (i.e.,
   restores the context's state to what it was at the matching call to
   :c:func:`yices_push`), then decrements the assertion level. It
   fails if the current assertion level is zero.

   The function returns 0 if the operation succeeds or -1 otherwise.

   **Error report**

   - if *ctx* is not configured for push and pop:

     -- error code: :c:enum:`CTX_OPERATION_NOT_SUPPORTED`

   - if *ctx*'s status is :c:enum:`STATUS_SEARCHING` or if the assertion level is zero:

     -- error code: :c:enum:`CTX_INVALID_OPERATION`


Check with Assumptions and Unsat Cores
--------------------------------------

When checking satisfiability, it is possible to treat certain formulas as *assumptions*.
Assumptions are similar to asserted formulas but they are local to a single call to check.
Here is an example::

   context_t *ctx = yices_new_context(NULL);
   yices_assert_formula(ctx, f);
   status = yices_check_context_with_assumptions(ctx, NULL, 5, a);

In this fragment, we first create a context ``ctx`` then we assert a
formula ``f``.  In the call to check, we give an array of five
assumptions ``a[0]``, ..., ``a[4]``.  This amounts to checking the
conjunction of ``f`` and the five assumptions, but the assumptions are
local to the call to :c:func:`yices_check_context_with_assumptions`
and are not added to the context.  We could achieve the same effect by
using incremental solving::

   context_t *ctx = yices_new_context(NULL);
   yices_assert_formula(ctx, f);
   yices_push(ctx);
   yices_assert_formulas(ctx, 5, a);
   status = yices_check_context(ctx, NULL);
   yices_pop(ctx);

However, check with assumptions provides an additional functionality,
namely, the construction of an *unsatisfiable core*, that is, a subset
of the five assumptions that's inconsistent. The unsatisfiable core is
constructed by calling function :c:func:`yices_get_unsat_core`, which
returns the core in a term vector. A full example is in file
:file:`examples/example_unsat_core.c` included in the Yices
distribution.

.. c:function:: smt_status_t yices_check_context_with_assumptions(context_t* ctx, const param_t* params, uint32_t n, const term_t t[])

   Checks whether *n* assumptions are satisfiable in a context *ctx*.

   **Parameters**

   - *ctx* is a context

   - *params* is an optional structure to a search-parameter structure.

   - *n* is the number of assumptions

   - *t* is an array of *n* Boolean terms

   The *params* structure controls search heuristics. If *params* is NULL, default
   settings are used. See :ref:`params` and :c:func:`yices_check_context`.

   The function checks whether all assertions currently asserted in *ctx*
   together with the *n* assumptions *t[0]* |...| *t[n-1]* are
   satisfiable, and returns the result as a status code. If the
   function returns :c:enum:`STATUS_UNSAT` then one can compute an
   unsat core (i.e., a subset of the assumptions that is
   unsatisfiable) by calling :c:func:`yices_get_unsat_core`.

   More precisely:

   - If *ctx*'s current status is :c:enum:`STATUS_UNSAT` then the function does nothing
     and returns :c:enum:`STATUS_UNSAT`.

   - If *ctx*'s status is :c:enum:`STATUS_IDLE`, :c:enum:`STATUS_SAT`,
     or :c:enum:`STATUS_UNKNOWN` then the function checks whether *ctx* conjoined
     with the *n* assumptions is satisfiable. This is done even if *n* is zero.
     The function will then return a code as in :c:func:`yices_check_context`.

   - If *ctx*'s status is anything else, the function returns :c:enum:`STATUS_ERROR`.


   This operation fails and returns :c:enum:`STATUS_ERROR` if *ctx* is
   configured for one-shot solving and *ctx*'s status is anything
   other than :c:enum:`STATUS_IDLE`.

   **Error report**

   - If *ctx*'s status is wrong:

     -- error code: :c:enum:`CTX_INVALID_OPERATION`

   - If the operation is not supported by this context:

     -- error code: :c:enum:`CTX_OPERATION_NOT_SUPPORTED`


.. c:function:: int32_t yices_get_unsat_core(context_t* ctx, term_vector_t* v)

   Construct an unsat core (after a call to :c:func:`yices_check_context_with_assumptions`)
   and store it in vector *v*.

   **Parameters**

   - *ctx* is a context

   - *v* must be an initialized term vector (see :c:func:`yices_init_term_vector`).

   The function checks whether *ctx*'s status is
   :c:enum:`STATUS_UNSAT`. If so, it computes and unsat core and store
   it in vector *v*. The unsat core is an subset of the assumptions
   passed to the most recent call to :c:func:`yices_check_context_with_assumptions`.

   It is also possible to use this function after a call to :c:func:`yices_check_context`.
   In this case, the function returns an empty core.

   The unsat core is returned as follows:

   - *v->size* contains the number of elements in the core

   - *v->data[0 ... v->size - 1]* contains the elements. Each term in *v->data[i]* is
     a Boolean term, equal to one of the assumption that is part of the core.

     There are no duplicates in the *v->data* array.


   If *ctx*'s status is anything other than :c:enum:`STATUS_UNSAT`,
   the function leaves *v* unchanged and returns -1.

   **Error report**

   - If *ctx*'s status is not :c:enum:`STATUS_UNSAT`

     -- error code: :c:enum:`CTX_INVALID_OPERATION`



Check Modulo a Model and Model Interpolant
------------------------------------------

When checking satisfiability, it is possible to provide a partial
model such that the satisfiability is checked for the assertions in
conjunction with the provided model. Moreover, it is possible to
provide hints as initial model guesses when mcsat decides a
variable. To use this functionality, the context must be a context
initialized with support for MCSAT (see yices_new_context,
yices_new_config, yices_set_config).  Here is an example::

   ctx_config_t* config = yices_new_config();
   yices_set_config(config, "solver-type", "mcsat");
   context_t *ctx = yices_new_context(config);
   yices_assert_formula(ctx, f);
   status = yices_check_context_with_model(ctx, NULL, model, 5, a);

In this fragment, we first create a yices configuration ``config``
then we set its parameter ``solver-type`` to ``mcsat``. Then, we
create a context ``ctx`` using ``config``. After that we assert a
formula ``f``.  In the call to check, we give an array of five
uninterpreted terms ``a[0]``, ..., ``a[4]``.  This amounts to checking
the conjunction of ``f`` and the equalities between the unintpreted
terms and their value in the ``model``.

Here is an example of checking context with model and hint::

   ctx_config_t* config = yices_new_config();
   yices_set_config(config, "solver-type", "mcsat");
   context_t *ctx = yices_new_context(config);
   yices_assert_formula(ctx, f);
   status = yices_check_context_with_model_and_hint(ctx, NULL, model, 5, a, 3);

In this fragment, similar to the earlier one, we assert a formula
``f``.  In the call to check on the last line, we give an array of
five uninterpreted terms ``a[0]``, ..., ``a[4]``.  However, this time
we would be checking the conjunction of ``f`` and the equalities
between the first three (the number is given as the last argument)
unintpreted terms and their value in the ``model``. The remaining two
terms and their values will be provided as hints to the internal mcsat
decide method.

The check modulo a model provides an additional functionality, namely,
the construction of a model interpolant, if the yices context is
unsatisfiable and supports model interpolation (see
yices_set_config). This model interpolant is constructed by calling
:c:func:`yices_get_model_interpolant`.


.. c:function:: smt_status_t yices_check_context_with_model(context_t* ctx, const param_t* params, model_t *mdl, uint32_t n, const term_t t[])

   Checks whether *n* assumptions are satisfiable in a context *ctx*.

   **Parameters**

   - *ctx* is a context

   - *params* is an optional structure to a search-parameter structure.

   - *mdl* is a model

   - *n* is the number of assumptions

   - *t* is an array of *n* uninterpreted terms

   The *params* structure controls search heuristics. If *params* is NULL, default
   settings are used. See :ref:`params` and :c:func:`yices_check_context`.

   This function checks statisfiability of the constraints in ctx
   conjoined with a conjunction of equalities defined by *t[i]* and the
   model, namely,

   *t[0] == v_0 /\ .... /\ t[n-1] = v_{n-1}*,

   where *v_i* is the value of *t[i]* in *mdl*.

   NOTE: if *t[i]* does not have a value in *mdl*, then a default value is
   picked for *v_i*.

   If this function returns STATUS_UNSAT and the context supports
   model interpolation, then one can construct a model interpolant by
   calling function :c:func:`yices_get_model_interpolant`.

   More precisely:

   - If *ctx*'s current status is :c:enum:`STATUS_UNSAT` then the function does nothing
     and returns :c:enum:`STATUS_UNSAT`.

   - If *ctx*'s status is :c:enum:`STATUS_IDLE`, :c:enum:`STATUS_SAT`,
     or :c:enum:`STATUS_UNKNOWN` then the function checks whether
     *ctx* conjoined with the *n* equalities given by *mdl* and *t* is
     satisfiable. This is done even if *n* is zero.  The function will
     then return a code as in :c:func:`yices_check_context`.

   - If *ctx*'s status is anything else, the function returns :c:enum:`STATUS_ERROR`.


   This operation fails and returns :c:enum:`STATUS_ERROR` if *ctx* is
   configured for one-shot solving and *ctx*'s status is anything
   other than :c:enum:`STATUS_IDLE`.

   **Error report**

   - If one of the terms *t[i]* is not an uninterpreted:

     -- error code: :c:enum:`MCSAT_ERROR_ASSUMPTION_TERM_NOT_SUPPORTED`

   - If the context does not have the MCSAT solver enabled:

     -- error code: :c:enum:`CTX_OPERATION_NOT_SUPPORTED`

   - If the resulting status is :c:enum:`STATUS_SAT` and context does not support multichecks:

     -- error code: :c:enum:`CTX_OPERATION_NOT_SUPPORTED`


.. c:function:: smt_status_t yices_check_context_with_model_and_hint(context_t* ctx, const param_t* params, model_t *mdl, uint32_t n, const term_t t[], uint32_t m)

   Checks whether *n* assumptions are satisfiable in a context *ctx*.

   **Parameters**

   - *ctx* is a context

   - *params* is an optional structure to a search-parameter structure.

   - *mdl* is a model

   - *n* is the number of terms in *t*

   - *t* is an array of *n* uninterpreted terms

   - *m* is the number of terms 

   The *params* structure controls search heuristics. If *params* is NULL, default
   settings are used. See :ref:`params` and :c:func:`yices_check_context`.

   This function checks statisfiability of the constraints in ctx
   conjoined with a conjunction of equalities defined by *t[i]* and the
   model, namely,

   *t[0] == v_0 /\ .... /\ t[n-1] = v_{m-1}*,

   and the remaining n-m terms in t are provided with hints from the model, i.e.
 
   *t[m], ... , t[n-1]* will be given *v_{m}, ... , v_{n-1}* values when deciding

   where *v_i* is the value of *t[i]* in *mdl*.

   NOTE: if *t[i]* does not have a value in *mdl*, then a default value is
   picked for *v_i*.

   If this function returns STATUS_UNSAT and the context supports
   model interpolation, then one can construct a model interpolant by
   calling function :c:func:`yices_get_model_interpolant`.

   More precisely:

   - If *ctx*'s current status is :c:enum:`STATUS_UNSAT` then the function does nothing
     and returns :c:enum:`STATUS_UNSAT`.

   - If *ctx*'s status is :c:enum:`STATUS_IDLE`, :c:enum:`STATUS_SAT`,
     or :c:enum:`STATUS_UNKNOWN` then the function checks whether
     *ctx* conjoined with the *n* equalities given by *mdl* and *t* is
     satisfiable. This is done even if *n* is zero.  The function will
     then return a code as in :c:func:`yices_check_context`.

   - If *ctx*'s status is anything else, the function returns :c:enum:`STATUS_ERROR`.


   This operation fails and returns :c:enum:`STATUS_ERROR` if *ctx* is
   configured for one-shot solving and *ctx*'s status is anything
   other than :c:enum:`STATUS_IDLE`.

   **Error report**

   - If one of the terms *t[i]* is not an uninterpreted:

     -- error code: :c:enum:`MCSAT_ERROR_ASSUMPTION_TERM_NOT_SUPPORTED`

   - If the context does not have the MCSAT solver enabled:

     -- error code: :c:enum:`CTX_OPERATION_NOT_SUPPORTED`

   - If the resulting status is :c:enum:`STATUS_SAT` and context does not support multichecks:

     -- error code: :c:enum:`CTX_OPERATION_NOT_SUPPORTED`

.. c:function:: term_t yices_get_model_interpolant(context_t* ctx)

   Construct and return a model interpolant.

   **Parameters**

   - *ctx* is a context


   If *ctx* status is unsat and the context was configured with model-interpolation,
   this function returns a model interpolant.
   Otherwise, it sets an error code and return NULL_TERM.

   This is intended to be used after a call to
   :c:func:`yices_check_context_with_model` or
   :c:func:`yices_check_context_with_model_and_hint`
   that returned
   :c:enum:`STATUS_UNSAT`. In this case, the function builds an model
   interpolant. The model interpolant is a clause implied by the
   current context that is false in the model provides to
   :c:func:`yices_check_context_with_model`.

   **Error report**

   - If the context is not configured with model interpolation:

     -- error code: :c:enum:`CTX_OPERATION_NOT_SUPPORTED`

   - If the context's status is not :c:enum:`STATUS_UNSAT`:

     -- error code: :c:enum:`CTX_INVALID_OPERATION`


Check and Compute Interpolant
-----------------------------

It is possible to check assertions and compute an interpolant if the
assertions are unsatisfiable. This functionality requires having two
contexts that are stored in a *interpolation_context*. The
*interpolation_context* is a struct with four components defined
as follows::

   typedef struct interpolation_context_s {
     context_t *ctx_A;
     context_t *ctx_B;
     term_t interpolant;
     model_t *model;
   } interpolation_context_t;


.. c:function:: smt_status_t yices_check_context_with_interpolation(interpolation_context_t *ctx, const param_t *params, int32_t build_model)

   Check satisfiability and compute interpolant.

   **Parameters**

   - *ctx* is a interpolation context

   - *params* is an optional structure to a search-parameter structure.

   - *build_model* is a Boolean flag

   The *params* structure controls search heuristics. If *params* is NULL, default
   settings are used. See :ref:`params` and :c:func:`yices_check_context`.

   To call this function:

   - *ctx->ctx_A* must be a context initialized with support for MCSAT and interpolation.

   - *ctx->ctx_B* can be another context (not necessarily with MCSAT support).

   If this function returns :c:enum:`STATUS_UNSAT`, then an
   interpolant is returned in *ctx->interpolant*.

   If this function returns :c:enum:`STATUS_SAT` and *build_model* is
   true, then a model is returned in *ctx->model*. This model must be
   freed when no-longer needed by calling :c:func:`yices_free_model`.

   **Error report**

   - If something is wrong:

     -- error code: :c:enum:`CTX_INVALID_OPERATION`


Set a Fixed Variable Ordering for MCSat
---------------------------------------

It is possible to give a fixed variable ordering for the MCSat search --
this will make MCSAT to decide the variables in the given order. Note
that the variables in the given ordering are always decided earlier
than the ones not in the ordering. Therefore, the ordering variables
are not affected by the dynamic variable decision heuristic like
VSIDS. Moreover, a subsequent calls to this operation will overwrite
previously set ordering.

.. c:function:: smt_status_t yices_mcsat_set_fixed_var_order(context_t *ctx, uint32_t n, const term_t t[])

   Set a fixed variable ordering for the MCSat search.

   **Parameters**

   - *ctx* is a context

   - *t* is an array of variables

   - *n* is the size of the *t* array

   If the operation fails, it will return :c:enum:`STATUS_ERROR`,
   otherwise it returns :c:enum:`STATUS_IDLE`.

   **Error report**

   - If the context is not configured for MCSat:

     -- error code: :c:enum:`CTX_OPERATION_NOT_SUPPORTED`

   - If the terms in the *t* array are not variables:

     -- error code: :c:enum:`VARIABLE_REQUIRED`


Set a Initial Variable Ordering for MCSat
-----------------------------------------

It is also possible to give a variable ordering that will be used only
in the beginning of the MCSAT search -- once that order has been
decided, MCSAT can choose according to its heuristics from that point
onward. 

.. c:function:: smt_status_t yices_mcsat_set_initial_var_order(context_t *ctx, uint32_t n, const term_t t[])

   Set an initial variable ordering for the MCSat search.

   **Parameters**

   - *ctx* is a context

   - *t* is an array of variables

   - *n* is the size of the *t* array

   If the operation fails, it will return :c:enum:`STATUS_ERROR`,
   otherwise it returns :c:enum:`STATUS_IDLE`.

   **Error report**

   - If the context is not configured for MCSat:

     -- error code: :c:enum:`CTX_OPERATION_NOT_SUPPORTED`

   - If the terms in the *t* array are not variables:

     -- error code: :c:enum:`VARIABLE_REQUIRED`


.. _params:

Search Parameters
-----------------

A parameter record stores search parameters and options that control
the heuristics used by a solver. It is created by calling
:c:func:`yices_new_param_record`.  Individual parameters can be set
using function :c:func:`yices_set_param`. The record can then be
passed as argument to function :c:func:`yices_check_context`. When the
record is no longer needed, it can be deleted by
:c:func:`yices_free_param_record`.

.. c:function:: param_t* yices_new_param_record(void)

   Allocates a parameter record.

   This returns a (pointer to) a record initialized with default settings.

   The record is allocated internally by Yices. It must be freed when
   no-longer used by calling :c:func:`yices_free_param_record`.


.. c:function:: int32_t yices_set_param(param_t* p, const char* name, const char* value)

   Sets a search parameter.

   **Parameters**

   - *p* must be a record returned by :c:func:`yices_new_param_record`.

   - *name* is a parameter name

   - *value* is the value for this parameter

   Both *name* and *value* must be given as ``'\0'``-terminated strings.
   Here are a few examples::

     yices_set_param(p, "branching", "negative");   // branching heuristic
     yices_set_param(p, "randomness", "0.02");      // 2% of random decisions
     yices_set_param(p, "max-interface-eqs", "20");

   The full list of search parameters and possible values for each is given
   in Section :ref:`heuristic_parameters`.

   This function returns -1 if there's an error, or 0 otherwise.

   **Error report**

   - if *name* is not a known parameter

     -- error code: :c:enum:`CTX_UNKNOWN_PARAMETER`

   - if *value* is not valid for the parameter *name*

     -- error code: :c:enum:`CTX_INVALID_PARAMETER_VALUE`


.. c:function:: void yices_default_params_for_context(const context_t *ctx, param_t *p)

   Set all the parameters in record *p* to values appropriate for
   context *ctx*.  The parameter settings depend on the logic
   supported by *ctx* and are based on empirical evaluation on
   benchmarks in the same logic.


.. c:function:: void yices_free_param_record(param_t* param)

   Deletes a parameter record.

   *param* must be a record returned by :c:func:`yices_new_param_record`.

   This function frees the memory allocated to this record.

