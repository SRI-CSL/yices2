:tocdepth: 2

.. include:: macros

.. highlight:: c

.. _formula_operations:

Formula Satisfiability
======================

The standard way of checking whether formulas are satisfiable requires the following steps:

  1. Construct a context for the relevant logic

  2. Assert the formulas in this context

  3. Call :c:func:`check_context`

  4. Optionally, get a model from the context

Since Yices 2.6.2, the API includes functions that implement these four steps seamlessly.
The new functions also gives access to a new feature of Yices 2.6.2, namely, the use of
third-party Boolean satisfiability solvers for bit-vector problems.


.. c:function:: smt_status_t yices_check_formula(term_t f, const char *logic, model_t **model, const char *delegate)

   Check satisfiability of formula *f*

   This returns :c:enum:`STATUS_SAT` if *f* is satisfiable,
   :c:enum:`STATUS_UNSAT` if *f* is not satisfiable,
   or :c:enum:`STATUS_ERROR` if there is an error.

   **Parameters**

  - *f* must be a Boolean term

  - *logic* must be either NULL or be the name of an SMT logic (like "QF_UFIDL")

  - *model* must be either NULL or be a pointer to a variable in which to store a model

  - *delegate* mut be either NULL or the name of a *delegate*, that is, an external SAT solver

  The function first checks whether *f* is trivially satisifiable or unsatisfiable. If that
  fails, the function performs the four steps listed previously:

  1. Constructs a context specialized for the given *logic*. 

     If *logic* is NULL, a generic context is used instead with default
     coniguration. This context supports linear arithmetic,
     bit-vectors, uninterpreted functions, and arrays (see
     _context_operations).

  2. Assert *f* in this context.

  3. Check whether the context is satisfiable.

  4. If the context is satisfiable and *model* is not NULL, the
     function returns a model of *f* in the *model* variable.
 
     This model must be deleted when no-longer needed by calling :c:func:`yices_free_model`.


  **Delegates**

  A delegate is a SAT solver to use as backend when checking satisfiability of a bit-vector
  formula. The *delegate* parameter is ignored and has no effect unless the *logic* is "QF_BV".
  In the latter case, three different delegates can be used:

   - "cadical": the CaDiCaL solver (https://github.com/arminbiere/cadical)

   - "cryptominisat: the CryptoMiniSat solver (https://github.com/msoos/cryptominisat)

   - "y2sat": an experimental SAT solver included in Yices

   These three delegates are known to Yices but support for CaDiCaL and CryptoMiniSat is optional.
   They may or may not be available depending on how the Yices library was configured and compiled.
   The "y2sat" delegate is always available.

   If *delegate* is NULL, the default SAT solver internal to Yices is used (which can be much slower
   than state-of-the-art solvers such as CaDiCaL).


  **Examples**

  The following code fragment shows how to check satisfiability of a
  formula *f* in the QF_LRA theory and obtain a model::

    model_t *result;
    smt_status_t status = yices_check_formula(f, "QF_LRA", &result, NULL);
    if (status == STATUS_SAT) {
       // a model is returned in result
       yices_pp_model(stdout, result, 100, 100, 0);
       ...
       // delete the model when we don't need it
       yices_free_model(result);
    } 

  If the model is not needed, call the function as follows::

    smt_status_t status = yices_check_formula(f, "QF_LRA", NULL, NULL);


  For a bitvector formula *f*, we can pass a delegate as follows::

    smt_status_t status = yices_check_formula(f, "QF_BV", &result, "cadical");

  
  **Error report**
  
  - if *f* is not a valid term

    -- error code: :c:enum:`INVALID_TERM`

    -- term1 := t

  - if *t* is not Boolean

     -- error code: :c:enum:`TYPE_MISMATCH`

     -- term1 := t

     -- type1 := bool

  - if *logic* is not recognized

     -- error code: :c:enum:`CTX_UNKNOWN_LOGIC`

  - if *logic* is known but not supported

     -- error code: :c:enum:`CTX_LOGIC_NOT_SUPPORTED`

  - if *logic* is "QF_BV" and *delegate* is not recognized

     -- error code: :c:enum:`CTX_UNKNOWN_DELEGATE`

  - if *logic* is "QF_BV" and *delegate* is known but is not supported

     -- error code: :c:enum:`CTX_DELEGATE_NOT_AVAILABLE`

  - other codes are possible if the formula cannot be processed by the context.



.. c:function:: smt_status_t yices_check_formulas(const term_t f[], uint32_t n, const char *logic, model_t **model, const char *delegate)

   Check satisfiability of an array formula *f*

   This is similar to :c:func:`yices_check_formula` except that it checks satisfiability of a conjunction of *n* formulas.


   **Parameters**

  - *f* must be an array of  Boolean term

  - *n* is the size of array *f*

  - *logic* must be either NULL or be the name of an SMT logic (like "QF_UFIDL")

  - *model* must be either NULL or be a pointer to a variable in which to store a model

  - *delegate* mut be either NULL or the name of a *delegate*, that is, an external SAT solver

  
  The last three parameters have the same meaning as in :c:func:`yices_check_formula`. The returned value
  and error codes are as in this function too.


.. c:function:: int32_t yices_has_delegate(const char *delegate)

  Check whether the given *delegate* is supported.

  Return 0 if *delegate* is not the name of a known delegate, or if it's known but not
  available in this version of the Yices library.

  Return 1 if *delegate* is NULL or if it's the name of a delegate that's available in
  this version of the Yices library.
