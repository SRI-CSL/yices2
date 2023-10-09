:tocdepth: 2

.. include:: macros

.. highlight:: c

.. _formula_operations:

Operations on Formulas
======================

Checking Satisfiability
-----------------------

The standard way of checking whether formulas are satisfiable involves the following four steps:

  1. Construct a context for the relevant logic

  2. Assert the formulas in this context

  3. Call :c:func:`check_context`

  4. Optionally, get a model from the context

Since Yices 2.6.2, the API includes functions that implement these four steps seamlessly.
The new functions also gives access to a new feature of Yices 2.6.2, namely, the use of
third-party Boolean satisfiability solvers for bit-vector problems.


.. c:function:: smt_status_t yices_check_formula(term_t f, const char *logic, model_t **model, const char *delegate)

   Check satisfiability of formula *f*

   This returns :c:enum:`SMT_STATUS_SAT` if *f* is satisfiable,
   :c:enum:`SMT_STATUS_UNSAT` if *f* is not satisfiable,
   or :c:enum:`SMT_STATUS_ERROR` if there is an error.

   **Parameters**

  - *f* must be a Boolean term

  - *logic* must be either NULL or be the name of an SMT logic (like "QF_UFIDL")

  - *model* must be either NULL or be a pointer to a variable in which to store a model

  - *delegate* mut be either NULL or the name of a *delegate*, that is, an external SAT solver

  The function first checks whether *f* is trivially satisifiable or unsatisfiable. If that
  fails, the function performs the four steps listed previously:

  1. Construct a context specialized for the given *logic*.

     If *logic* is NULL, a generic context is used instead with default
     configuration. This context supports linear arithmetic,
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
    if (status == SMT_STATUS_SAT) {
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

    -- term1 := f

  - if *f* is not Boolean

     -- error code: :c:enum:`TYPE_MISMATCH`

     -- term1 := f

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

  - *f* must be an array of Boolean term

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


Export to DIMACS
----------------

It is possible to use Yices to export the results of bit-blasting.
Input to this process is a formula or array of formulas in the QF_BV
logic. Bit-blasting converts this input into a equisatifiable Boolean
formula in Conjunctive Normal Form (CNF). The CNF is exported in the
DIMACS format, which is used by all modern SAT solvers.

Bit-blasting starts by applying simplifications and rewriting rules to
the input problem. This preprocessing may be sufficient to determnine
whether the input is satisfiable or not. In such cases, exporting
to DIMACS cannot be performed as no CNF is constructed.

The following two functions process formulas in the QF_BV logic. They
first perform preprocessing and simplification. If the formulas are
solved by this preprocessing, the functions return the status (either
:c:enum:`SMT_STATUS_SAT` or :c:enum:`SMT_STATUS_UNSAT`). Otherwise, the
functions construct a CNF formula and write it to a file. Optionally,
the functions can perform an extra round of simplification to the CNF
formula before exporting it.

.. c:function:: int32_t yices_export_formula_to_dimacs(term_t f, const char *filename, int32_t simplify_cnf, smt_status_t *status)

   Export a bit-vector formula to CNF

   **Parameters**

   - *f* must be a Boolean term in the QF_BV theory

   - *filename* is the name of a file in which to store the CNF

   - *simplify_cnf* enables CNF simplification using the "y2sat" SAT solver

   - *staus* is a pointer to a variable that will store the formula's status if no DIMACS file is produced.

   **Returned Value**

   The function returns an integer code that indicates whether a
   DIMACS file was produced, or the formula was solved by preprocessing, or an error occurred:

   - a negative code (-1) indicates an error while processing the formula or while writing the DIMACS file.

   - the value 0 means that the formula was solved by preprocessing and that no file was created.

     In this case, the formula's status is returned in variable *status*.

   - the value 1 means that a DIMACS file was successfully generated.

   **Error Reports**

   - if *f* is not a valid term

     -- error code: :c:enum:`INVALID_TERM`

     -- term1 := f

   - if *f* is not Boolean

     -- error code: :c:enum:`TYPE_MISMATCH`

     -- term1 := f

     -- type1 := bool

   - if opening or writing to *filename* failed

     -- error code: :c:enum:`OUTPUT_ERROR`

   Other error codes are possible if *f* is not in the QF_BV theory
  
   If the error code is :c:enum:`OUTPUT_ERROR`, it is possible to get more information on
   the error by using standard functions such as ``perror`` and ``strerror``.


.. c:function:: int32_t yices_export_formulas_to_dimacs(const term_t f[], uint32_t n, const char *filename, int32_t simplify_cnf, smt_status_t *status)

   Export an array of bit-vector formulas to CNF

   This is similar to :c:func:`yices_export_formula_to_dimacs` except that it processes an array of *n* bit-vector formulas.

    **Parameters**

   - *f* must be an array of Boolean terms in the QF_BV theory

   - *n* is the size of array *f*

   - *filename* is the name of a file in which to store the CNF

   - *simplify_cnf* enables CNF simplification using the "y2sat" SAT solver

   - *staus* is a pointer to a variable that will store the formula's status if no DIMACS file is produced.


   The returned code and error reports are the same as :c:func:`yices_export_formula_to_dimacs`.
