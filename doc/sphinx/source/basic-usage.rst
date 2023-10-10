:tocdepth: 2

.. include:: macros

.. highlight:: c

.. _basic_api_usage:

Basic Usage
===========

The Yices distribution includes a few example source files that
illustrate basic use of the Yices library. The code fragments in this
section are from file :file:`examples/example1.c`. This example shows how
to initialize Yices, construct and print terms, create a context and
assert formulas, and build and query a model when a context is
satisfiable.


Global Initialization
---------------------

Before doing anything with Yices, make sure to initialize all internal
data structures by calling function :c:func:`yices_init`. To avoid
memory leaks, you should also call :c:func:`yices_exit` at the end of
your code to free all the memory that Yices has allocated internally.

Here is the corresponding code from :file:`examples/example1.c`::

  int main(void) {
     yices_init();    // Always call this first
     simple_test();
     yices_exit();    // Cleanup 
     return 0;
  }


Type and Term Construction
--------------------------

The following code fragment builds two uninterpreted terms ``x`` and ``y`` of type ``int``::

   type_t int_type = yices_int_type();
   term_t x = yices_new_uninterpreted_term(int_type);
   term_t y = yices_new_uninterpreted_term(int_type);

In Yices, the type and term constructors return objects of type
:c:type:`type_t` and :c:type:`term_t`, respectively. A global variable
is constructed using function
:c:func:`yices_new_uninterpreted_term`.

It is possible to assign a name to any term by calling
:c:func:`yices_set_term_name`.  Since we want to print some terms, it
makes sense to give a name to both the terms ``x`` and ``y``::

   yices_set_term_name(x, "x");
   yices_set_term_name(y, "y");

This has two effects:

  1. The pretty printer will use the names ``"x"`` and ``"y"`` when
     printing these two terms. Otherwise, it would construct names
     such as ``"t!3"`` and ``"t!4"``.

  2. The strings ``"x"`` and ``"y"`` can now be used to retrieve the
     terms ``x`` and ``y``. Yices maintains an internal symbol table
     that maps strings to terms. Calling :c:func:`yices_set_term_name`
     adds an entry in this table.

We can now build a more complex term by using constructors such as
:c:func:`yices_arith_geq0_atom` and :c:func:`yices_and3`::

   term_t f = yices_and3(yices_arith_geq0_atom(x),
                         yices_arith_geq0_atom(y),
                         yices_arith_eq_atom(yices_add(x, y),
                                             yices_int32(100)));

.. only:: format_html

   The resulting term ``f`` is the formula :raw-html:`<em>x &#x2265; 0 &#x2227; y &#x2265; 0 &#x2227; x+y=100</em>`.

.. only:: not format_html

   The resulting term ``f`` is the formula :math:`x \ge 0 \wedge y \ge 0 \wedge x+y=10`.


We can also build the same term by parsing a string::

   term_t f_var = yices_parse_term("(and (>= x 0) (>= y 0) (= (+ x y) 100))");

The input to :c:func:`yices_parse_term` must be an expression in the
Yices syntax (see :ref:`yices_language`). The parser relies on the
symbol table to interpret the two symbols ``"x"`` and ``"y"``. 


Pretty Printing
---------------

Here is a simple function for printing a term on standard output::

  static void print_term(term_t term) {
    int32_t code;

    code = yices_pp_term(stdout, term, 80, 20, 0);
    if (code < 0) {
      // An error occurred
      fprintf(stderr, "Error in print_term: ");
      yices_print_error(stderr);
      exit(1);
    }
  }

This uses the pretty-printing function :c:func:`yices_pp_term`. The
first argument to this function is the output file (here we use
``stdout``).  The second argument is the term to print. The other
three parameters define the pretty-printing area (in this example, a
rectangle of 80 columns and 20 lines).

The example also illustrates the use of the error-reporting functions.
Most functions in the API return a negative number---or another special
value such as :c:macro:`NULL`---to report an error. An internal data structure stores an error
code and other diagnostic information about the most recent
error. Function :c:func:`yices_print_error` reads this data and
prints an error message.


Checking Satisfiability
-----------------------

To check whether formula ``f`` is satisfiable, we create a fresh
context, assert ``f`` in this context, then call function :c:func:`yices_check_context`::

  context_t *ctx = yices_new_context(NULL);
  code = yices_assert_formula(ctx, f);
  if (code < 0) {
    fprintf(stderr, "Assert failed: code = %"PRId32", error = %"PRId32"\n",
            code, yices_error_code());
    yices_print_error(stderr);
  }

  switch (yices_check_context(ctx, NULL)) {
  case SMT_STATUS_SAT:
    printf("The formula is satisfiable\n");
    ...
    break;

  case SMT_STATUS_UNSAT:
    printf("The formula is not satisfiable\n");
    break;

  case SMT_STATUS_UNKNOWN:
    printf("The status is unknown\n");
    break;

  case SMT_STATUS_IDLE:
  case SMT_STATUS_SEARCHING:
  case SMT_STATUS_INTERRUPTED:
  case SMT_STATUS_ERROR:
    fprintf(stderr, "Error in check_context\n");
    yices_print_error(stderr);
    break;
  }
  yices_free_context(ctx);

Function :c:func:`yices_new_context` creates a new context and
function :c:func:`yices_assert_formula` asserts a formula in the
context. Function :c:func:`yices_check_context` returns a code of type
:c:type:`smt_status_t`:
 
   - :c:enum:`SMT_STATUS_SAT` means that the context is satisfiable.

   - :c:enum:`SMT_STATUS_UNSAT` means that the context is not satisfiable.

   - :c:enum:`SMT_STATUS_UNKNOWN` means that the context's status could
     not be determined.

Other codes are error conditions.

Once the context ``ctx`` is no longer needed, we delete it using :c:func:`yices_free_context`.



Building and Querying a Model
-----------------------------

If :c:func:`yices_check_context` returns :c:data:`SMT_STATUS_SAT` (or
:c:data:`SMT_STATUS_UNKNOWN`), we can construct a model of the asserted
formulas by calling :c:func:`yices_get_model`. We then display the
model using :c:func:`yices_pp_model`::

  model_t* model = yices_get_model(ctx, true);
  if (model == NULL) {
    fprintf(stderr, "Error in get_model\n");
    yices_print_error(stderr);
  } else {
    printf("Model\n");
    code = yices_pp_model(stdout, model, 80, 4, 0);

Then, we query the model to get the value of the two terms ``x`` and ``y``::

    int32_t v;
    // get the value of x
    code = yices_get_int32_value(model, x, &v);
    if (code < 0) {
      printf(stderr, "Error in get_int32_value for 'x'\n");
      yices_print_error(stderr);
    } else {
      printf("Value of x = %"PRId32"\n", v);
    }

    // get the value of y
    code = yices_get_int32_value(model, y, &v);
    if (code < 0) {
      fprintf(stderr, "Error in get_int32_value for 'y'\n");
      yices_print_error(stderr);
    } else {
      printf("Value of y = %"PRId32"\n", v);
    }

    yices_free_model(model);

In this case, the values of ``x`` and ``y`` are small integers that
fit in the 32bit integer variable ``v``, so we use function
:c:func:`yices_get_int32_value`. Other functions are available to
extract large integer values (either using 64bit integers or GMP
numbers).

Once we are done with the model, we delete it by calling
:c:func:`yices_free_model`.


Running this Example
--------------------

The source file for this example can be downloaded :download:`here <_static/example1.c>`.
It can be compiled as follows::

  gcc example1.c -o example1 -lyices

Running this example should produce something like this:

.. code-block:: none

  Formula f
  (and (>= x 0) (>= y 0) (= (+ -100 x y) 0))
  Formula f_var
  (and (>= x 0) (>= y 0) (= (+ -100 x y) 0))
  The formula is satisfiable
  Model
  (= x 0)
  (= y 100)
  Value of x = 0
  Value of y = 100


.. warning::

   You may encounter problems if you compile the example with Visual
   Studio on Windows. These problems are caused by incompatibilities
   between the C runtime library of Visual Studio and the one Yices is
   linked against. See https://msdn.microsoft.com/en-us/library/ms235460(v=vs.140).aspx
   for a detailed explanation.

   To avoid these issues, we recommend compiling with mingw.
   It is still possible to use Visual Studio or other compilers on Windows,
   as long as you avoid functions in the Yices API that take a `FILE *`
   argument. File :file:`examples/example1b.c` in the distribution shows
   how to use alternative functions for pretty printing. You can also
   download this file  :download:`here <_static/example1b.c>`.

