:tocdepth: 2

.. include:: macros

.. highlight:: c

.. _term_operations:

Terms
=====

The API provides constructors for terms defined in the Yices language.
There are no special constructs for formulas; formulas are terms of
Boolean type.  The semantics and type-checking rules of the language
are explained in the `manual
<https://yices.csl.sri.com/papers/manual.pdf>`_.

All term constructors return an object of type :c:type:`term_t`. They
check their arguments, perform type checking, and return
:c:macro:`NULL_TERM` if there's an error. The functions listed in Section
:ref:`error_reports` can then be used to diagnose the error or print
an error message. 

If there's no error, the constructors apply rewriting and simplification
procedures, then return an index in the global term table maintained
within Yices. This index uniquely identifies the resulting term.
Since Yices uses hash consing, two terms that are syntactically
identical (after rewriting and simplification) are represented by the
same index.

.. warning:: Some functions take an array of terms as argument. If this
             array is not declared as ``const term_t a[]`` then the
             function may modify the array.

**Common error reports**

All functions in this section may report the following errors.

  - When a parameter to the functions is not a valid term, the error
    report is set as follow:

    -- error code: :c:enum:`INVALID_TERM`

    -- term1 := the invalid term

  - If a type parameter is invalid:

    -- error code: :c:enum:`INVALID_TYPE`

    -- type1 := the invalid type

  - When a parameter *t* to a function does not match a type *tau*, the 
    type error is reported as follows:

    -- error code: :c:enum:`TYPE_MISMATCH`

    -- term1 := *t*

    -- type1 := *tau* (i.e., the expected type)

  - Some functions expect arguments of compatible types. In
    particular, many bitvector constructors require bitvector
    arguments of the same size (i.e., the same number of bits). If two
    arguments *t1* and *t2* do not have compatible types the error
    report is:

    -- error code: :c:enum:`INCOMPATIBLE_TYPES`

    -- term1 := *t1*

    -- type1 := *t1* 's type

    -- term2 := *t2*

    -- type2 := *t2* 's type

  - If an integer parameter that must be positive is given the value zero:

    -- error code: :c:enum:`POS_INT_REQUIRED`

    -- badval := 0

  - The arithmetic constructors expect arguments of type integer or real.
    If they are given a term *t* of a different type, they report the
    following error:

    -- error code: :c:enum:`ARITHTERM_REQUIRED`

    -- term1 := *t*

  - Several constructors have a parameter that specifies a bitvector
    size (i.e., number of bits). This number *n* must be positive and no more
    than :c:macro:`YICES_MAX_BVSIZE`. If *n* is more than this limit, the
    following error is reported:

    -- error code: :c:enum:`MAX_BVSIZE_EXCEEDED`

    -- badval := *n*

  - When a bitvector constructor is given a term *t* that's not a bitvector:

    -- error code: :c:enum:`BITVECTOR_REQUIRED`

    -- term1 := *t*

Other error reports may be produced by the term constructors.
They are indicated after the function signature.




General Constructors
--------------------

.. c:function:: term_t yices_new_uninterpreted_term(type_t tau)

   Returns a new uninterpreted term of type *tau*.

   An uninterpreted term is like a global variable of type *tau*. If
   *tau* is a function type, the resulting term is an uninterpreted
   function of type *tau*.

   Optionally, you can give a name to new uninterpreted terms.  using the
   functions defined in :ref:`names_api`. This makes pretty printing nicer
   and it is useful if you want to construct terms using the parsing
   functions (see :ref:`parsing_api`).


.. c:function:: term_t yices_new_variable(type_t tau)

   Returns a fresh variable of type *tau*.

   Variables are different from uninterpreted terms and are reserved
   for use in quantifiers and lambda terms. They can also be used to
   define term substitutions.


.. c:function:: term_t yices_constant(type_t tau, int32_t i)

   Returns the constant of type *tau* and index *i*.

   **Parameters**

   - *tau* must be either a scalar type or an uninterpreted type

   - *i* must be non-negative and, if *tau* is scalar, *i* must be less
     than *tau*'s cardinality

   **Error report**

   - If *tau* is not scalar or uninterpreted

     -- error code: :c:enum:`SCALAR_OR_UTYPE_REQUIRED`

     -- type1 := *tau*

   - If *i* is negative or too large for type *tau*

     -- error code: :c:enum:`INVALID_CONSTANT_INDEX`

     -- type1 := *tau*

     -- badval := *i*

   This function creates constants of uninterpreted or scalar
   types. Within each such type, the constants are identified by a
   non-negative index *i*. Two constants with distinct indices are
   semantically distinct terms.

   A scalar type *tau* has finite cardinality so the number of
   constants of type *tau* is limited. There is no such restriction
   if *tau* is an uninterpreted type.

.. c:function:: term_t yices_ite(term_t c, term_t t1, term_t t2)

   Returns the term *(ite c t1 t2)*  which means *if c then t1 else t2*.

   **Parameters**

   - *c* must be a Boolean term

   - *t1* and *t2* must be two terms of compatible types


.. c:function:: term_t yices_eq(term_t t1, term_t t2)

   Returns the Boolean term *(= t1 t2)*.

   The terms *t1* and *t2* must have compatible types


.. c:function:: term_t yices_neq(term_t t1, term_t t2)

   Returns the Boolean term *(/= t1 t2)*.

   The terms *t1* and *t2* must have compatible types


.. c:function:: term_t yices_distinct(uint32_t n, term_t arg[])

   Returns the term *(distinct arg[0] ... arg[n-1])*.

   **Parameters**

   - *n* is the size of array *arg*. It must be positive and no more
     than :c:macro:`YICES_MAX_ARITY`.

   - *arg* is an array of *n* terms. All elements of *arg* must have
     compatible types.

   If *n* is 1, this function returns *true*.

   **Error report**

   - If *n* is more than :c:macro:`YICES_MAX_ARITY`:

     -- error code: :c:enum:`TOO_MANY_ARGUMENTS`

     -- badval: *n*

   **Warning**

   -  Array *arg* may be modified.
    

.. c:function:: term_t yices_application(term_t fun, uint32_t n, const term_t arg[])

   Constructs the term *(fun arg[0] ... arg[n-1])*.

   This applies function *fun* to the arguments *arg[0] ... arg[n-1]*,
   where *fun* can be any term of function type. For example, *fun*
   may be an uninterpreted function constructed using
   :c:func:`yices_new_uninterpreted_term` or a lambda term created
   using :c:func:`yices_lambda`.

   If *fun* is a lambda term, then this constructor applies beta
   reduction.

   **Parameters**

   - *fun*: term of function type

   - *n*: number of arguments

   - *arg[0] ... arg[n-1]*: arguments

   The parameter *n* must be equal to the arity of function *fun*, and
   the arguments *arg[0] ... arg[n-1]* must have types that match the
   function signature. More precisely, if *fun* has
   type (-> |tau|\ |_1| |...| |tau|\ |_n| |sigma|) then *arg[i]*'s type must 
   be a subtype of |tau|\ |_i+1|.

   **Error report**

   - If *fun* does not have function type

     -- error code: :c:enum:`FUNCTION_REQUIRED`
 
     -- term1 := *fun*

   - If *n* is different from *fun*'s arity

     -- error code: :c:enum:`WRONG_NUMBER_OF_ARGUMENTS`

     -- badval := *n*


.. c:function:: term_t yices_application1(term_t fun, term_t arg1)

   Returns the term *(fun arg1)*.

   This function applies a unary function *fun* to term *arg1*.

   It is equivalent to :c:func:`yices_application` with *n=1*.


.. c:function:: term_t yices_application2(term_t fun, term_t arg1, term_t arg2)

   Returns the term *(fun arg1 arg2)*.

   This function applies binary function *fun* to the terms *arg1* and *arg2*. 

   It is equivalent to :c:func:`yices_application` with *n=2*.


.. c:function:: term_t yices_application3(term_t fun, term_t arg1, term_t arg2, term_t arg3)

   Returns the term *(fun arg1 arg2 arg3)*.

   This function applies ternary function *fun* to *arg1*, *arg2*, and *arg3*. 

   It is equivalent to :c:func:`yices_application` with *n=3*.


.. c:function:: term_t yices_tuple(uint32_t n, const term_t arg[])

   Returns the tuple term *(mk-tuple arg[0] ... arg[n-1])*.

   **Parameters**

   - *n* is the number of components. It must be positive and no more than :c:macro:`YICES_MAX_ARITY`

   - *arg*: array of *n* terms

   **Error report**

   - If *n* is more than :c:macro:`YICES_MAX_ARITY`

     -- error code: :c:enum:`TOO_MANY_ARGUMENTS`

     -- badval := n


.. c:function:: term_t yices_pair(term_t t1, term_t t2)

   Returns the pair *(mk-tuple t1 t2)*.

   This function is equivalent to :c:func:`yices_tuple` with *n=2*.


.. c:function:: term_t yices_triple(term_t t1, term_t t2, term_t t3)

   Returns the triple *(mk-tuple t1 t2 t3)*.

   This function is equivalent to :c:func:`yices_tuple` with *n=3*.


.. c:function:: term_t yices_select(uint32_t i, term_t t)

   Returns the term *(select t i)*.

   This function extracts the *i*-th component of a tuple *t*. 

   **Parameters**

   - *i* must be an index between 1 and N (where N is the number of components of *t*)

   - *t* must be a term of tuple type

   **Error report**

   - If *t* is does not have tuple type

     -- error code: :c:enum:`TUPLE_REQUIRED`

     -- term1 := *t*

   - If *i* is zero or larger than N:

     -- error code: :c:enum:`INVALID_TUPLE_INDEX`

     -- type1 := type of *t*

     -- badval := *i*


.. c:function:: term_t yices_tuple_update(term_t t, uint32_t i, term_t v)

   Creates the term *(tuple-update t i v)*.

   The result is the tuple obtained by replacing the *i*-th component
   of tuple *t* by *v*.

   **Parameters**

   - *t* must be a term of tuple type

   - *i* must be an index between 1 and N, where N is the number of components in *t*

   - If *t*'s type is *(tuple* |tau|\ |_1| |...| |tau|\ |_i| |...| |tau|\ |_n| *)* then *v*'s type 
     must be a subtype of |tau|\ |_i|

   **Error report**

   - If *t* does not have a tuple type

     -- error code: :c:enum:`TUPLE_REQUIRED`

     -- term1 := *t*

   - If *i* is zero or larger than N:

     -- error code: :c:enum:`INVALID_TUPLE_INDEX`

     -- type1 := type of *t*

     -- badval := *i*    

   - If *v*'s type is incorrect, the error code is :c:enum:`TYPE_MISMATCH`


.. c:function:: term_t yices_update(term_t fun, uint32_t n, const term_t arg[], term_t v)

   Creates the function update *(update fun (arg[0] ... arg[n-1]) v)*.

   The result is the function that has the same value as *fun* at all points in its domain,
   except at point *(arg[0] ... arg[n-1])*. At this point, the function returns *v*.

   **Parameters**

   - *fun* must be a term of function type
 
   - *n* is the size of array *arg*; it must be positive and equal to the arity of *fun*

   - *arg* is an array of *n* terms

   - *v* is a term (the new value)

   As in :c:func:`yices_application`, the arguments *arg[0] ... arg[n-1]* must have
   types that match the signature of *fun*. In addition, *v*'s type must be a subtype of 
   the function range.

   **Error report**

   - If *fun* does not have function type

     -- error code: :c:enum:`FUNCTION_REQUIRED`

     -- term1 := *fun*

   - If *n* is different from *fun*'s arity

     -- error code: :c:enum:`WRONG_NUMBER_OF_ARGUMENTS`

     -- badval := *n*

   This constructor is often used to encode the operation of writing
   into an array.  Yices does not have special types for arrays and an
   array is the same as a function.  Under this interpretation, the
   function *fun* above is an array with *n* dimensions, and the update
   operation writes the value *v* at the index *(arg[0]
   ... arg[n-1])*.  The result is a new array.

   

.. c:function:: term_t yices_update1(term_t fun, term_t arg1, term_t v)

   Creates the function update *(update fun (arg1) v)*.

   This constructor is equivalent to :c:func:`yices_update` for
   functions of arity *n=1* (or single-dimensional arrays).


.. c:function:: term_t yices_update2(term_t fun, term_t arg1, term_t arg2, term_t v)

   Creates the function update *(update fun (arg1 arg2) v)*.

   This constructor is equivalent to :c:func:`yices_update` for
   functions of arity *n=2* (or two-dimensional arrays).


.. c:function:: term_t yices_update3(term_t fun, term_t arg1, term_t arg2, term_t arg3, term_t v)

   Creates the function update *(update fun (arg1 arg2 arg3) v)*.

   This constructor is equivalent to :c:func:`yices_update` for
   functions of arity *n=3* (or three-dimensional arrays).


.. c:function:: term_t yices_forall(uint32_t n, term_t var[], term_t body)

   Creates the quantified term: *(forall (var[0] ... var[n-1]) body)*.

   **Parameters**

   - *n* is the number of variables

   - *var* must be an array of *n* variables

   - *body* must be a Boolean term

   Parameter *n* must be positive and no more than :c:macro:`YICES_MAX_VARS`.

   All the elements in array *var* must be constructed with function :c:enum:`yices_new_variable`,
   and the array must not contain duplicate elements.

   **Error report**

   - If *n* is more than :c:macro:`YICES_MAX_VARS`:

     -- error code: :c:enum:`TOO_MANY_VARS`

     -- badval := *n*

   - If one *var[i]* is not a variable:

     -- error code: :c:enum:`VARIABLE_REQUIRED`

     -- term1 := *var[i]*

   - If a variable *x* occurs twice in array *var*:

     -- error code: :c:enum:`DUPLICATE_VARIABLE`

     -- term1 := *x*

   **Warning**

   - Array *var* may be modified.

.. c:function:: term_t yices_exists(uint32_t n, term_t var[], term_t body)

   Creates the quantified term *(exists (var[0] ... var[n-1]) body)*.

   This function is similar to :c:func:`yices_forall`. The parameters
   must satisfy the same constraints, and the possible error reports
   are the same.

   **Warning**

   - Array *var* may be modified.

.. c:function:: term_t yices_lambda(uint32_t n, const term_t var[], term_t body)

   Creates the lambda term *(lambda (var[0] ... var[n-1]) body)*.

   **Parameters**

   - *n* is the number of variables.

   - *var* is an array of *n* variables.

   - *body* can be any term

   The parameter *n* must be positive and no more than :c:enum:`YICES_MAX_VARS`

   As in constructors :c:func:`yices_forall` and
   :c:func:`yices_exists`, all the elements in array *var* must be
   constructed with function :c:enum:`yices_new_variable`, and the
   array must not contain duplicate elements.

   **Error report**

   - If *n* is more than :c:macro:`YICES_MAX_VARS`:

     -- error code: :c:enum:`TOO_MANY_VARS`

     -- badval := *n*

   - If one *var[i]* is not a variable:

     -- error code: :c:enum:`VARIABLE_REQUIRED`

     -- term1 := *var[i]*

   - If a variable *x* occurs twice in array *var*:

     -- error code: :c:enum:`DUPLICATE_VARIABLE`

     -- term1 := *x*

   
   

Boolean Terms
-------------

.. c:function:: term_t yices_true(void)

   Returns the Boolean constant *true*.

.. c:function:: term_t yices_false(void)

   Returns the Boolean constant *false*.

.. c:function:: term_t yices_not(term_t arg)

   Returns the term *(not arg)*.

   **Parameter**

   - *arg* must be a Boolean term

.. c:function:: term_t yices_and(uint32_t n, term_t arg[])

   Constructs the conjunction *(and arg[0] ... arg[n-1])*.

   **Parameters**

   - *n* is the number of arguments. It must be positive and no more than :c:macro:`YICES_MAX_ARITY`.

   - *arg* must be an array of *n* Boolean terms

   **Error report**

   - If *n* is more than :c:macro:`YICES_MAX_ARITY`:

     -- error code: :c:enum:`TOO_MANY_ARGUMENTS`

     -- badval: *n*

   **Warning**

   -  Array *arg* may be modified.
    
.. c:function:: term_t yices_and2(term_t t1, term_t t2)

   Constructs the term *(and t1 t2)*.
 
   This function is equivalent to :c:func:`yices_and` with *n=2*.

   **Parameters**

   - *t1* and *t2* must be Boolean terms


.. c:function:: term_t yices_and3(term_t t1, term_t t2, term_t t3)

   Constructs the term *(and t1 t2 t3)*.
 
   This function is equivalent to :c:func:`yices_and` with *n=3*.

   **Parameters**

   - *t1*, *t2*, and *t3* must be Boolean terms


.. c:function:: term_t yices_or(uint32_t n, term_t arg[])

   Constructs the disjunction *(or arg[0] ... arg[n-1])*.

   **Parameters**

   - *n* is the number of arguments. It must be positive and no more than :c:macro:`YICES_MAX_ARITY`.

   - *arg* must be an array of *n* Boolean terms

   **Error report**

   - If *n* is more than :c:macro:`YICES_MAX_ARITY`:

     -- error code: :c:enum:`TOO_MANY_ARGUMENTS`

     -- badval: *n*

   **Warning**

   -  Array *arg* may be modified.
    

.. c:function:: term_t yices_or2(term_t t1, term_t t2)

   Constructs the term *(or t1 t2)*.
 
   This function is equivalent to :c:func:`yices_or` with *n=2*.

   **Parameters**

   - *t1* and *t2* must be Boolean terms


.. c:function:: term_t yices_or3(term_t t1, term_t t2, term_t t3)

   Constructs the term *(or t1 t2 t3)*.
 
   This function is equivalent to :c:func:`yices_or` with *n=3*.

   **Parameters**

   - *t1*, *t2*, and *t3* must be Boolean terms


.. c:function:: term_t yices_xor(uint32_t n, term_t arg[])

   Constructs the exclusive or *(xor arg[0] ... arg[n-1])*.

   **Parameters**

   - *n* is the number of arguments. It must be positive and no more than :c:macro:`YICES_MAX_ARITY`.

   - *arg* must be an array of *n* Boolean terms

   **Error report**

   - If *n* is more than :c:macro:`YICES_MAX_ARITY`:

     -- error code: :c:enum:`TOO_MANY_ARGUMENTS`

     -- badval: *n*

   **Warning**

   -  Array *arg* may be modified.
    

.. c:function:: term_t yices_xor2(term_t t1, term_t t2)

   Constructs the term *(xor t1 t2)*.
 
   This function is equivalent to :c:func:`yices_xor` with *n=2*.

   **Parameters**

   - *t1* and *t2* must be Boolean terms

.. c:function:: term_t yices_xor3(term_t t1, term_t t2, term_t t3)

   Constructs the term *(xor t1 t2 t3)*.
 
   This function is equivalent to :c:func:`yices_xor` with *n=3*.

   **Parameters**

   - *t1*, *t2*, and *t3* must be Boolean terms


.. c:function:: term_t yices_iff(term_t t1, term_t t2)

   Constructs the equivalence *(<=> t1 t2)*.

   **Parameters**

   - *t1* and *t2* must be Boolean terms


.. c:function:: term_t yices_implies(term_t t1, term_t t2)

   Constructs the implication *(=> t1 t2)*  (i.e. *t1 implies t2*).

   **Parameters**

   - *t1* and *t2* must be Boolean terms



Arithmetic Terms
----------------

.. c:function:: term_t yices_zero(void)

   Returns the integer constant 0.

.. c:function:: term_t yices_int32(int32_t val)

   Converts *val* to a constant integer term.

.. c:function:: term_t yices_int64(int64_t val)

   Converts *val* to a constant integer term.

.. c:function:: term_t yices_rational32(int32_t num, uint32_t den)

   Creates the rational constant *num/den*.

   The parameter *den* must be positive.

   **Error report**

   - If *den* is zero:

     -- error code: :c:enum:`DIVISION_BY_ZERO`

.. c:function:: term_t yices_rational64(int64_t num, uint64_t den)

   Creates the rational constant *num/den*.

   The parameter *den* must be positive.

   **Error report**

   - If *den* is zero:

     -- error code: :c:enum:`DIVISION_BY_ZERO`

.. c:function:: term_t yices_mpz(const mpz_t z)

   Converts the GMP integer *z* into a constant integer term.

   **Note**

   - This function is not declared unless you include :file:`gmp.h`
     before :file:`yices.h` in your code::

         #include <gmp.h>
         #include <yices.h>

 
.. c:function:: term_t yices_mpq(const mpq_t q)

   Converts the GMP rational *q* into a constant rational term.

   The parameter *q* must be in canonical form (cf. the `GMP
   <http://gmplib.org>`_ documentation).

   Like the previous function, you must include :file:`gmp.h` before
   :file:`yices.h` to ensure that this function is declared.

.. c:function:: term_t yices_parse_rational(const char *s)

   Converts string *s* into a rational or integer term.

   **Parameter**

   - The string *s* must be in the following format:

      .. code-block:: none

            <sign> <digits>/<digits>
         or <sign> <digits>

     -- the ``<sign>`` can be either ``+`` or ``-`` or nothing

     -- and ``<digits>`` must be a sequence of decimal digits.

     For example, ``"+1230/8939"``, ``"1/4"``, and ``"-10000"`` are in this format.

   **Error report**

   - If *s* is not in the right format:

     -- error code: :c:enum:`INVALID_RATIONAL_FORMAT`

   - If the denominator is zero:

     -- error code: :c:enum:`DIVISION_BY_ZERO`


.. c:function:: term_t yices_parse_float(const char *s)

   Converts string *s* into a rational or integer term.

   **Parameter**

   - The string *s* must be in the following floating-point format:

      .. code-block:: none

             <sign><digits>.<digits>
         or  <sign><digits><exp><sign><digits>
         or  <sign><digits>.<digits><exp><sign><digits>

     -- the ``<sign>`` can be either ``+`` or ``-`` or nothing

     -- the ``<exp>`` can be either ``e`` or ``E``

     For example, ``"+1.04e5"`` or ``"-4E-3"`` are valid input for
     this function.

   The string is converted to a rational or integer constant. Yices
   does not use floating point numbers internally.

   **Error report**

   - If *s* is not in the right format:

     -- error code: :c:enum:`INVALID_FLOAT_FORMAT`


.. c:function:: term_t yices_add(term_t t1, term_t t2)

   Returns the sum *(+ t1 t2)*.

.. c:function:: term_t yices_sub(term_t t1, term_t t2)

   Returns the difference *(- t1 t2)*.

.. c:function:: term_t yices_neg(term_t t1)

   Returns the opposite of *t1*.

.. c:function:: term_t yices_mul(term_t t1, term_t t2)

   Returns the product *(\* t1 t2)*.

   **Error report**

   - If the result has degree *n* that's more than :c:macro:`YICES_MAX_DEGREE`

     -- error code: :c:enum:`DEGREE_OVERFLOW`

     -- badval := *n*

.. c:function:: term_t yices_square(term_t t1)

   Returns the square of *t1*.

   - If the result has degree *n* that's more than :c:macro:`YICES_MAX_DEGREE`

     -- error code: :c:enum:`DEGREE_OVERFLOW`

     -- badval := *n*

.. c:function:: term_t yices_power(term_t t1, uint32_t d)

   Raises *t1* to power *d*.

   When *d* is zero, this function returns the constant 1 even if *t1* is zero.

   **Error report**

   - If the result has degree *n* that's more than :c:macro:`YICES_MAX_DEGREE`

     -- error code: :c:enum:`DEGREE_OVERFLOW`

     -- badval := *n*

.. c:function:: term_t yices_division(term_t t1, term_t t2)

   Constructs the quotient *(/ t1 t2)*.
 
   **Parameters**

   - *t1* amd *t2* must be arithmetic terms


   Until version 2.5.0, Yices supported only division by non-zero constants.
   Division by arbitrary arithmetic terms is now supported (and can be handled
   by Yices's solver for non-linear arithmetic).


.. c:function:: term_t yices_sum(uint32_t n, const term_t t[])

   Constructs the sum *(+ t[0] ... t[n-1])*.

   **Parameters**

   - *n* is the size of array *t*

   - *t* must be an array of *n* arithmetic terms

   This generalizes function :c:func:`yices_add` to *n* arguments. The
   array may be empty (i.e., *n* may be zero), in which case the
   function returns 0.

.. c:function:: term_t yices_product(uint32_t n, const term_t t[])

   Constructs the product *(\* t[0] ... t[n-1])*.

   **Parameters**

   - *n* is the size of array *t*

   - *t* must be an array of *n* arithmetic terms

   This generalizes function :c:func:`yices_mul` to *n* arguments.
   If *n* is zero, the function returns 1.

.. c:function:: term_t yices_poly_int32(uint32_t n, const int32_t a[], const term_t t[])

   Creates the linear polynomial *(+ (\* a[0] t[0]) ... (\* a[n-1] t[n-1))*.

   **Parameters**

   - *n* is the number of terms in the sum

   - *a* must be an array of *n* integer coefficients (of 32bits)

   - *t* must be an array of *n* arithmetic terms

.. c:function:: term_t yices_poly_int64(uint32_t n, const int64_t a[], const term_t t[])

   Creates the linear polynomial *(+ (\* a[0] t[0]) ... (\* a[n-1] t[n-1))*.

   **Parameters**

   - *n* is the number of terms in the sum

   - *a* must be an array of *n* integer coefficients (of 64bits)

   - *t* must be an array of *n* arithmetic terms


.. c:function:: term_t yices_poly_rational32(uint32_t n, const int32_t num[], const uint32_t den[], const term_t t[])

   Creates the linear polynomial *(+ (\* a[0] t[0]) ... (\* a[n-1] t[n-1))*,

   where coefficient *a[i]* is given by *num[i]/den[i]*.   

   **Parameters**

   - *n* is the number of terms in the sum

   - *num* and *den* must be two arrays of *n* integers (of 32bits)

   - *t* must be an array of *n* arithmetic terms

   - No element of array *den* can be zero

   **Error report**

   - If a denominator *den[i]* is zero:

     -- error code: :c:enum:`DIVISION_BY_ZERO`

.. c:function:: term_t yices_poly_rational64(uint32_t n, const int64_t num[], const uint64_t den[], const term_t t[])

   Creates the linear polynomial *(+ (\* a[0] t[0]) ... (\* a[n-1] t[n-1))*,

   where coefficient *a[i]* is given by *num[i]/den[i]*.   

   **Parameters**

   - *n* is the number of terms in the sum

   - *num* and *den* must be two arrays of *n* integers (of 64bits)

   - *t* must be an array of *n* arithmetic terms

   - No element of array *den* can be zero

   **Error report**

   - If a denominator *den[i]* is zero:

     -- error code: :c:enum:`DIVISION_BY_ZERO`

.. c:function:: term_t yices_poly_mpz(uint32_t n, const mpz_t z[], const term_t t[])

   Creates the linear polynomial *(+ (\* z[0] t[0]) ... (\* z[n-1] t[n-1])*,

   where the coefficients *z[i]* are GMP integers.

   **Parameters**

   - *n* is the number of terms in the sum

   - *z* must be an array of *n* GMP integers

   - *t* must be an array of *n* arithmetic terms

   This function is not declared unless you include :file:`gmp.h` before
   :file:`yices.h` in your code. See :c:func:`yices_mpz`.

.. c:function:: term_t yices_poly_mpq(uint32_t n, const mpq_t q[], const term_t t[])

   Creates the linear polynomial *(+ (\* q[0] t[0]) ... (\* q[n-1] t[n-1])*

   where the coefficients *q[i]* are GMP rationals.

   **Parameters**

   - *n* is the number of terms in the sum

   - *q* must be an array of *n* GMP rationals

   - *t* must be an array of *n* arithmetic terms

   - All the elements of *q* must be canonicalized

   Like the previous function, you must include the header
   :file:`gmp.h` before including :file:`yices.h` to ensure that
   this function is declared.

.. c:function:: term_t yices_abs(term_t t)

   Absolute value: *(abs t)*

   **Parameter**

   - *t* must be an arithmetic term


.. c:function:: term_t yices_floor(term_t t)

   Floor: *(floor t)*

   **Parameter**

   - *t* must be an arithmetic term

   The resulting term has integer type. It denotes the largest integer that's 
   smaller than or equal to *t*.


.. c:function:: term_t yices_ceil(term_t t)

   Ceiling: *(ceil t)*

   **Parameter**

   - *t* must be an arithmetic term

   The resulting term has integer type. It denotes the smallest integer that's 
   larger than or equal to *t*.


.. c:function:: term_t yices_idiv(term_t t1, term_t t2)

   Integer division *(div t1 t2)*

   **Parameters**

   - *t1* and *t2* msut be arithmetic terms

   The resulting term has type integer.

   If *t2* is positive, then *(div t1 t2)* is equal to *(floor (/ t1 t2))*.

   If *t2* is negative, then *(div t1 t2)* is equal to *(ceil (/ t1 t2))*.


   Until version 2.5.0, Yices supported only division by non-zero constants.
   Division by arbitrary arithmetic terms is now supported (and can be handled
   by Yices's solver for non-linear arithmetic).


.. c:function:: term_t yices_imod(term_t t1, term_t t2)

   Modulo: *(mod t1 t2)*

   **Parameters**

   - *t1* and *t2* must be arithmetic terms

   The resulting term is equal to *(- t1 (\* t2 (div t1 t2)))*.

   **Note**

   - Until version 2.5.0, Yices supported only division by non-zero constants.
     Division by arbitrary arithmetic terms is now supported (and can be handled
     by Yices's solver for non-linear arithmetic).



.. c:function:: term_t yices_arith_eq_atom(term_t t1, term_t t2)

   Creates the arithmetic equality *(= t1 t2)*.

.. c:function:: term_t yices_arith_neq_atom(term_t t1, term_t t2)

   Creates the arithmetic disequality *(/= t1 t2)*.

.. c:function:: term_t yices_arith_geq_atom(term_t t1, term_t t2)

   Creates the inequality *(>= t1 t2)*.

.. c:function:: term_t yices_arith_leq_atom(term_t t1, term_t t2)

   Creates the inequality *(<= t1 t2)*.

.. c:function:: term_t yices_arith_gt_atom(term_t t1, term_t t2)

   Creates the inequality *(> t1 t2)*.

.. c:function:: term_t yices_arith_lt_atom(term_t t1, term_t t2)

   Creates the inequality *(< t1 t2)*.

.. c:function:: term_t yices_arith_eq0_atom(term_t t)

   Creates the equality *(= t 0)*.

.. c:function:: term_t yices_arith_neq0_atom(term_t t)

   Creates the disequality *(/= t 0)*.

.. c:function:: term_t yices_arith_geq0_atom(term_t t)

   Creates the inequality *(>= t 0)*.

.. c:function:: term_t yices_arith_leq0_atom(term_t t)

   Creates the inequality *(<= t 0)*.

.. c:function:: term_t yices_arith_gt0_atom(term_t t)

   Creates the inequality *(> t 0)*.

.. c:function:: term_t yices_arith_lt0_atom(term_t t)

   Creates the inequality *(< t 0)*.


.. c:function:: term_t yices_divides_atom(term_t t1, term_t t2)

   Divisibility test: *(divides t1 t2)*

   **Parameters**

   - *t1* must be an arithmetic constant

   - *t2* must be an arithmetic term

   This constructs the Boolean term *(divides t1 t2)*, which is true
   iff *t2* is of the form *n.t2* for some integer *n*.

   **Error report**

   - if *t1* is not an arithmetic constant:

     -- error code: :c:enum:`ARITHCONSTANT_REQUIRED`

.. c:function:: term_t yices_is_int_atom(term_t t)

   Integrality test

   This constructs the atom *(is-int t)*, which is true iff *t* is an
   integer.


Bitvector Terms
---------------

.. c:function:: term_t yices_bvconst_uint32(uint32_t n, uint32_t x)

   Converts unsigned 32bit integer *x* into a bitvector constant.

   **Parameters**

   - *n* is the number of bits in the constant.

   - *x* is the value.

   The parameter *n* must be positive and no more than :c:macro:`YICES_MAX_BVSIZE`.

   If *n* is less than 32, then the value *x* is truncated to *n* bits
   (i.e., the result is formed by taking the *n* least significant
   bits of *x*).

   If *n* is more than 32, then the value *x* is zero-extended to *n* bits.

.. c:function:: term_t yices_bvconst_uint64(uint32_t n, uint64_t x)

   Converts unsigned 64bit integer *x* into a bitvector constant.

   **Parameters**

   - *n* is the number of bits in the constant.

   - *x* is the value.

   The parameter *n* must be positive and no more than :c:macro:`YICES_MAX_BVSIZE`.

   If *n* is less than 64, then the value *x* is truncated to *n* bits
   (i.e., the result is formed by taking the *n* least significant
   bits of *x*).

   If *n* is more than 64, then the value *x* is zero-extended to *n* bits.

.. c:function:: term_t yices_bvconst_int32(uint32_t n, int32_t x)

   Converts signed 32bit integer *x* into a bitvector constant.

   **Parameters**

   - *n* is the number of bits in the constant.

   - *x* is the value.

   The parameter *n* must be positive and no more than :c:macro:`YICES_MAX_BVSIZE`.

   If *n* is less than 32, then the value *x* is truncated to *n* bits
   (i.e., the result is formed by taking the *n* least significant
   bits of *x*).

   If *n* is more than 32, then the value *x* is sign-extended to *n* bits.

.. c:function:: term_t yices_bvconst_int64(uint32_t n, int64_t x)

   Converts signed 64bit integer *x* into a bitvector constant.

   **Parameters**

   - *n* is the number of bits in the constant.

   - *x* is the value.

   The parameter *n* must be positive and no more than :c:macro:`YICES_MAX_BVSIZE`.

   If *n* is less than 64, then the value *x* is truncated to *n* bits
   (i.e., the result is formed by taking the *n* least significant
   bits of *x*).

   If *n* is more than 64, then the value *x* is sign-extended to *n* bits.

.. c:function:: term_t yices_bvconst_mpz(uint32_t n, const mpz_t x)

   Converts GMP integer *x* into a bitvector constant.

   **Parameters**

   - *n* is the number of bits.

   - *x* is the value.

   The number *n* must be positive and no more than :c:macro:`YICES_MAX_BVSIZE`.

   The GMP integer *x* is interpreted as a signed number in 2's complement.

   - If *x* has fewer than *n* bits, then the value is sign-extended.

   - If *x* has more than *n* bits, then the result is formed by taking the
     *n* least significant bits of *x*.

   This function is not declared unless you include :file:`gmp.h` before
   :file:`yices.h` in your code. See :c:func:`yices_mpz`.

.. c:function:: term_t yices_bvconst_zero(uint32_t n)

   Constructs the zero bitvector of *n* bits.

   All bits of the results are set to 0.

   **Parameter**

   - *n* is the number of bits.

     It must be positive and no more than :c:macro:`YICES_MAX_BVSIZE`

.. c:function:: term_t yices_bvconst_one(uint32_t n)

   Constructs the bitvector constant 1.

   The least significant bit of the result is 1 and all other bits
   are 0.

   **Parameter**

   - *n* is the number of bits.

     It must be positive and no more than :c:macro:`YICES_MAX_BVSIZE`

.. c:function:: term_t yices_bvconst_minus_one(uint32_t n)

   Constructs the bitvector constant equal to -1 in 2's complement representation.

   All the bits in the result are set to 1.

   **Parameter**

   - *n* is the number of bits.

     It must be positive and no more than :c:macro:`YICES_MAX_BVSIZE`


.. c:function:: term_t yices_bvconst_from_array(uint32_t n, const int32_t a[])

   Constructs a bitvector constant from an array of integers.

   **Parameters**

   - *n* is the number of bits

   - *a* must be an array of *n* integers

   Parameter *n* must be positive and no more than :c:macro:`YICES_MAX_BVSIZE`.

   The bits are indexed from 0 (least significant bit) to *n-1* (most significant bit),
   and the result is defined as follows:

   - bit *i* of the result is 0 if *a[i]* is 0.

   - bit *i* of the result is 1 if *a[i]* is not 0.

.. c:function:: term_t yices_parse_bvbin(const char *s)

   Constructs a bitvector constant from a string in binary format.

   **Parameter**

   - *s* must be a ``'\0'``-terminated string that contains only
     the characters ``'0'`` and ``'1'``.

   The first character of *s* is the most-significant bit in the result,
   and the last character is the least-significant bit.

   The size of the result (number of bits) is the same as the length of string *s*.

   For example, ``yices_parse_bvbin("00001")`` returns the same term as
   ``yices_bvconst_one(5)``.

   **Error report**

   - If *s* is empty or contains characters other than ``'0'`` or ``'1'``:

     -- error code: :c:enum:`INVALID_BVBIN_FORMAT`

   - If *s* is too long (more than :c:macro:`YICES_MAX_BVSIZE` characters):

     -- error code: :c:enum:`MAX_BVSIZE_EXCEEDED`

     -- badval := length of *s*

.. c:function:: term_t yices_parse_bvhex(const char *s)

   Constructs a bitvector constant from a string in hexadecimal format.

   **Parameter**

   - *s* must be a ``'\0'``-terminated string that contains only
     the characters ``'0'`` to ``'9'`` or ``'a'`` to ``'f'`` or ``'A'`` to ``'F'``.

   If *s* is a string of length *n*, then the result is a bitvector
   of *4\*n* bits.

   The first character of *s* defines the four most significant bits
   of the result, and the last character gives the four least
   significant bits.

   For example, ``yices_parse_bvhex("A7")`` returns the same term
   as ``yices_parse_bvbin("10100111")``.

   **Error report**

   - If *s* is empty or contains non-hexadecimal characters:

     -- error code: :c:enum:`INVALID_BVHEX_FORMAT`

   - If *s* is too long (more than :c:macro:`YICES_MAX_BVSIZE`/4 characters):

     -- error code: :c:enum:`MAX_BVSIZE_EXCEEDED`

     -- badval := 4 * (length of *s*)


.. c:function:: term_t yices_bvadd(term_t t1, term_t t2)

   Returns the bitvector sum *(bv-add t1 t2)*.

   **Parameters**

   - *t1* and *t2* must be bitvector terms of the same type.

.. c:function:: term_t yices_bvsub(term_t t1, term_t t2)

   Returns the bitvector difference *(bv-sub t1 t2)*.

   **Parameters**

   - *t1* and *t2* must be bitvector terms of the same type.

.. c:function:: term_t yices_bvneg(term_t t1)

   Returns the 2's complement opposite of *t1*.

.. c:function:: term_t yices_bvmul(term_t t1, term_t t2)

   Returns the bitvector product *(bv-mul t1 t2)*.

   **Parameters**

   - *t1* and *t2* must be bitvector terms of the same type.

   **Error report**

   - If (degree of *t1* + degree of *t2*) is more than :c:macro:`YICES_MAX_DEGREE`

     -- error code := :c:enum:`DEGREE_OVERFLOW`

     -- badval := degree of *t1* + degree of *t2*  

.. c:function:: term_t yices_bvsquare(term_t t1)

   Returns the product  *(bv-mul t1 t1)*.

   **Error report**

   - If (2 |times| degree of *t1*) is more than :c:macro:`YICES_MAX_DEGREE`

     -- error code := :c:enum:`DEGREE_OVERFLOW`

     -- badval := twice the degree of *t1*

.. c:function:: term_t yices_bvpower(term_t t1, uint32_t d)

   Bitvector exponentiation: raises *t1* to power *d*.

   If *d* is 0, the result is *0b0...01*, even if *t1* is the zero constant.

   **Error report**

   - If (*d* |times| degree of *t1*) is more than :c:macro:`YICES_MAX_DEGREE`

     -- error code := :c:enum:`DEGREE_OVERFLOW`

     -- badval := (*d* |times| degree of *t1*)
   

.. c:function:: term_t yices_bvsum(uint32_t n, const term_t t[])

   Returns the bitvector sum *(bv-add t[0] ... t[n-1])*.

   This function generalizes :c:func:`yices_bvadd` to an arbitrary
   number of arguments.

   **Parameters**

   - *n* is the number of arguments. It must be positive.

   - *t* must be an array of *n* bitvector terms. All the elements of *t* must
     have the same type (i.e., the same number of bits).

   If *n=1*, this function returns *t[0]*, otherwise, it builds a sum.


.. c:function:: term_t yices_bvproduct(uint32_t n, const term_t t[])

   Returns the bitvector product *(bv-mul t[0] ... t[n-1])*.

   This function generalizes :c:func:`yices_bvmul` to an arbitrary number 
   of arguments.

   **Parameters**

   - *n* is the number of arguments. It must be positive.

   - *t* must be an array of *n* bitvector terms. All the elements of *t* must
     have the same type (i.e., the same number of bits).

   If *n=1*, this function returns *t[0]*, otherwise, it builds a product.

   **Error report**

   - If the degree is too large:

     -- error code: :c:enum:`DEGREE_OVERFLOW`

     -- badval := degree


.. c:function:: term_t yices_bvdiv(term_t t1, term_t t2)

   Quotient in the unsigned bitvector division.

   **Parameters**

   - *t1* and *t2* must be bitvector terms of the same type.

   The two vectors are interpreted as unsigned integers (represented
   with *n* bits) and the results is the largest integer that 
   can be represented with *n* bits, and is less than or equal to *t1/t2*.

   For division by zero, Yices uses the following convention:

   .. code-block:: none

        (bv-div t1 0b00...0) = 0b11...1

      
.. c:function:: term_t yices_bvrem(term_t t1, term_t t2)

   Remainder in the unsigned division.

   **Parameters**

   - *t1* and *t2* must be bitvector terms of the same type.

   The remainder satisfies the following equality:

   .. code-block:: none

        (bv-rem t1 t2) = (bv-sub t1 (bv-mul (bv-div t1 t2) t2))

   If *t2* is zero, this gives:

   .. code-block:: none

        (bv-rem t1 0b00...0) = t1

.. c:function:: term_t yices_bvsdiv(term_t t1, term_t t2)

   Quotient in the signed bitvector division.

   **Parameters**

   - *t1* and *t2* must be bitvector terms of the same type.

   The two bitvectors *t1* and *t2* are interpreted as signed integers
   of *n* bits in 2's complement representation. This signed division
   rounds the quotient toward zero.

   - If *t1/t2* is positive and *t2* isn't zero, then *(bv-sdiv t1
     t2)* is positive. It is the largest integer that can be
     represented using *n* bits and is less than or equal to *t1/t2*.

   - If *t1/t2* is negative and *t2* isn't zero, then (*bv-sdiv t1
     t2)* is negative. It is the smallest integer that can be
     represented using *n* bits and is more than or equal to *t1/t2*.

   When *t2* is zero, Yices uses the following convention:

   - If *t1* is negative then

     .. code-block:: none 
 
           (bv-sdiv t1 0b00...00) = 0b00...01

   - If *t1* is positive or zero

     .. code-block:: none 

          (bv-sdiv t1 0b00...00) = 0b11...11


.. c:function:: term_t yices_bvsrem(term_t t1, term_t t2)

   Remainder in the signed division.

   **Parameters**

   - *t1* and *t2* must be bitvector terms of the same type.

   The remainder satisfies the following equality:

   .. code-block:: none

        (bv-srem t1 t2) = (bv-sub t1 (bv-mul (bv-sdiv t1 t2) t2))

   If *t2* is zero, this gives:

   .. code-block:: none

        (bv-srem t1 0b00...0) = t1


.. c:function:: term_t yices_bvsmod(term_t t1, term_t t2)

   Remainder in the *floor* division.

   **Parameters**

   - *t1* and *t2* must be bitvector terms of the same type.

   The two bitvectors *t1* and *t2* are interpreted as signed integers
   of *n* bits in 2's complement representation.  This function returns
   the remainder in the signed division of *t1* by *t2* with rounding
   to minus infinity.

   If *t2* is non-zero, the quotient *q* in this division is the
   largest signed integer that can be represented with *n* bits and is
   less than or equal to *t1/t2*.

   Then *(bv-smod t1 t2)* is defined by

   .. code-block:: none

        (bv-smod t1 t2) = (bv-sub t1 (bv-mul q t2))

   If *t2* is zero, this gives

   .. code-block:: none

        (bv-srem t1 0b00...0) = t1


.. c:function:: term_t yices_bvnot(term_t t1)

   Returns the bitwise negation of *t1*.

.. c:function:: term_t yices_bvand(uint32_t n, const term_t t[])

   Returns the bitwise and *(bv-and t[0] ... t[n-1])*.

   **Parameters**

   - *n* is the number of arguments. It must be positive.

   - *t* must be an array of *n* bitvector terms. All the elements of *t* must
     have the same type (i.e., the same number of bits).

.. c:function:: term_t yices_bvand2(term_t t1, term_t t2)

   Returns the bitwise and *(bv-and t1 t2)*.

   **Parameters**

   - *t1* and *t2* must be bitvector terms of the same type.

   This function is equivalent to :c:func:`yices_bvand` with *n=2*.

.. c:function:: term_t yices_bvand3(term_t t1, term_t t2, term_t t3)

   Returns the bitwise and *(bv-and t1 t2 t3)*.

   **Parameters**

   - *t1*, *t2*, and *t3* must be bitvector terms of the same type.

   This function is equivalent to :c:func:`yices_bvand` with *n=3*.

.. c:function:: term_t yices_bvor(uint32_t n, const term_t t[])

   Returns the bitwise or *(bv-or t[0] ... t[n-1])*.

   **Parameters**

   - *n* is the number of arguments. It must be positive.

   - *t* must be an array of *n* bitvector terms. All the elements of *t* must
     have the same type (i.e., the same number of bits).

.. c:function:: term_t yices_bvor2(term_t t1, term_t t2)

   Returns the bitwise or *(bv-or t1 t2)*.

   **Parameters**

   - *t1* and *t2* must be bitvector terms of the same type.

   This function is equivalent to :c:func:`yices_bvor` with *n=2*.

.. c:function:: term_t yices_bvor3(term_t t1, term_t t2, term_t t3)

   Returns the bitwise or *(bv-or t1 t2 t3)*.

   **Parameters**

   - *t1*, *t2*, and *t3* must be bitvector terms of the same type.

   This function is equivalent to :c:func:`yices_bvor` with *n=3*.

.. c:function:: term_t yices_bvxor(uint32_t n, const term_t t[])

   Returns the bitwise exclusive or *(bv-xor t[0] ... t[n-1])*.

   **Parameters**

   - *n* is the number of arguments. It must be positive.

   - *t* must be an array of *n* bitvector terms. All the elements of *t* must
     have the same type (i.e., the same number of bits).

.. c:function:: term_t yices_bvxor2(term_t t1, term_t t2)

   Returns the bitwise exclusive or *(bv-xor t1 t2)*.

   **Parameters**

   - *t1* and *t2* must be bitvector terms of the same type.

   This function is equivalent to :c:func:`yices_bvxor` with *n=2*.

.. c:function:: term_t yices_bvxor3(term_t t1, term_t t2, term_t t3)

   Returns the bitwise exclusive or *(bv-xor t1 t2 t3)*.

   **Parameters**

   - *t1*, *t2*, and *t3* must be bitvector terms of the same type.

   This function is equivalent to :c:func:`yices_bvxor` with *n=3*.


.. c:function:: term_t yices_bvnand(term_t t1, term_t t2)   

   Returns the bitwise *NAND* of *t1* and *t2*.

   **Parameters**

   - *t1* and *t2* must be bitvector terms of the same type.
 
   The result is the bitwise negation of *(bv-and t1 t2)*.

.. c:function:: term_t yices_bvnor(term_t t1, term_t t2)

   Returns the bitwise *NOR* of *t1* and *t2*.

   **Parameters**

   - *t1* and *t2* must be bitvector terms of the same type.
 
   The result is the bitwise negation of *(bv-or t1 t2)*.

.. c:function:: term_t yices_bvxnor(term_t t1, term_t t2)

   Returns the bitwise *XNOR* of *t1* and *t2*.

   **Parameters**

   - *t1* and *t2* must be bitvector terms of the same type.
 
   The result is the bitwise negation of *(bv-xor t1 t2)*.


.. c:function:: term_t yices_shift_left0(term_t t, uint32_t n)

   Bitvector shift left by a constant, padding with 0.

   This shifts bitvector *t* by *n* bits to the left, and sets the
   least significant bits to 0. 

   **Parameters**

   - If *t* is a bitvector of *m* bits then parameter *n* must
     be between 0 and *m*.

   **Examples**

        ========= ===== =========
           *t*     *n*    result
        ========= ===== =========
         0b11111    0    0b11111
         0b11111    2    0b11100
         0b11111    5    0b00000
        ========= ===== =========

   **Error report**

   - If *n* is more than the number of bits in *t*:

     -- error code: :c:enum:`INVALID_BITSHIFT`

     -- badval := *n*   

.. c:function:: term_t yices_shift_left1(term_t t, uint32_t n)

   Bitvector shift left by a constant, padding with 1.

   This shifts bitvector *t* by *n* bits to the left, and sets the
   least significant bits to 1. 

   **Parameters**

   - If *t* is a bitvector of *m* bits then parameter *n* must
     be between 0 and *m*.

   **Examples**

        ========= ===== =========
           *t*     *n*    result
        ========= ===== =========
         0b00000    0    0b00000
         0b00000    2    0b00011
         0b00000    5    0111111
        ========= ===== =========

   **Error report**

   - If *n* is more than the number of bits in *t*:

     -- error code: :c:enum:`INVALID_BITSHIFT`

     -- badval := *n*   

.. c:function:: term_t yices_shift_right0(term_t t, uint32_t n)

   Bitvector shift right by a constant, padding with 0.

   This shifts bitvector *t* by *n* bits to the right, and sets the
   most significant bits to 0. 

   **Parameters**

   - If *t* is a bitvector of *m* bits then parameter *n* must
     be between 0 and *m*.

   **Examples**

        ========= ===== =========
           *t*     *n*    result
        ========= ===== =========
         0b11111    0    0b11111
         0b11111    2    0b00111
         0b11111    5    0b00000
        ========= ===== =========

   **Error report**

   - If *n* is more than the number of bits in *t*:

     -- error code: :c:enum:`INVALID_BITSHIFT`

     -- badval := *n*   

.. c:function:: term_t yices_shift_right1(term_t t, uint32_t n)

   Bitvector shift right by a constant, padding with 1.

   This shifts bitvector *t* by *n* bits to the right, and sets the
   most significant bits to 1. 

   **Parameters**

   - If *t* is a bitvector of *m* bits then parameter *n* must
     be between 0 and *m*.

   **Examples**

        ========= ===== =========
           *t*     *n*   result
        ========= ===== =========
         0b00000    0    0b00000
         0b00000    2    0b11000
         0b00000    5    0111111
        ========= ===== =========

   **Error report**

   - If *n* is more than the number of bits in *t*:

     -- error code: :c:enum:`INVALID_BITSHIFT`

     -- badval := *n*   

.. c:function:: term_t yices_ashift_right(term_t t, uint32_t n)

   Bitvector arithmetic shift right by a constant.

   This shifts bitvector *t* by *n* bits to the right, and
   sets the most significant bits of the result to the same
   value as *t*'s sign bit (i.e., the most significant bit of *t*).

   **Parameters**

   - If *t* is a bitvector of *m* bits then parameter *n* must
     be between 0 and *m*.

   **Examples**

        ========= ===== =========
           *t*     *n*   result
        ========= ===== =========
         0b01111    2    0b00011
         0b01111    5    0b00000
         0b10111    2    0b11101
         0b10111    5    0b11111
        ========= ===== =========

   **Error report**

   - If *n* is more than the number of bits in *t*:

     -- error code: :c:enum:`INVALID_BITSHIFT`

     -- badval := *n*   


.. c:function:: term_t yices_rotate_left(term_t t, uint32_t n)

   Bitvector rotate left by a constant.

   This rotates bitvector *t* to the left by *n* bits.

   **Parameters**

   - If *t* is a bitvector of *m* bits then parameter *n* must
     be between 0 and *m*.

   **Examples**

   If *n* is either 0 or *m*, the result is equal to *t*.

        ========= ===== =========
           *t*     *n*   result
        ========= ===== =========
         0b01010    0    0b01010
         0b01010    1    0b10100
         0b01010    2    0b01001
        ========= ===== =========

   **Error report**

   - If *n* is more than the number of bits in *t*:

     -- error code: :c:enum:`INVALID_BITSHIFT`

     -- badval := *n*   


.. c:function:: term_t yices_rotate_right(term_t t, uint32_t n)

   Bitvector rotate right by a constant.

   This rotates bitvector *t* to the right by *n* bits.

   **Parameters**

   - If *t* is a bitvector of *m* bits then parameter *n* must
     be between 0 and *m*.

   If *n* is either 0 or *m*, the result is equal to *t*.

   **Examples**

        ========= ===== =========
           *t*     *n*   result
        ========= ===== =========
         0b01010    0    0b01010
         0b01010    1    0b00101
         0b01010    2    0b10010
        ========= ===== =========

   **Error report**

   - If *n* is more than the number of bits in *t*:

     -- error code: :c:enum:`INVALID_BITSHIFT`

     -- badval := *n*   



.. c:function:: term_t yices_bvshl(term_t t1, term_t t2)

   Bitvector shift left.

   This shifts bitvector *t1* to the left by the amount specified by *t2*.
   The least significant bits of the result are set to 0.

   **Parameters**

   - *t1* and *t2* must be two bitvectors of the same type

   If *n* is the number of bits in both *t1* and *t2*, then bitvector
   *t2* is interpreted as an unsigned integer of *n* bits that specifies
   the shift amount. If *t2*'s value is more than *n-1*, then
   the result is the bitvector ``0b00...00``.


.. c:function:: term_t yices_bvlshr(term_t t1, term_t t2)

   Bitvector logical shift right.

   This shifts bitvector *t1* to the right by the amount specified by *t2*.
   The most significant bits of the result are set to 0.

   **Parameters**

   - *t1* and *t2* must be two bitvectors of the same type

   If *n* is the number of bits in both *t1* and *t2*, then bitvector
   *t2* is interpreted as an unsigned integer of *n* bits that specifies
   the shift amount. If *t2*'s value is more than *n-1*, then
   the result is the bitvector ``0b00...00``.


.. c:function:: term_t yices_bvashr(term_t t1, term_t t2)

   Bitvector arithmetic shift right.

   This shifts bitvector *t1* to the right by the amount specified by *t2*.
   The most significant bits of the result are equal to *t1*'s sign bit (i.e.,
   the most significant bit of *t1*).

   **Parameters**

   - *t1* and *t2* must be two bitvectors of the same type

   If *n* is the number of bits in both *t1* and *t2*, then bitvector
   *t2* is interpreted as an unsigned integer of *n* bits that specifies
   the shift amount. If *t2*'s value is more than *n-1*, then
   the result is either the bitvector ``0b11...11`` if *t1* is negative,
   or the bitvector ``0b00...00`` if *t1* is positive or null.

.. c:function:: term_t yices_bvextract(term_t t, uint32_t i, uint32_t j)

   Extracts a subvector from bitvector *t*.

   **Parameters**

   - *t* must be a bitvector term

   - *i* and *j* must satisfy the constraint *i* |<=| *j* |<=| *n-1* where *n*
     is the number of bits in *t*

   The result is a bitvector of *1 + j - i* bits, formed by taking bits *i* to *j*
   of *t*. The least significant bit of the result is the *i*-th bit of *t*, and the
   most significant bit is the *j*-th bit of *t*.

   **Examples**
 
      ========= ===== ===== =========
        *t*      *i*   *j*   result
      ========= ===== ===== =========
       0b10010    0     2    0b010
       0b10010    2     4    0b100
       0b10010    1     4    0b1001
      ========= ===== ===== =========

   **Error report**

   - If the constraint *i* |<=| *j* |<=| *n-1* does not hold
  
     -- error code: :c:enum:`INVALID_BVEXTRACT`


.. c:function:: term_t yices_bitextract(term_t t, uint32_t i)

   Extracts the *i*-th bit of bitvector *t*.

   **Parameters**

   - *i* must be an index between 0 and *n-1*, where *n* is the number
     of bits of *t*.

   The result is a Boolean term.

   **Error report**

   - If *i* is too large:

     -- error code: :c:enum:`INVALID_BITEXTRACT`


.. c:function:: term_t yices_bvconcat(uint32_t n, const term_t t[])

   Bitvector concatenation: *(bv-concat t[0] ... t[n-1])*

   **Parameters**

   - *n* is the number of arguments

   - *t* must be an array of *n* bitvector terms

   Parameter *n* must be positive.

   The array *t* lists the elements to concatenate from left to right:
   the most significant bits of the result are given by *t[0]* and the
   least significant bits are formed by *t[n-1]*.  For example, if we
   have *n=3* and *t[0] = 0b000*, *t[1] = 0b111*, and *t[2] = 0b01*,
   then the result is *0b00011101*.
 
   **Error report**

   - If the size of the result would be more than :c:macro:`YICES_MAX_BVSIZE`

     -- error code: :c:enum:`MAX_BVSIZE_EXCEEDED`

     -- badval := sum of the sizes of the vectors *t[i]*

.. c:function:: term_t yices_bvconcat2(term_t t1, term_t t2)

   Concatenation of *t1* and *t2*.

   This function is equivalent to :c:func:`yices_bvconcat` with *n=2*.

   The left part (most significant bits) is *t1* and the right part
   (least significant bits) is *t2*.

.. c:function:: term_t yices_bvrepeat(term_t t, uint32_t n)

   Repeated concatenation.

   This concatenates *t* with itself *n* times.

   The result is a bitvector of *n\*m* bits, where *m* is the number of bits in *t*.
   If *n=1* the result is ``t``; if *n=2*, it is the same as ``yices_bvconcat2(t, t)``,
   and so forth.

   **Parameters**

   - The integer *n* must be positive

   **Error report** 

   - If *n* * (number of bits of *t*) is more than :c:macro:`YICES_MAX_BVSIZE`

     -- error code: :c:enum:`MAX_BVSIZE_EXCEEDED`

     -- badval := *n* * (number of bits of *t*)

.. c:function:: term_t yices_sign_extend(term_t t, uint32_t n)

   Sign extension.

   This adds *n* copies of *t*'s sign bit to the left of *t*.

   **Error report**

   - If *n* + (number of bits of *t*) is more than :c:macro:`YICES_MAX_BVSIZE`

     -- error code: :c:enum:`MAX_BVSIZE_EXCEEDED`

     -- badval := *n* + (number of bits of *t*)


.. c:function:: term_t yices_zero_extend(term_t t, uint32_t n)

   Zero extension.

   This adds *n* zero bits to the left of *t*.

   **Error report**

   - If *n* + (number of bits of *t*) is more than :c:macro:`YICES_MAX_BVSIZE`

     -- error code: :c:enum:`MAX_BVSIZE_EXCEEDED`

     -- badval := *n* + (number of bits of *t*)


.. c:function:: term_t yices_redand(term_t t)

   And reduction.

   This returns a bitvector of one bit equal to the conjunction of all
   bits of *t*.

   If we denote by *b[n-1] ... b[0]* the *n* bits of *b*, then bit 0
   of the result is *(and b[0] ... b[n-1])*.

.. c:function:: term_t yices_redor(term_t t)

   Or reduction.

   This returns a bitvector of one bit equal to the disjunction of all
   bits of *t*.

   If we denote by *b[n-1] ... b[0]* the *n* bits of *b*, then bit 0
   of the result is *(or b[0] ... b[n-1])*.

.. c:function:: term_t yices_redcomp(term_t t1, term_t t2)

   Bitwise equality reduction.

   This function returns *(bv-redand (bv-xnor t1 t2))*. 

   The result is a bitvector of one bit equal to 1 if *t1* and *t2* are equal,
   and to 0 otherwise.

   **Parameters**

   - *t1* and *t2* must be two bitvectors of the same size.

.. c:function:: term_t yices_bvarray(uint32_t n, const term_t arg[])

   Converts an array of Boolean terms into a bitvector.

   **Parameters**

   - *n* is the number of bits in the result

   - *arg* must be an array of *n* Boolean terms

   Parameter *n* must be positive and no more than
   :c:macro:`YICES_MAX_BVSIZE`. The least significant bit is *arg[0]*
   and the most significant bit is *arg[n-1]*.

   **Error report**

   - If *n* is too large:

     -- error code: :c:enum:`MAX_BVSIZE_EXCEEDED`

     -- badval := *n*

.. c:function:: term_t yices_bveq_atom(term_t t1, term_t t2)

   Bivector equality.

   This returns the Boolean term *(= t1 t2)*.

   **Parameters**
 
   - *t1* and *t2* must be bitvector of the same type

.. c:function:: term_t yices_bvneq_atom(term_t t1, term_t t2)

   Bivector disequality.

   This returns the Boolean term *(/= t1 t2)*.

   **Parameters**
 
   - *t1* and *t2* must be bitvector of the same type

.. c:function:: term_t yices_bvge_atom(term_t t1, term_t t2)

   Bitvector unsigned inequality: *t1* greater than or equal to *t2*.

   **Parameters**
 
   - *t1* and *t2* must be bitvector of the same type

   Both bitvectors are interpreted as unsigned integers of *n* bits
   and the result is the atom *(>= t1 t2)*.

.. c:function:: term_t yices_bvgt_atom(term_t t1, term_t t2)

   Bitvector unsigned inequality: *t1* greater than *t2*.

   **Parameters**
 
   - *t1* and *t2* must be bitvector of the same type

   Both bitvectors are interpreted as unsigned integers of *n* bits
   and the result is the atom *(> t1 t2)*.

.. c:function:: term_t yices_bvle_atom(term_t t1, term_t t2)

   Bitvector unsigned inequality: *t1* less than or equal to *t2*.

   **Parameters**
 
   - *t1* and *t2* must be bitvector of the same type

   Both bitvectors are interpreted as unsigned integers of *n* bits
   and the result is the atom *(<= t1 t2)*.

.. c:function:: term_t yices_bvlt_atom(term_t t1, term_t t2)

   Bitvector unsigned inequality: *t1* less than *t2*.

   **Parameters**
 
   - *t1* and *t2* must be bitvector of the same type

   Both bitvectors are interpreted as unsigned integers of *n* bits
   and the result is the atom *(< t1 t2)*.

.. c:function:: term_t yices_bvsge_atom(term_t t1, term_t t2)

   Bitvector signed inequality: *t1* greater than or equal to *t2*.

   **Parameters**
 
   - *t1* and *t2* must be bitvector of the same type

   Both bitvectors are interpreted as signed integers of *n* bits in
   2's complement representation and the result is the atom *(>= t1 t2)*.

.. c:function:: term_t yices_bvsgt_atom(term_t t1, term_t t2)

   Bitvector signed inequality: *t1* greater than *t2*.

   **Parameters**
 
   - *t1* and *t2* must be bitvector of the same type

   Both bitvectors are interpreted as signed integers of *n* bits in
   2's complement representation and the result is the atom *(> t1 t2)*.

.. c:function:: term_t yices_bvsle_atom(term_t t1, term_t t2)

   Bitvector signed inequality: *t1* less than or equal to *t2*.

   **Parameters**
 
   - *t1* and *t2* must be bitvector of the same type

   Both bitvectors are interpreted as signed integers of *n* bits in
   2's complement representation and the result is the atom *(<= t1 t2)*.

.. c:function:: term_t yices_bvslt_atom(term_t t1, term_t t2)

   Bitvector signed inequality: *t1* less than *t2*.

   **Parameters**
 
   - *t1* and *t2* must be bitvector of the same type

   Both bitvectors are interpreted as signed integers of *n* bits in
   2's complement representation and the result is the atom *(< t1 t2)*.



Term Properties
---------------

.. c:function:: type_t yices_type_of_term(term_t t)

   Returns the type of term *t*.

   This function returns :c:macro:`NULL_TYPE` if *t* is not a valid term.

.. c:function:: int32_t yices_term_is_bool(term_t t)

   Checks whether *t* is a Boolean term.

   This function returns 1 for true and 0 for false. It also returns 0
   if *t* is not a valid term and sets the error report.

.. c:function:: int32_t yices_term_is_int(term_t t)

   Checks whether *t* has type integer.

   This function returns 1 for true and 0 for false. It also returns 0
   if *t* is not a valid term and sets the error report.

.. c:function:: int32_t yices_term_is_real(term_t t)

   Checks whether *t* has type real.

   This function returns 1 for true and 0 for false. It also returns 0
   if *t* is not a valid term and sets the error report.

   This function checks the actual type of *t* and does not take
   subtyping into account. It returns false if *t* has integer type.

.. c:function:: int32_t yices_term_is_arithmetic(term_t t)

   Checks whether *t* is an arithmetic term.

   This function returns 1 (for true) if *t* has either integer or real type.
   It returns 0 otherwise. If *t* is not a valid term, the function returns 
   0 and sets the error report.

.. c:function:: int32_t yices_term_is_bitvector(term_t t)

   Checks whether *t* has a bitvector type.

   This function returns 1 for true and 0 for false. It also returns 0
   if *t* is not a valid term and sets the error report.

.. c:function:: int32_t yices_term_is_scalar(term_t t)

   Checks whether *t* has a scalar or uninterpreted type.

   This function returns 1 for true and 0 for false. It also returns 0
   if *t* is not a valid term and sets the error report.

.. c:function:: int32_t yices_term_is_tuple(term_t t)

   Checks whether *t* has a tuple type.

   This function returns 1 for true and 0 for false. It also returns 0
   if *t* is not a valid term and sets the error report.

.. c:function:: int32_t yices_term_is_function(term_t t)

   Checks whether *t* has a function type.

   This function returns 1 for true and 0 for false. It also returns 0
   if *t* is not a valid term and sets the error report.

.. c:function:: uint32_t yices_term_bitsize(term_t t)

   Returns the number of bits of term *t*.

   This function returns 0 if there's an error, either because *t* is not
   valid or does not have bitvector type.

.. c:function:: int32_t  yices_term_is_ground(term_t t)

   Checks whether term *t* is ground.

   Returns 1 if *t* does not contain free variables, 0 otherwise.
   It also returns 0 if *t* is not a valid term and sets the error report.


.. _access_to_term_representation:

Access to Term Components
-------------------------

The internal term representation distinguishes between the following classes of terms:

1) **Atomic terms** include constants of Boolean, bitvector,
   arithmetic, scalar, and uninterpreted types, and variables and
   uninterpreted terms.

2) **Composite terms** are terms represented by an operator tag and a
   list of children.  For example an if-then-else term *(ite c t1 t2)*
   is composite. Its tag is the term-constructor
   :c:enum:`YICES_ITE_TERM` and its three children are the terms *c*,
   *t1*, and *t2*.

3) **Projections** represent tuple projection and extraction of a bit
   from a bitvector, which are constructed by functions
   :c:func:`yices_select` and :c:func:`yices_bitextract`,
   respectively. Internally, such terms consists of an integer index
   and a term (either a tuple or a bitvector term).

4) **Arithmetic sums** are used to build arithmetic polynomials.
   An arithmetic sum is of the form

   .. container:: centered

        *a*\ |_0| *t*\ |_0| + |...| + *a*\ |_n| *t*\ |_n|

   where the coefficients *a*\ |_0| |...| *a*\ |_n| are rational constants
   and the terms *t*\ |_0| |...| *t*\ |_n| are all arithmetic terms.

   Term *t*\ |_0| may be equal to :c:macro:`NULL_TERM`. In such a case,
   the product *a*\ |_0| *t*\ |_0| is replaced by the constant *a*\ |_0|,
   and the sum is

   .. container:: centered

        *a*\ |_0| + *a*\ |_1| *t*\ |_1| + |...| + *a*\ |_n| *t*\ |_n|.


5) **Bitvector sums** are used to build bitvector polynomials.  A
   bitvector sum is similar to an arithmetic sum but the coefficients
   are bitvector constants. It is of the form

   .. container:: centered

        *a*\ |_0| *t*\ |_0| + |...| + *a*\ |_n| *t*\ |_n|

   where the coefficients *a*\ |_0| |...| *a*\ |_n| are bitvector constants and
   the terms *t*\ |_0| |...| *t*\ |_n| are bitvector terms. All the coefficients
   and terms have the same number of bits.

   As previously, *t*\ |_0| may be equal to :c:macro:`NULL_TERM` to encode
   the sum:

   .. container:: centered

        *a*\ |_0| + *a*\ |_1| *t*\ |_1| + |...| + *a*\ |_n| *t*\ |_n|.


6) **Products** are also used to build arithmetic and bitvector polynomials.
   A product is of the form

   .. container:: centered

        *t*\ |_0|\ ^\ *d*\ |_0| |times| |...| |times| *t*\ |_n|\ ^\ *d*\ |_n|

   where the exponents *d*\ |_0| |...| *d*\ |_n| are positive
   integers, and the terms *t*\ |_0| |...| *t*\ |_n| are either all arithmetic
   terms or all bitvector terms of the same type.

The number of terms in a sum or product is always positive, but it may be
equal to one. For example, the expression (|-| *u*) is represented internally
as an arithmetic sum with a single monomial ( -1 ) |times| *u*.

Every term has a label of type :c:type:`term_constructor_t` that
identifies the class of the term and its constructor. Section :ref:`types_for_terms`
lists all the constructors and explains their roles.


Atomic Terms
............

Atomic terms are labeled with the following constructors.

    ==================================== ===========================
     Constructor                          Term
    ==================================== ===========================
     :c:enum:`YICES_BOOL_CONSTANT`        Boolean constant
     :c:enum:`YICES_ARITH_CONSTANT`       Arithmetic constant
     :c:enum:`YICES_BV_CONSTANT`          Bitvector constant
     :c:enum:`YICES_SCALAR_CONSTANT`      Scalar/unint constant
     :c:enum:`YICES_VARIABLE`             Variable
     :c:enum:`YICES_UNINTERPRETED_TERM`   Uninterpreted term
    ==================================== ===========================


The API provides functions to obtain the value of a constant. For
arithmetic constant, the value is given as a GMP rational. For a
bitvector constant, the value is an array of 0/1 integers; the number
of bits in this array is given by :c:func:`yices_term_bitsize`.  The
value of a constant of scalar or uninterpreted type is an integer
index (cf. :c:func:`yices_constant`).


Structure of Composite Terms
............................

The following table lists the constructors of composite terms.

    ================================ ===========================
     Constructor                      Term
    ================================ ===========================
     :c:enum:`YICES_ITE_TERM`         (ite c t1 t2)
     :c:enum:`YICES_APP_TERM`         (apply f t1 ... tn)
     :c:enum:`YICES_UPDATE_TERM`      (update f t1 ... tn v)
     :c:enum:`YICES_TUPLE_TERM`       (tuple t1 ... tn)
     :c:enum:`YICES_EQ_TERM`          (eq t1 t2)
     :c:enum:`YICES_DISTINCT_TERM`    (distinct t1 ... tn)
     :c:enum:`YICES_FORALL_TERM`      (forall v1 ... vn t)
     :c:enum:`YICES_LAMBDA_TERM`      (lambda v1 ... vn t)
     :c:enum:`YICES_NOT_TERM`         (not t)
     :c:enum:`YICES_OR_TERM`          (or t1 ... tn)
     :c:enum:`YICES_XOR_TERM`         (xor t1 ... tn)
     :c:enum:`YICES_BV_ARRAY`         (bv-array t1 ... tn)
     :c:enum:`YICES_BV_DIV`           (bv-div t1 t2)
     :c:enum:`YICES_BV_REM`           (bv-rem t1 t2)
     :c:enum:`YICES_BV_SDIV`          (bv-sdiv t1 t2)
     :c:enum:`YICES_BV_SREM`          (bv-srem t1 t2)
     :c:enum:`YICES_BV_SMOD`          (bv-smod t1 t2)
     :c:enum:`YICES_BV_SHL`           (bv-shl t1 t2)
     :c:enum:`YICES_BV_LSHR`          (bv-lshr t1 t2)
     :c:enum:`YICES_BV_ASHR`          (bv-ashr t1 t2)
     :c:enum:`YICES_BV_GE_ATOM`       (bv-ge t1 t2)
     :c:enum:`YICES_BV_SGE_ATOM`      (bv-sge t1 t2)
     :c:enum:`YICES_ARITH_GE_ATOM`    (>= t1 t2)
     :c:enum:`YICES_ARITH_ROOT_ATOM`  see below
     :c:enum:`YICES_ABS`              (abs t)
     :c:enum:`YICES_CEIL`             (ceil t)
     :c:enum:`YICES_FLOOR`            (floor t)
     :c:enum:`YICES_RDIV`             (/ t1 t2)
     :c:enum:`YICES_IDIV`             (div t1 t2)
     :c:enum:`YICES_IMOD`             (mod t1 t2)
     :c:enum:`YICES_IS_INT_ATOM`      (is-int t)
     :c:enum:`YICES_DIVIDES_ATOM`     (divides t1 t2)
    ================================ ===========================

**Notes**

The children of a composite term are indexed starting from 0.  The
indexing corresponds to the left-to-right order in the above
table. For example an if-then-else term has three children indexed
from 0 to 2. The first child is the condition *c*, the next child
is the then part *t1*, and the last child is the else part *t2*.

The first child in a function application is the function, the other
children are the arguments. The first child of a function update is
the function, the next *n* children are the arguments, and the last child
is the new value *v*.
  
For *forall* and *lambda* terms, the first *n* children are the
variables and the last child is the body *t*.

In the construct *(bv-array t1 ... tn)*, the *n* children are
Boolean terms listed in little-endian form. The first child *t1* is
the least significant bit and the last child *tn* is the most
significant bit.

**Arithmetic Root Atoms**

Arithmetic root atoms are used internally by the MCSAT solver.
Such a term represents an atomic constraint of the form::

   x r (k-th root of p)

where *x* and *p* are both arithmetic terms, *r* denotes a relational
operator (e.g., |<=| or >), and *k* is an integer index.
The term *p* is always a polynomial. This term is treated like a composite
term of two children. The first child is *x* and the second child is *p*.


Projection Terms
................

There are two types of projection terms to represent projection of a tuple
and extraction of a bit from a bitvector.

    ================================ ===========================
     Constructor                      Term
    ================================ ===========================
     :c:enum:`YICES_SELECT_TERM`      (select t i)
     :c:enum:`YICES_BIT_TERM`         (bit i t)
    ================================ ===========================

For a term of the form *(select t i)*, the child *t* is a tuple and *i* is
an index. If the *t* has type (*tuple* |tau|\ |_1| |...| |tau|\ |_n|)
then the index is between 1 and *n*. See :c:func:`yices_select`.

For a term of the form *(bit i t)*, the child *t* is a bitvector and *i* is
an index. If *t* is a bitvector of *n* bits, then *i* is between 0 and *n-1*.
Index 0 refers to the least significant bit of *t* and index *n-1* refers to
the most significant bit. See :c:func:`yices_bitextract`.


Polynomials
...........

Sums and power products have the following constructors.

    ================================ ===========================
     Constructor                      Term
    ================================ ===========================
     :c:enum:`YICES_ARITH_SUM`        Arithmetic sum
     :c:enum:`YICES_BV_SUM`           Bitvector sum
     :c:enum:`YICES_POWER_PRODUCT`    Power product
    ================================ ===========================

Functions are available to extract the monomials of a sum (as pairs
(coefficient |times| term)) and the factors of a product (as pairs
(term, exponent)).

Functions
.........

The following functions give access to the class, constructors,
children, and other components of a term. As usual, these functions
set the error report to :c:enum:`INVALID_TERM` if the argument is not
a valid term.

.. c:function:: int32_t yices_term_is_atomic(term_t t)

   Checks whether a term is atomic.

   This function returns 1 for true and 0 for false.  If *t* is not a
   valid term, the function returns 0 and sets the error report.

.. c:function:: int32_t yices_term_is_composite(term_t t)

   Checks whether a term is composite.

   This function returns 1 for true and 0 for false.  If *t* is not a
   valid term, the function returns 0 and sets the error report.

.. c:function:: int32_t yices_term_is_projection(term_t t)

   Checks whether a term is a projection.

   This function returns 1 for true and 0 for false.  If *t* is not a
   valid term, the function returns 0 and sets the error report.

.. c:function:: int32_t yices_term_is_sum(term_t t)

   Checks whether a term is an arithmetic sum.

   This function returns 1 for true and 0 for false.  If *t* is not a
   valid term, the function returns 0 and sets the error report.

.. c:function:: int32_t yices_term_is_bvsum(term_t t)

   Checks whether a term is a bitvector sum.

   This function returns 1 for true and 0 for false.  If *t* is not a
   valid term, the function returns 0 and sets the error report.

.. c:function:: int32_t yices_term_is_product(term_t t)

   Checks whether a term is a product.

   This function returns 1 for true and 0 for false.  If *t* is not a
   valid term, the function returns 0 and sets the error report.

.. c:function:: term_constructor_t yices_term_constructor(term_t t)

   Constructor of a term.

   This function returns the constructor of term *t*. If *t* is not
   a valid term, it returns :c:enum:`YICES_CONSTRUCTOR_ERROR`.

.. c:function:: int32_t yices_term_num_children(term_t t)

   Number of children of a term.

   - if *t* is atomic, this function returns 0.

   - if *t* is composite, it returns the number of children.

   - if *t* is a projection, the function returns 1.

   - if *t* is a sum, the function returns the number of summands.

   - if *t* is a product, the function returns the number of factors in the product.

   - otherwise, *t* is not valid; the function returns -1.
   
.. c:function:: term_t yices_term_child(term_t t, int32_t i)

   Child of a composite term.

   The function returns the *i*-th child of composite term *t* or
   :c:macro:`NULL_TERM` if there's an error.

   **Parameters**

   - *t* must be a composite term

   - *i* must be an index between 0 and *n-1*, where *n* is the number of children of *t*

   **Error report**

   - if *t* is not a composite term or *i* is not a valid index for term *t*

     -- error code: :c:enum:`INVALID_TERM_OP`


.. c:function:: term_t yices_term_children(term_t t, term_vector_t *v)

   Collect the children of a composite term.

   Store the children of term *t* into vector *v*. The vector must be initialized
   first by calling function :c:func:`yices_init_term_vector`.

   If *t* is not valir of not a composite term, the function returns -1, sets
   the error report, and leaves *v* unchanged.

   Otherwise, the children of *t* are stored in *v* in the same order as given
   by :c:func:`yices_term_child`.

   - *v->size* is the number  of children of term *t*

   - *v->data[i]* is the *i*-th child of term *t*

   **Error report**

   - if *t* is not a composite term

     -- error code: :c:enum:`INVALID_TERM_OP`


.. c:function:: int32_t yices_proj_index(term_t t)

   Index of a projection term.

   Term *t* must either be a tuple select *(select u i)* or a bit extract *(bit i u)*.
   This function returns the index *i* or -1 if there's an error.

   **Error report**

   - if *t* is not a projection

     -- error code: :c:enum:`INVALID_TERM_OP`

.. c:function:: term_t yices_proj_arg(term_t t)

   Child of a projection term.

   Term *t* must either be a tuple select *(select u i)* or a bit extract *(bit i u)*.
   This function returns the child *u* or :c:macro:`NULL_TERM` if there's an error.

   **Error report**

   - if *t* is not a projection

     -- error code: :c:enum:`INVALID_TERM_OP`


.. c:function:: int32_t yices_bool_const_value(term_t t, int32_t *val)

   Value of a Boolean constant.

   This function returns -1 and leaves *\*val* unchanged if *t* is
   not a Boolean constant. Otherwise, it stores the value of *t* in
   variable *\*val* (0 means false and 1 means true), and returns 0.

   **Error report**

   - if *t* is not a Boolean constant

     -- error code: :c:enum:`INVALID_TERM_OP`

.. c:function:: int32_t yices_bv_const_value(term_t t, int32_t val[])

   Value of a bitvector constant.

   This function stores the value of *t* in array *val*. If *t* is a
   bitvector of *n* bits, then *val* must be large enough to store *n*
   integers. The *n* bits of *t* are stored in array *val*. Element
   *val[i]* is either 0 or 1. The least significant bit is stored in
   *val[0]* and the most significant bit is stored in *val[n-1]*.

   The function returns -1 and leaves *val* unchanged if there's an error.
   It returns 0 if *t* is a bitvector constant.

   **Error report**

   - if *t* is not a bitvector constant

     -- error code: :c:enum:`INVALID_TERM_OP`

.. c:function:: int32_t yices_scalar_const_value(term_t t, int32_t *val)

   Index of a constant of scalar or uninterpreted type. 

   Constants of scalar and uninterpreted types are identified by an
   integer index (cf. :c:func:`yices_constant`). This function stores the
   index of constant *t* in *\*val*.

   The function returns -1 if there's an error and leaves *\*val* unchanged. Otherwise, it returns 0.

   **Error report**

   - if *t*'s constructor is not :c:enum:`YICES_SCALAR_CONSTANT`

     -- error code: :c:enum:`INVALID_TERM_OP`

.. c:function:: int32_t yices_rational_const_value(term_t t, mpq_t q)

   Value of a rational constant.

   This function copies the value of rational constant *t* in the GMP
   rational *q*.  The GMP rational *q* must be initialized (check the
   `GMP <http://gmplib.org>`_ documentation).

   If *t* is not a rational constant, the function returns -1 and leaves *q* unchanged.
   Otherwise it returns 0.

   **Error report**

   - if *t*'s constructor is not :c:enum:`YICES_ARITH_CONSTANT`

     -- error code: :c:enum:`INVALID_TERM_OP`

   **Note**

   To make sure that this function is declared, you must include :file:`gmp.h` before
   :file:`yices.h` in your code (see :c:func:`yices_mpz`).


.. c:function:: int32_t yices_sum_component(term_t t, int32_t i, mpq_t coeff, term_t *term)

   Component of an arithmetic sum.

   An arithmetic sum *t* is of the form *a*\ |_0| *t*\ |_0| + |...| +
   *a*\ |_n| *t*\ |_n|.  This function copies the coefficient *a*\ |_i|
   in the GMP rational *coeff* and it copies *t*\ |_i| in variable
   *\*term*.

   As a special case, the returned *\*term* may be equal to
   :c:macro:`NULL_TERM`. This may happen for *i=0*. In such a case,
   the sum is of the form *a*\ |_0| + *a*\ |_1| *t*\ |_1| + |...| +
   *a*\ |_n| *t*\ |_n|.

   This function returns -1 if *t* is not an arithmetic sum or if the
   index *i* is too large. It returns 0 otherwise.

   **Error report**

   - if *t*'s constructor is not :c:enum:`YICES_ARITH_SUM` or if *i* is too large

     -- error code: :c:enum:`INVALID_TERM_OP`

   **Note**

   To make sure that this function is declared, you must include :file:`gmp.h` before
   :file:`yices.h` in your code (see :c:func:`yices_mpz`).

.. c:function:: int32_t yices_bvsum_component(term_t t, int32_t i, int32_t val[], term_t *term)

   Component of a bitvector sum.

   A bitvector sum *t* is of the form *a*\ |_0| *t*\ |_0| + |...| +
   *a*\ |_n| *t*\ |_n|. This function copies the coefficient *a*\ |_i|
   in array *val* and it copies *t*\ |_i| in *\*term*.

   If *t* is a bitvector term of *m* bits, then array *val* must be large enough
   to store *m* integers. The *m* bits of coefficients *a*\ |_i| are copied in
   *val[0]* |...| *val[m-1]*; *val[0]* is the least significant bit and *val[m-1]* is
   the most significant bit of *a*\ |_i|.

   As a special case, the returned *\*term* may be equal to
   :c:macro:`NULL_TERM`. This may happen for *i=0*. In such a case,
   the sum is of the form *a*\ |_0| + *a*\ |_1| *t*\ |_1| + |...| +
   *a*\ |_n| *t*\ |_n|.
   
   This function returns -1 if *t* is not an arithmetic sum or if the
   index *i* is too large. It returns 0 otherwise.
      
   **Error report**

   - if *t*'s constructor is not :c:enum:`YICES_BV_SUM` or if *i* is too large

     -- error code: :c:enum:`INVALID_TERM_OP`


.. c:function:: int32_t yices_product_component(term_t t, int32_t i, term_t *term, uint32_t *exp)

   Component of a power product.

   A product *t* is of the form  *t*\ |_0|\ ^\ *d*\ |_0| |times| |...| |times| *t*\ |_n|\ ^\ *d*\ |_n|.
   This function stores the term *t*\ |_i| into *\*term* and the exponent *d*\ |_i| into *\*exp*.

   The function returns -1 if *t* is not a product or if the index *i* is too large.
   It returns 0 otherwise.

   **Error report**

   - if *t*'s constructor is not :c:enum:`YICES_POWER_PRODUCT` or if *i* is too large

     -- error code: :c:enum:`INVALID_TERM_OP`

