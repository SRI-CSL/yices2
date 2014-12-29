:tocdepth: 2

.. highlight:: c

.. _term_operations:

Terms
=====

The API provides constructors for terms defined in the Yices language.
There are no special constructs for formulas; formulas are terms of
Boolean type.  The semantics and type-checking rules of the language
are explained in the `manual
<http://yices.csl.sri.com/papers/manual.pdf>`_.

All term constructors return an object of type :c:type:`term_t`. They
check their arguments, perform type checking, and return
:c:macro:`NULL_TERM` if there's error. The functions listed in Section
:ref:`error_reports` can then be used to diagnose the error or print
an error message. 

If there's no error, the constructors apply rewriting and simplication
procedures, then return an index in the global term table maintained
within Yices. This index uniquely identifies the resulting term.
Since Yices uses hash consing, two terms that are syntactically
identical (after rewriting and simplification) are represented by the
same index.

.. warning:: Some functions take an array of terms as argument. If this
             array is not declared as ``const term_t a[]`` then the
             function may modify the array.

**Generic error reports**

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

  - Some functions expect arguments of compatible types. If parameters
    *t1* and *t2* do not have compatible types the error report is:

    -- error code: :c:enum:`INCOMPATIBLE_TYPES`

    -- term1 := *t1*

    -- type1 := *t1* 's type

    -- term2 := *t2*

    -- type2 := *t2* 's type

  - If an integer parameter that must be positive is given the value zero:

    -- error code :c:enum:`POS_INT_REQUIRED`

    -- badval := 0

Other error reports may be produced by the term constructors.
They are indicated after the function signature.

The next four sections present generic constructors, then constructors
for Boolean, arithmetic, and bitvector terms. The last section
documents functions to extract term attributes and access the internal
term representation.



Generic Term Constructors
-------------------------

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

   - if *tau* is not scalar or uninterpreted

     -- error code: :c:enum:`SCALAR_OR_UTYPE_REQUIRED`

     -- type1 := *tau*

   - if *i* is negative or too large for type *tau*

     -- error code: :c:enum:`INVALID_CONSTANT_INDEX`

     -- type1 := *tau*

     -- badval := *i*

   This function creates constants of uninterpreted or scalar
   types. Within each such type, the constants are identified by a
   non-negative index *i*. Two constants with distinct indices are
   distinct terms. A scalar type *tau* has finite cardinality so the
   number of constants of type *tau* is limited. There is no
   restriction on the number of constants of type *tau* if *tau* is an
   uninterpreted type.

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

   - if *n* is more than :c:macro:`YICES_MAX_ARITY`:

     -- error code: :c:enum:`TOO_MANY_ARGUMENTS`

     -- badval: *n*

   **Warning**

   -  array *arg* may be modified.
    

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

   The parameter *n* must be equal to the arity of function *fun*, and the arguments *arg[0] ... arg[n-1]* 
   must have types that match the function signature. More precisely, if *fun* has type *(-> tau_1 ... tau_n sigma)*
   then *arg[i]*'s type must be a subtype of *tau_(i+1)*.

   **Error report**

   - if *fun* does not have function type

     -- error code: :c:enum:`FUNCTION_REQUIRED`
 
     -- term1 := *fun*

   - if *n* is different from *fun*'s arity

     -- error code: :c:enum:`WRONG_NUMBER_OF_ARGUMENTS`

     -- badval := *n*


.. c:function:: term_t yices_application1(term_t fun, term_t arg1)

   Returns the term *(fun arg1)*.

   This function applies a unary function *fun* to term *arg1*.

   It is equivalent to :c:func:`yices_application` with *n=1*.


.. c:function:: term_t yices_application2(term_t fun, term_t arg1, term_t arg2)

   Returns the term *(fun arg1 arg2)*.

   This function applies binary function *fun* to the *arg1* and *arg2*. 

   It is equivalent to :c:func:`yices_application` with *n=2*.


.. c:function:: term_t yices_application3(term_t fun, term_t arg1, term_t arg2, term_t arg3)

   Returns the term *(fun arg1 arg2 arg3)*.

   This function applies ternary function *fun* to *arg1*, *arg2*, and *arg3*. 

   It is equivalent to :c:func:`yices_application` with *n=3*.


.. c:function:: term_t yices_tuple(uint32_t n, const term_t arg[])

   Returns the tuple term *(tuple arg[0] ... arg[n-1])*

   **Parameters**

   - *n* is the number of components. It must be positive and no more than :c:macro:`YICES_MAX_ARITY`

   - *arg*: array of *n* terms

   **Error report**

   - if *n* is more than :c:macro:`YICES_MAX_ARITY`

     -- error code: :c:enum:`TOO_MANY_ARGUMENTS`

     -- badval := n


.. c:function:: term_t yices_pair(term_t t1, term_t t2)

   Returns the pair *(tuple t1 t2)*

   This function is equivalent to :c:func:`yices_tuple` with *n=2*.


.. c:function:: term_t yices_triple(term_t t1, term_t t2, term_t t3)

   Returns the triple *(tuple t1 t2 t3)*

   This function is equivalent to :c:func:`yices_tuple` with *n=3*.


.. c:function:: term_t yices_select(uint32_t i, term_t t)

   Returns the term *(select t i)*

   This function extracts the *i*-th component of a tuple *t*. 

   **Parameters**

   - *i* must be an index between 1 and N (where N is the number of components of *t*)

   - *t* must be a term of tuple type

   **Error report**

   - if *t* is does not have tuple type

     -- error code: :c:enum:`TUPLE_REQUIRED`

     -- term1 := *t*

   - if *i* is zero or larger than N:

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

   - if *t*'s type is *(tuple tau_1 .. tau_i .. tau_n)* then *v*'s type must be a subtype of *tau_i*

   **Error report**

   - if *t* does not have a tuple type

     -- error code: :c:enum:`TUPLE_REQUIRED`

     -- term1 := *t*

   - if *i* is zero or larger than N:

     -- error code: :c:enum:`INVALID_TUPLE_INDEX`

     -- type1 := type of *t*

     -- badval := *i*    

   - if *v*'s type is incorrect, the error code is :c:enum:`TYPE_MISMATCH`


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
   types that match the signature of *fun*. In addition, the new value *v* must
   have a type that's a subtype of the function range.

   **Error report**

   - if *fun* does not have function type

     -- error code: :c:enum:`FUNCTION_REQUIRED`

     -- term1 := *fun*

   - if *n* is different from *fun*'s arity

     -- error code: :c:enum:`WRONG_NUMBER_OF_ARGUMENTS`

     -- badval := *n*

   This constructor is often used to encode the operation of writing
   into an array.  Yices does not have special types for arrays and an
   array is the same as a function.  Under this interpretation, the
   function *fun* above is an array with *n* dimensions, and the update
   operation writes the value *v* at the index *(arg[0]
   ... arg[n-1])*.  The result is a new array.

   

.. c:function:: term_t yices_update1(term_t fun, term_t arg1, term_t v)

   Creates the function update *(update fun (arg1) v)*

   This constructor is equivalent to :c:func:`yices_update` for
   functions of arity *n=1* (or single-dimensional arrays).


.. c:function:: term_t yices_update2(term_t fun, term_t arg1, term_t arg2, term_t v)

   Creates the function update *(update fun (arg1 arg2) v)*

   This constructor is equivalent to :c:func:`yices_update` for
   functions of arity *n=2* (or two-dimensional arrays).


.. c:function:: term_t yices_update3(term_t fun, term_t arg1, term_t arg2, term_t arg3, term_t v)

   Creates the function update *(update fun (arg1 arg2 arg3) v)*

   This constructor is equivalent to :c:func:`yices_update` for
   functions of arity *n=3* (or three-dimensional arrays).


.. c:function:: term_t yices_forall(uint32_t n, term_t var[], term_t body)

   Creates the quantified term: *(forall (var[0] ... var[n-1]): body)*

   **Parameters**

   - *n* is the number of variables

   - *var* must be an array of *n* variables

   - *body* must be a Boolean term

   Parameter *n* must be positive and no more than :c:macro:`YICES_MAX_VARS`.

   All the elements in array *var* must be constructed with function :c:enum:`yices_new_variable`,
   and the array must not contain duplicate elements.

   **Error report**

   - if *n* is more than :c:macro:`YICES_MAX_VARS`:

     -- error code: :c:enum:`TOO_MANY_VARS`

     -- badval := *n*

   - if one *var[i]* is not a variable:

     -- error code: :c:enum:`VARIABLE_REQUIRED`

     -- term1 := *var[i]*

   - if a variable *x* occurs twice in array *var*:

     -- error code: :c:enum:`DUPLICATE_VARIABLE`

     -- term1 := *x*

   **Warning**

   - array *var* may be modified.

.. c:function:: term_t yices_exists(uint32_t n, term_t var[], term_t body)

   Creates the quantified term *(exists (var[0] ... var[n-1]) body)*

   This function is similar to :c:func:`yices_forall`. The parameters must
   satisfy the same constraints and the possible error reports are the same.

   **Warning**

   - array *var* may be modified.

.. c:function:: term_t yices_lambda(uint32_t n, const term_t var[], term_t body)

   Creates the lambda term *(lambda (var[0] ... var[n-1]) body)*

   **Parameters**

   - *n* is the number of variables. It must be positive and no mode than :c:enum:`YICES_MAX_VARS`

   - *var* is an array of *n* variables.

   - *body* can be any term

   As in constructors :c:func:`yices_forall` and
   :c:func:`yices_exists`, all the elements in array *var* must be
   constructed with function :c:enum:`yices_new_variable`, and the
   array must not contain duplicate elements.

   **Error report**

   - if *n* is more than :c:macro:`YICES_MAX_VARS`:

     -- error code: :c:enum:`TOO_MANY_VARS`

     -- badval := *n*

   - if one *var[i]* is not a variable:

     -- error code: :c:enum:`VARIABLE_REQUIRED`

     -- term1 := *var[i]*

   - if a variable *x* occurs twice in array *var*:

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

.. c:function:: term_t yices_or(uint32_t n, term_t arg[])

   Constructs the disjunction *(or arg[0] ... arg[n-1])*

   **Parameters**

   - *n* is the number of arguments. It must be positive and no mode than :c:macro:`YICES_MAX_ARITY`.

   - *arg* must be an array of *n* Boolean terms

   **Error report**

   - if *n* is more than :c:macro:`YICES_MAX_ARITY`:

     -- error code: :c:enum:`TOO_MANY_ARGUMENTS`

     -- badval: *n*

   **Warning**

   -  array *arg* may be modified.
    

.. c:function:: term_t yices_or2(term_t t1, term_t t2)

   Constructs the term *(or t1 t2)*
 
   This function is equivalent to :c:func:`yices_or` with *n=2*.

   **Parameters**

   - *t1* and *t2* must be Boolean terms


.. c:function:: term_t yices_or3(term_t t1, term_t t2, term_t t3)

   Constructs the term *(or t1 t2 t3)*
 
   This function is equivalent to :c:func:`yices_or` with *n=3*.

   **Parameters**

   - *t1*, *t2*, and *t3* must be Boolean terms


.. c:function:: term_t yices_and(uint32_t n, term_t arg[])

   Constructs the conjunction *(and arg[0] ... arg[n-1])*

   **Parameters**

   - *n* is the number of arguments. It must be positive and no mode than :c:macro:`YICES_MAX_ARITY`.

   - *arg* must be an array of *n* Boolean terms

   **Error report**

   - if *n* is more than :c:macro:`YICES_MAX_ARITY`:

     -- error code: :c:enum:`TOO_MANY_ARGUMENTS`

     -- badval: *n*

   **Warning**

   -  array *arg* may be modified.
    
.. c:function:: term_t yices_and2(term_t t1, term_t t2)

   Constructs the term *(and t1 t2)*
 
   This function is equivalent to :c:func:`yices_and` with *n=2*.

   **Parameters**

   - *t1* and *t2* must be Boolean terms


.. c:function:: term_t yices_and3(term_t t1, term_t t2, term_t t3)

   Constructs the term *(and t1 t2 t3)*
 
   This function is equivalent to :c:func:`yices_and` with *n=3*.

   **Parameters**

   - *t1*, *t2*, and *t3* must be Boolean terms


.. c:function:: term_t yices_xor(uint32_t n, term_t arg[])

   Constructs the exclusive or *(xor arg[0] ... arg[n-1])*

   **Parameters**

   - *n* is the number of arguments. It must be positive and no mode than :c:macro:`YICES_MAX_ARITY`.

   - *arg* must be an array of *n* Boolean terms

   **Error report**

   - if *n* is more than :c:macro:`YICES_MAX_ARITY`:

     -- error code: :c:enum:`TOO_MANY_ARGUMENTS`

     -- badval: *n*

   **Warning**

   -  array *arg* may be modified.
    

.. c:function:: term_t yices_xor2(term_t t1, term_t t2)

   Constructs the term *(xor t1 t2)*
 
   This function is equivalent to :c:func:`yices_xor` with *n=2*.

   **Parameters**

   - *t1* and *t2* must be Boolean terms

.. c:function:: term_t yices_xor3(term_t t1, term_t t2, term_t t3)

   Constructs the term *(xor t1 t2 t3)*
 
   This function is equivalent to :c:func:`yices_xor` with *n=3*.

   **Parameters**

   - *t1*, *t2*, and *t3* must be Boolean terms


.. c:function:: term_t yices_iff(term_t t1, term_t t2)

   Constructs the equivalence *(<=> t1 t2)*

   **Parameters**

   - *t1* and *t2* must be Boolean terms


.. c:function:: term_t yices_implies(term_t t1, term_t t2)

   Constructs the implication *(=> t1 t2)*  (i.e. *t1 implies t2*)

   **Parameters**

   - *t1* and *t2* must be Boolean terms



Arithmetic Terms
----------------

.. c:function:: term_t yices_zero(void)

.. c:function:: term_t yices_int32(int32_t val)

.. c:function:: term_t yices_int64(int64_t val)

.. c:function:: term_t yices_rational32(int32_t num, uint32_t den)

.. c:function:: term_t yices_rational64(int64_t num, uint64_t den)

.. c:function:: term_t yices_mpz(const mpz_t z)

.. c:function:: term_t yices_mpq(const mpq_t q)

.. c:function:: term_t yices_parse_rational(const char *s)

.. c:function:: term_t yices_parse_float(const char *s)


.. c:function:: term_t yices_add(term_t t1, term_t t2)

.. c:function:: term_t yices_sub(term_t t1, term_t t2)

.. c:function:: term_t yices_neg(term_t t1)

.. c:function:: term_t yices_mul(term_t t1, term_t t2)

.. c:function:: term_t yices_square(term_t t1)

.. c:function:: term_t yices_power(term_t t1, uint32_t d)


.. c:function:: term_t yices_sum(uint32_t n, const term_t t[])

.. c:function:: term_t yices_division(term_t t1, term_t t2)

.. c:function:: term_t yices_product(uint32_t n, const term_t t[])


.. c:function:: term_t yices_poly_int32(uint32_t n, const int32_t a[], const term_t t[])

.. c:function:: term_t yices_poly_int64(uint32_t n, const int64_t a[], const term_t t[])

.. c:function:: term_t yices_poly_rational32(uint32_t n, const int32_t num[], const uint32_t den[], const term_t t[])

.. c:function:: term_t yices_poly_rational64(uint32_t n, const int64_t num[], const uint64_t den[], const term_t t[])

.. c:function:: term_t yices_poly_mpz(uint32_t n, const mpz_t z[], const term_t t[])

.. c:function:: term_t yices_poly_mpq(uint32_t n, const mpq_t q[], const term_t t[])


.. c:function:: term_t yices_arith_eq_atom(term_t t1, term_t t2)

.. c:function:: term_t yices_arith_neq_atom(term_t t1, term_t t2)

.. c:function:: term_t yices_arith_geq_atom(term_t t1, term_t t2)

.. c:function:: term_t yices_arith_leq_atom(term_t t1, term_t t2)

.. c:function:: term_t yices_arith_gt_atom(term_t t1, term_t t2)

.. c:function:: term_t yices_arith_lt_atom(term_t t1, term_t t2)


.. c:function:: term_t yices_arith_eq0_atom(term_t t)

.. c:function:: term_t yices_arith_neq0_atom(term_t t)

.. c:function:: term_t yices_arith_geq0_atom(term_t t)

.. c:function:: term_t yices_arith_leq0_atom(term_t t)

.. c:function:: term_t yices_arith_gt0_atom(term_t t)

.. c:function:: term_t yices_arith_lt0_atom(term_t t)



Bitvector Terms
---------------

.. _access_to_term_representation:

Access to Term Components
-------------------------
