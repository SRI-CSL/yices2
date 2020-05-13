:tocdepth: 2

.. highlight:: c

.. _miscellaneous_operations:

Miscellaneous Operations
========================

This section describes functions for assigning names to terms and
types and for building terms and types by parsing expressions in the
Yices language. It also documents term substitutions and support for
garbage collection.


.. _names_api:


Names
-----

It is possible to assign names to terms and types, and later retrieve
a term or a type by its name.

For each term and type, Yices stores a *base name* that's used for
pretty printing. Initially, the base name is :c:macro:`NULL`.  It is set on the
first call to :c:func:`yices_set_term_name` or
:c:func:`yices_set_type_name`.

In addition, Yices maintains two symbol tables that map names to
terms and names to types, respectively. The name spaces for types and
terms are disjoint. The term or type to which a name refers can be
changed, and Yices provides a scoping mechanism:

- When function ``yices_set_term_name(t, name)`` is called, then the
  previous mapping for ``name`` (if any) is hidden and now ``name`` refers
  to term ``t``.

- If function ``yices_remove_term_name(name)`` is called, then the current
  mapping for ``name`` is removed and the previous mapping (if any)
  is restored.

Functions :c:func:`yices_set_type_name` and
:c:func:`yices_remove_type_name` behave in the same way.

File :file:`examples/names.c` included in the distributions
illustrates these functions. You can also download it :download:`here <_static/names.c>`.
   



Type Names
..........

.. c:function:: int32_t yices_set_type_name(type_t tau, const char *name)

   Attaches a name to a type.

   **Parameters**

   - *tau* can be any valid type

   - *name* must be a ``'\0'``-terminated string.

   If *tau* does not have a base name yet, then *name* is stored as base name for *tau*.

   If *name* currently refers to a type, then this current mapping is
   hidden, then the mapping from *name* to *tau* is recorded in the
   symbol table for types.

   Yices makes an internal copy of the string *name*.

   **Returned value**

   - If *tau* is not valid, the function returns -1 and sets the error report.
     Otherwise, the function returns 0.


.. c:function:: const char* yices_get_type_name(type_t tau)

   Retrieves the base name of a type.

   This function returns :c:macro:`NULL` if the type *tau* is invalid
   or has no base name. Otherwise it returns the base name of *tau*.

.. c:function:: type_t yices_get_type_by_name(const char *name)

   Gets a type by its name.

   This function returns the type mapped to *name* or :c:macro:`NULL_TYPE`
   if nothing is mapped to *name* in the symbol table.

.. c:function:: void yices_remove_type_name(const char *name)

   Removes the current mapping of name from the symbol table for types.

   This function has no effect if *name* does not refer to any type.

   Otherwise, the current mapping of *name* is removed. If *name* was
   previously mapped to another type, then this previous mapping is
   restored.

.. c:function:: int32_t yices_clear_type_name(type_t tau)

   Removes the base name of a type.

   If *tau* is not a valid type, this function returns -1, and sets
   the error report. Otherwise, it returns 0.

   If type *tau* does not have a base name, this function does nothing
   and returns 0.

   Otherwise, the mapping from *tau*'s base name to *tau* is removed
   from the symbol table and *tau*'s base name is removed.


Term Names
..........

.. c:function:: int32_t yices_set_term_name(term_t t, const char *name)

   Attaches a name to a term.

   **Parameters**

   - *t* can be any valid term

   - *name* must be a ``'\0'``-terminated string.

   If *t* does not have a base name yet, then *name* is stored as base name for *t*.

   If *name* currently refers to a term, then this current mapping is hidden.

   Then the mapping from *name* to *t* is recorded in the symbol table for terms.

   Yices makes an internal copy of the string *name*.

   **Returned value**

   - If *t* is not valid, the function returns -1 and sets the error report.
     Otherwise, the function returns 0.


.. c:function:: const char* yices_get_term_name(term_t t)

   Retrieves the base name of a term.

   This function returns :c:macro:`NULL` if the term *t* is invalid or has no
   base name. Otherwise it returns the base name of *t*.

.. c:function:: term_t yices_get_term_by_name(const char *name)

   Gets a term by its name.

   This function returns the term mapped to *name* or :c:macro:`NULL_TERM`
   if nothing is mapped to *name* in the symbol table.

.. c:function:: void yices_remove_term_name(const char *name)

   Removes the current mapping of name from the symbol table for terms.

   This function has no effect if *name* does not refer to any term.

   Otherwise, the current mapping of *name* is removed. If the *name*
   was previously mapped to another term, then this previous mapping
   is restored.

.. c:function:: int32_t yices_clear_term_name(term_t t)

   Removes the base name of a term.

   If *t* is not a valid term, then this function returns -1,
   and sets the error report. Otherwise, it returns 0.

   If term *t* does not have a base name, this function does nothing
   and returns 0.

   Otherwise, the mapping from *t*'s base name to *t* is removed from
   the symbol table then *t*'s base name is removed.

.. _parsing_api:

Parsing
-------

Parsing functions convert a string into a term or a type. The string
must be a type or term expression in the Yices language
(cf. :ref:`yices_language`).  The input string must be terminated by
``'\0'``.  If a symbol occurs in the string, its value (either as a
term or a type, depending on the context) is retrieved in the symbol
table for terms or types.

The parsing functions return :c:macro:`NULL_TYPE` or
:c:macro:`NULL_TERM` if there's an error, including a syntax error.
The *line* and *column* fields of the error report give information about
the error location in the string.

.. c:function:: type_t yices_parse_type(const char *s)

   Parses string *s* as a type.

.. c:function:: term_t yices_parse_term(const char *s)

   Parses string *s* as a term.


Substitutions
-------------

A substitution replaces one or more variables or uninterpreted terms
by other terms. A substitution is defined by two term arrays of the same size:

  - *var* must be an array of variables or uninterpreted terms.

    This array defines the domain of the substitution. It is allowed to
    mix variables and uninterpreted terms in the array.

  - *map* specifies the replacement terms.

    The variable or uninterpreted term in *var[i]* is replaced by the term *map[i]*.

The types must be consistent: *map[i]*'s type must be a subtype of *var[i]*'s type.

If the same term occurs several times in *var[i]* then the last occurrence counts.
For example, if *v[0] = x* and *v[1] = x* then *x* is mapped to *map[1]* in the
substitution, not to *map[0]* (unless *x* occurs in the rest of the array *var*).


.. c:function:: term_t yices_subst_term(uint32_t n, const term_t var[], const term_t map[], term_t t)

   Applies a substitution to a term.

   **Parameters**

   - *n* is the size of arrays *var* and *map*.

   - *var* and *map* define the substitution.
 
   - *t* is the term to which the substitution is applied.

   Every element of *var* must be either a variable (cf. :c:func:`yices_new_variable`) or
   an uninterpreted term (cf. :c:func:`yices_new_uninterpreted_term`).

   Every (free) occurrence of *var[i]* in *t* is replaced by term *map[i]*.

   It's allowed to have *n=0*, in which case this operation returns *t* unchanged.
 
   The function returns :c:macro:`NULL_TERM` if there's an error.

   **Error report**

   - if *var[i]* or *map[i]* is not a valid term:

     -- error code: :c:enum:`INVALID_TERM`

     -- term1 := the invalid term

   - if *var[i]* is not a variable or uninterpreted term:

     -- error code: :c:enum:`VARIABLE_REQUIRED`

     -- term1 := *var[i]*

   - if *map[i]*'s type is wrong:

     -- error code: :c:enum:`TYPE_MISMATCH`

     -- term1 := *map[i]*

     -- type1 := type of *var[i]*

   - if the substitution creates a term of too high degree:

     -- error code: :c:enum:`DEGREE_OVERFLOW`



.. c:function:: int32_t yices_subst_term_array(uint32_t n, const term_t var[], const term_t map[], uint32_t m, term_t t[])

   Applies a substitution to an array of terms.

   **Parameters**

   - *n* is the size of arrays *var* and *map*.

   - *var* and *map* define the substitution.
 
   - *t* is an array of *m* terms.

   The constraints on *var* and *map* are the same as in function :c:func:`yices_subst_term`.

   This function applies the substitution defined by *var* and *map*
   to the *m* terms of *t*.  The result is stored in place in array *t*.
   Assuming there's no error, this function has the same effect as the loop::

       for (i=0; i<m; i++) {
         t[i] = yices_subst_term(n, var, map, t[i]);
       }

   But it is more efficient to call :c:func:`yices_subst_term_array`
   than to use such a loop in your code.

   The function returns -1 if there's an error or 0 otherwise.

   The possible error reports are the same as for function :c:func:`yices_subst_term`.


Garbage Collection
------------------

By default, Yices never deletes any terms or types. All the terms and
types returned by the constructors can always be used by the
application. There's no explicit term or type deletion function.

If you want to delete terms or types that are no longer useful, you
must make an explicit call to the garbage collector by calling
function :c:func:`yices_garbage_collect`.

Yices uses a mark-and-sweep garbage collector. Given a set of root
terms and types that must be preserved, Yices marks the roots then
recursively marks all the terms and types on which the roots depend.
After this marking phase, all unmarked terms and types are deleted.

The set of roots is constructed as follows:

1) First, every term or type that is used in a live context or model
   is a root. For example, all the formulas asserted in a context
   are preserved by the garbage collector until the context is
   deleted.

2) In addition, more roots can be specified using any of the following
   mechanisms (they can be combined).

   - Give a list of root terms and types as arguments to :c:func:`yices_garbage_collect`.

   - Set parameter ``keep_named`` to true when calling :c:func:`yices_garbage_collect`.

     If this flag is true, all the terms and types that are stored in
     the symbol tables are added to the set of roots.

   - Maintain reference counts for individual terms and types, using
     the functions:

        - :c:func:`yices_incref_type`

        - :c:func:`yices_decref_type`

        - :c:func:`yices_incref_term`

        - :c:func:`yices_decref_term`

     When :c:func:`yices_garbage_collect` is called, all the terms or
     types with a positive reference counter are added to the set of
     roots. If the functions above are never called, then all the
     terms and types are considered to have a reference count of
     zero.

     Just decrementing a reference counter to zero does not delete
     anything. The terms and types are not deleted until function
     :c:func:`yices_garbage_collect` is called.


.. c:function:: uint32_t yices_num_types(void)

   Returns the number of types internally stored in Yices.

.. c:function:: uint32_t yices_num_terms(void)

   Returns the number of terms internally stored in Yices.

.. c:function:: int32_t yices_incref_type(type_t tau)

   Increments the reference counter of a type.

   This function returns -1 if *tau* is not a valid type, or 0 otherwise.

.. c:function:: int32_t yices_decref_type(type_t tau)

   Decrements the reference counter of a type.

   The type *tau* must be valid and its reference counter must be positive.
   If *tau*'s reference count is zero, the function keeps it unchanged
   and reports an error.

   The function returns -1 if there's an error, or 0 otherwise.

   **Error report**

   - if *tau*'s reference counter is zero:

     -- error code: :c:enum:`BAD_TYPE_DECREF`


.. c:function:: int32_t yices_incref_term(term_t t)

   Increments the reference counter of a term.

   This function returns -1 if *t* is not a valid term, or 0 otherwise.

.. c:function:: int32_t yices_decref_term(term_t t)

   Decrements the reference counter of a term.

   The term *t* must be valid and its reference counter must be
   positive.  If *t*'s reference count is zero, the function leaves it
   unchanged and reports an error.

   The function returns -1 if there's an error, or 0 otherwise.

   **Error report**

   - if *t*'s reference counter is zero:

     -- error code: :c:enum:`BAD_TERM_DECREF`


.. c:function:: uint32_t yices_num_posref_types(void)

   Returns the number of types that havee a positive reference count.
   This number is 0 if no call to :c:func:`yices_incref_type` was made.

.. c:function::  uint32_t yices_num_posref_terms(void)

   Returns the number of temrs that havee a positive reference count.
   This number is 0 if no call to :c:func:`yices_incref_term` was made.


.. c:function:: void yices_garbage_collect(const term_t t[], uint32_t nt, const type_t tau[], uint32_t ntau, int32_t keep_named)

   Calls the garbage collector.

   **Parameters**

   - *t*: optional array of terms to preserve

   - *nt*: number of terms in array *t*

   - *tau*: optional array of types to preserve

   - *ntau*: number of types in array *tau*

   - *keep_named*: indicates whether named terms and types should be preserved

   If *t* is not :c:macro:`NULL`, then all the elements *t[0 ... nt-1]* are added to the
   set of roots and will not be deleted.

   If *tau* is not :c:macro:`NULL`, then all the elements *tau[0 ... ntau-1]* are added to
   the set of roots and will not be deleted.

   If *keep_named* is non-zero (i.e., true) then all the terms and types accessible via
   the symbol tables are also preserved. See :ref:`names_api`.

   In addition, as explained above, all the terms and types with a
   positive reference count and all the terms used in a model or
   context are preserved.

   This function silently ignore any element of array *t* and *tau* that's not a valid
   term or type.
