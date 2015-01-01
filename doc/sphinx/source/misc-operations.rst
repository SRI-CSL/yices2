:tocdepth: 2

.. highlight:: c

.. _miscellaneous_operations:

Miscellaneous Operations
========================

.. _names_api:

Names
-----

It is possible to assign names to terms and types, and later retrieve
a term or a type by its name.

For each term and type, Yices stores a *base name* that's used for
pretty printing. Initially, the base name is NULL.  It is set on the
first call to :c:func:`yices_set_term_name` or
:c:func:`yices_set_type_name`.

In addition, Yices maintains two symbol tables that maps names to
terms and types, respectively. The name spaces for types and terms
are disjoint. The term or type to which a name refers can be changed,
and Yices provides a scoping mechanism:

- When function ``yices_set_term_name(t, name)`` is called, then the
  previous mapping for ``name`` (if any) is hidden and now ``name`` refers
  to term ``t``.

- If function ``yices_remove_term_name(name)`` is called, then the current
  mapping for ``name`` is removed and the previous mapping (if any)
  is restored.

Functions :c:func:`yices_set_type_name` and
:c:func:`yices_remove_type_name` behave in the same way.


Type Names
..........

.. c:function:: int32_t yices_set_type_name(type_t tau, const char *name)

   Attaches a name to a type.

   **Parameters**

   - *tau* can be any valid type

   - *name* must be a ``'\0'``-terminated string.

   If *tau* does not have a base name yet, then *name* is stored as base name for *tau*.

   If *name* currently refers to a type, then this current mapping is hidden.

   Then the mapping from *name* to *tau* is recorded in the symbol table for types.

   Yices makes an internal copy of the string *name*.

   **Returned value**

   - If *tau* is not valid, the function returns -1 and sets the error report.
     Otherwise, the function returns 0.


.. c:function:: yices_get_type_name(type_t tau)

   Retrieves the base name of a type.

   This function returns NULL if the type *tau* is invalid or has no
   base name. Otherwise it returns the base name of *tau*.

.. c:function:: yices_get_type_by_name(const char *name)

   Gets a type by its name.

   This function returns the type mapped to *name* or :c:macro:`NULL_TYPE`
   if nothing is mapped to *name* in the symbol table.

.. c:function:: yices_remove_type_name(const char *name)

   Removes the current mapping of name from the symbol table for types.

   This function has no effect if *name* does not refer to any type.

   Otherwise, the current mapping of *name* is removed. If the *name*
   was previously mapped to another type, then this previous mapping
   is restored.

.. c:function:: int32_t yices_clear_type_name(type_t tau)

   Removes the base name of a type.

   If *tau* is not a valid type, then this function returns -1,
   and sets the error report. Otherwise, it returns 0.

   If type *tau* does not have a base name, this function does nothing
   and returns 0.

   Otherwise, mapping from *tau*'s base name to *tau* is removed from
   the symbol table then *tau*'s base name is removed.


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


.. c:function:: yices_get_term_name(term_t t)

   Retrieves the base name of a term.

   This function returns NULL if the term *t* is invalid or has no
   base name. Otherwise it returns the base name of *t*.

.. c:function:: yices_get_term_by_name(const char *name)

   Gets a term by its name.

   This function returns the term mapped to *name* or :c:macro:`NULL_TERM`
   if nothing is mapped to *name* in the symbol table.

.. c:function:: yices_remove_term_name(const char *name)

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

   Otherwise, mapping from *t*'s base name to *t* is removed from
   the symbol table then *t*'s base name is removed.

.. _parsing_api:

Parsing
-------

Substitutions
-------------

Garbage Collection
------------------
