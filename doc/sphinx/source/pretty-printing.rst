:tocdepth: 2

.. include:: macros

.. highlight:: c

.. _pretty_printing:

Pretty Printing
===============

.. _ppbox:

.. figure:: _static/ppbox2.svgz
   :width: 400px
   :alt: Rectangle print area

   Display Area


All pretty-printing operations use a rectangular display area
characterized by its width, height, and offset as shown in Figure
:ref:`ppbox`. The width and offset are measured in number of columns,
and the height is a number of lines. The offset is the distance to the
beginning of the line. The width must be at least four columns and the
height must be at least one line.

Pretty-printing functions either write to a stream or construct and
return a string. For example, to print a term ``t`` to ``stdout`` you
can call::

   yices_pp_term(stdout, t, 120, 40, 0);

This uses a display area of 120 columns |times| 40 lines. To construct a
string, you can do::

   char *s = yices_term_to_string(t, 120, 40, 0);

The string ``s`` is formatted so that ``printf("%s\n", s)`` produces
the same result as the previous call to :c:func:`yices_pp_term`.

If the area is too small, then the pretty printer truncates the term
and prints ellipses. Example :download:`test_pp.c <_static/test_pp.c>`
illustrates this behavior. It prints a term made of twenty conjuncts
as follows:

.. code-block:: none

   (and (>= (+ 1 x0 x1) 0) (>= (+ 1 x1 x2) 0) (>= (+ 1 x2 x3) 0) (>= (+ 1 x3 x4) 0) (>= (+ 1 x4 x5) 0)
        (>= (+ 1 x5 x6) 0) (>= (+ 1 x6 x7) 0) (>= (+ 1 x7 x8) 0) (>= (+ 1 x8 x9) 0) (>= (+ 1 x9 x10) 0)
        (>= (+ 1 x10 x11) 0) (>= (+ 1 x11 x12) 0) (>= (+ 1 x12 x13) 0) (>= (+ 1 x13 x14) 0)
        (>= (+ 1 x14 x15) 0) (>= (+ 1 x15 x16) 0) (>= (+ 1 x16 x17) 0) (>= (+ 1 x17 x18) 0)
        (>= (+ 1 x18 x19) 0) (>= (+ 1 x0 x19) 0))


When the area is too small, the result is truncated:

.. code-block:: none

   (and
    (>= (+ 1 x0 x1) 0)
    (>= (+ 1 x1 x2) 0)
    (>= (+ 1 x2 x3) 0)
    (>= (+ 1 x3 x4) 0)
    (>= (+ 1 x4 x5) 0)
    (>= (+ 1 x5 x6) 0)
    (>= (+ 1 x6 x7) 0) (...



Printing Terms and Types
------------------------

The pretty-printing API includes functions to print terms, types, and
models. They may report the usual errors (i.e., :c:enum:`INVALID_TYPE`
and :c:enum:`INVALID_TERM` if the input is not valid). They can also
report that writing to a stream failed with error code
:c:enum:`OUTPUT_ERROR`. In such a case, ``errno`` and the standard
functions ``perror`` and ``strerror`` can be used to get more
explanation.


.. c:function:: int32_t yices_pp_type(FILE* f, type_t tau, uint32_t width, uint32_t height, uint32_t offset)

   Pretty-prints a type.

   **Parameters**

   - *f* is the output stream

   - *tau* is the type to print

   - *width*, *height*, and *offset* specify the display area

   The stream *f* must be open and writable.

   The function returns -1 if there's an error or 0 otherwise.

   **Error report**

   - if *tau* is not valid:

     -- error code: :c:enum:`INVALID_TYPE`

     -- type1 := *tau*

   - if writing to *f* fails:

     -- error code: :c:enum:`OUTPUT_ERROR`


.. c:function:: int32_t yices_pp_type_fd(int fd, type_t tau, uint32_t width, uint32_t height, uint32_t offset)

   Pretty-prints a type.

   This function is similar to :c:func:`yices_pp_type` except that it uses a file descriptor *fd*
   instead of a stream *f*.


.. c:function:: int32_t yices_pp_term(FILE* f, term_t t, uint32_t width, uint32_t height, uint32_t offset)

   Pretty-prints a term.

   **Parameters**

   - *f* is the output stream

   - *t* is the term to print

   - *width*, *height*, and *offset* specify the display area

   The stream *f* must be open and writable.

   The function returns -1 if there's an error or 0 otherwise.

   **Error report**

   - if *t* is not valid:

     -- error code: :c:enum:`INVALID_TERM`

     -- term1 := *t*

   - if writing to *f* fails:

     -- error code: :c:enum:`OUTPUT_ERROR`


.. c:function:: int32_t yices_pp_term_fd(int fd, term_t t, uint32_t width, uint32_t height, uint32_t offset)

   Pretty-prints a term.

   This function is similar to :c:func:`yices_pp_term` except that it uses a file descriptor *fd*
   instead of a stream *f*.



.. c:function:: int32_t yices_pp_term_array(FILE* f, uint32_t n, const term_t a[], uint32_t width, uint32_t height, uint32_t offset, int32_t horiz)

   Pretty-prints an array of terms.

   **Parameters**

   - *f* is the output stream

   - *n* is the size of the array

   - *a* is an array of *n* terms to print

   - *width*, *height*, and *offset* specify the display area

   - *horiz* is a Boolean flag that specifies the layout

   If *horiz* is true (i.e., not zero) the function attempts to print several terms, separated by spaces,
   on each line of the display areas: 

   .. code-block:: none

      a[0] a[1] ... a[k]
      a[k+1] ... a[n-1]

   Otherwise (i.e., if *horiz=0*) the terms are printed one below the other:

   .. code-block:: none

      a[0]
      a[1]
       ...
      a[n-1]

   The function first checks whether all the terms in array *a* are
   valid. If any *a[i]* is invalid, it prints nothing, sets the error
   report, and returns -1.

   Otherwise, the function prints the terms in the display area in the
   format specified by the *horiz* flag.  Some terms may be omitted if
   the area is too small. The function returns 0, unless an error
   occurs while attempting to write to stream *f*. In this case, the
   function sets the error report to :c:enum:`OUTPUT_ERROR` and
   returns -1.


.. c:function:: int32_t yices_pp_term_array_fd(int fd, uint32_t n, const term_t a[], uint32_t width, uint32_t height, uint32_t offset, int32_t horiz)

   Pretty-prints an array of terms.

   This function is similar to :c:func:`yices_pp_term_array` except that it uses a file descriptor *fd*
   instead of a stream *f*.


.. c:function:: char* yices_type_to_string(type_t tau, uint32_t width, uint32_t height, uint32_t offset)

   Converts a type to a string.

   This functions returns a string *s* formatted as if *tau* was
   printed in the given display area.

   **Parameters**

   - *tau* is the type to print

   - *width*, *height*, and *offset* specify the display area


   The function returns :c:macro:`NULL` if *tau* is not valid and sets the error report.

   Otherwise, it returns a string *s*. This string must be deleted when it is no longer
   needed by calling :c:func:`yices_free_string`.

   If you don't care too much about formatting, set *height* to 1, *offset* to 0, and use a large enough
   *width*. This will build a string *s* that does not contain any line breaks.


.. c:function:: char* yices_term_to_string(term_t t, uint32_t width, uint32_t height, uint32_t offset)

   Converts a term to a string.

   This constructs a string *s* formatted as if *t* was pretty-printed.

   **Parameters**

   - *t* is the term to print

   - *width*, *height*, and *offset* specify the display area

   
   The function returns :c:macro:`NULL` if *tau* is not valid and sets the error report.

   Otherwise, it returns a string *s*. This string must be deleted when it is no longer
   needed by calling :c:func:`yices_free_string`.

   If you don't care too much about formatting, set *height* to 1, *offset* to 0, and use a large enough
   *width*. This will build a string *s* that does not contain any line breaks.




Printing Models and Term Values
-------------------------------

.. c:function:: int32_t yices_pp_model(FILE* f, model_t* mdl, uint32_t width, uint32_t height, uint32_t offset)

   Pretty-prints a model.

   **Parameters**

   - *f*: output stream

   - *mdl* is the model to print

   - *width*, *height*, and *offset* specify the display area


   Stream *f* must be open and writable.

   This function prints *mdl* in the given display area. If writing to *f* fails, it returns -1. 
   Otherwise, it returns 0.

   For every uninterpreted that has name and has a value in *mdl*, the function will print a line
   of the form:

   .. code-block:: none

      (= <name> <value>

   For terms that have a function type, the format is different; it will look something like this:

   .. code-block:: none

      (function b
       (type (-> int bool))
         (= (b 0) true)
         (= (b 1) true)
        (default false))

   This shows how function *b* is defined in the model: it's a function from *int* to *bool* such
   that *(b 0)* and *(b 1)* are *true*, and *(b i)* is *false* for any *i* that's not equal to 0 or 1.

   **Error report**

   - if writing to *f* fails

     -- error code: :c:enum:`OUTPUT_ERROR`


   .. note:: The model *mdl* stores a mapping from uninterpreted
             terms to values. This function prints the value assigned to these
             uninterpreted terms, but it skips any uninterpreted term that does not have
             a name.


.. c:function:: int32_t yices_pp_model_fd(int fd, model_t* mdl, uint32_t width, uint32_t height, uint32_t offset)

   Pretty-prints a model.

   This function is similar to :c:func:`yices_pp_model` except that it uses a file descriptor *fd*
   instead of a stream *f*.


.. c:function:: void yices_print_model(FILE* f, model_t* mdl)

   Prints a model.

   This function prints model *mdl* on stream *f*. It has the same behavior as
   :c:func:`yices_pp_model` but it does not use a pretty printer.


.. c:function:: int32_t yices_print_model_fd(int fd, model_t* mdl)

   Prints a model.
 
   Same behavior as :c:func:`yices_print_model`, except that it uses a file descriptor *fd*
   instead of a stream *f*.

   This function returns -1 if the write to file *fd* fails. It returns 0 otherwise.


.. c:function:: int32_t yices_pp_term_values(FILE *f, model_t *mdl, uint32_t n, const term_t a[], uint32_t width, uint32_t height, uint32_t offset)

   Pretty print the value of *n* terms in a model

   The function prints the name and value of terms *a[0]* |...| *a[n-1]* on stream  *f*.

   **Parameters**

   - *f*: output stream

   - *mdl*: model

   - *n*: number of terms to print

   - *a*: array of *n* terms

   - *width*, *height*, *offset*: define the pretty-print area

   The function returns -1 if there's an error or 0 otherwise.

   **Error report**

   - if one of the terms *a[i]* is not valid:

     -- error code: :c:enum:`INVALID_TERM`

     -- term1 := *a[i]*

   - if writing to *f* fails:

     -- error code: :c:enum:`OUTPUT_ERROR`


.. c:function:: int32_t yices_pp_term_values_fd(int32_t fd, model_t *mdl, uint32_t n, const term_t a[], uint32_t width, uint32_t height, uint32_t offset)

   Pretty print the value of *n* terms in a model.

   This is the same as :c:func:`yices_pp_term_values`, except that it uses a file descriptor *fd*
   instead of a strean *f*.


.. c:function:: int32_t yices_print_term_values(FILE *f, model_t *mdl, uint32_t n, const term_t a[])

   Print the values of *n* tems in a model.

   This is similar to :c:func:`yices_pp_term_values`, except that it does not use pretty printing.


.. c:function:: int32_t yices_print_term_values_fd(int fd, model_t *mdl, uint32_t n, const term_t a[])

   Print the values of *n* tems in a model.

   This function is similar to :c:func:`yices_print_term_values`, except that it uses a file descriptor *fd*
   instead of a stream *f*.


.. c:function:: char* yices_model_to_string(model_t* mdl, uint32_t width, uint32_t height, uint32_t offset)

   Converts a model to a string.

   This function returns a string *s* constructed by pretty printing *mdl* in the given display area.
   The string must be deleted when no longer needed by calling :c:func:`yices_free_string`. 
   
