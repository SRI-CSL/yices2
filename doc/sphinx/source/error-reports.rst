:tocdepth: 2

.. highlight:: c

.. _error_reports:

Error Reporting
===============

When an API function is called with incorrect arguments or when an
error occurs for whatever reason, the function returns a special
value---which is typically a negative integer or the :c:macro:`NULL`
pointer---and stores information about the error in a global variable
of type :c:type:`error_report_t`. The error report stores an error
code and additional information (see :ref:`error_types`).

The following functions give access to the error report.

.. c:function:: error_code_t yices_error_code(void)

   Returns the global error code. The result is 0 if there's no error,
   or a positive constant that identifies the error type otherwise.

.. c:function:: error_report_t* yices_error_report(void)
 
   This returns a pointer to the global error report.

.. c:function:: void yices_clear_error(void)

   This resets the global error code to :c:enum:`YICES_NO_ERROR` (i.e., 0)

.. c:function:: int32_t yices_print_error(FILE* f)

   This function converts the current error code and error report into
   an error message, then it prints the message on output stream
   *f*. This stream must be writable.

   The function returns -1 if there is an error while writing to *f*,
   or 0 if there's no error. In case of write error, the standard C
   variable *errno* and functions such as *perror* and relatives can
   be used for diagnostic.


.. c:function:: int32_t yices_print_error_fd(int fd)

   This is a variant of the previous function that writes to file
   descriptor *fd* instead of an output stream. The file must be open
   and writable. All output will be appended at the end of the file.

   The function returns -1 if there's an error or 0 otherwise.

.. c:function:: char* yices_error_string(void)

   This function builds an error message from the current error
   code and error-report structure, and returns it as a string.

   To avoid memory leaks, the returned string must be freed when it is
   no longer used by calling :c:func:`yices_free_string`.


