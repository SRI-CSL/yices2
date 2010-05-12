/*
 * ERROR MESSAGES/DIAGNOSIS ON EXCEPTION RAISED BY TERM STACK
 */

#ifndef __TERM_STACK_ERROR_H
#define __TERM_STACK_ERROR_H


#include <stdio.h>

#include "term_stack.h"


/*
 * Print an error message on stream f, for the given exception.
 * - if name is no NULL, the error message is 
 *   'name: error message ...'
 * - if name is NULL the error message is 
 *   'Error: message ...'
 * The term-stacks location, etc. are used to help locate the error.
 *
 * Abort and print a request for a bug report if the error is 
 * internal to Yices. 
 */
extern void term_stack_error(FILE *f, char *name, tstack_t *tstack, tstack_error_t exception);


/*
 * Same thing but abort also for exceptions that should not occur in
 * SMT-LIB input (e.g., error codes involving tuples).
 */
extern void term_stack_smt_error(FILE *f, char *name, tstack_t *tstack, tstack_error_t exception);



/*
 * Function to call when an internal error is detected.
 * - it aborts with an error message and request for a bug report.
 */
extern void report_bug(const char *s) __attribute__ ((noreturn));


#endif /* __TERM_STACK_ERROR_H */
