/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * ERROR MESSAGES/DIAGNOSIS ON EXCEPTION RAISED BY TERM STACK
 */

#ifndef __TERM_STACK_ERROR_H
#define __TERM_STACK_ERROR_H


#include <stdio.h>

#include "parser_utils/term_stack2.h"


/*
 * Print an error message on stream f, for the given exception.
 * - if name is non NULL, the error message is
 *   'name: error message ...'
 * - if name is NULL the error message is
 *   'Error: message ...'
 * The term-stack location and other fields are used to help locate the error.
 *
 * The function aborts and prints a request for a bug report if the
 * error is internal to Yices.
 */
extern void term_stack_error(FILE *f, const char *name, tstack_t *tstack, tstack_error_t exception);


/*
 * Same thing but abort also for exceptions that should not occur in
 * SMT-LIB input (e.g., error codes involving tuples).
 */
extern void term_stack_smt_error(FILE *f, const char *name, tstack_t *tstack, tstack_error_t exception);


/*
 * Function to call when an internal error is detected.
 * - it aborts with an error message and requests a bug report.
 */
extern void report_bug(const char *s) __attribute__ ((noreturn));


#endif /* __TERM_STACK_ERROR_H */
