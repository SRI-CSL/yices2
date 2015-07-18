/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Various strings/error messages used by both the Yices and SMT2 frontends.
 */
#ifndef __FRONTEND_COMMON_H
#define __FRONTEND_COMMON_H

#include <stdio.h>

#include "exists_forall/ef_client.h"

/*
 * Table to convert  smt_status to a string
 */
extern const char* const status2string[];

/*
 * Conversion of EF preprocessing codes to string
 */
extern const char * const efcode2error[];

/*
 * Table to convert  ef-solver status to a string
 */
extern const char* const ef_status2string[];

/*
 * Conversion of internalization code to an error message
 */
extern const char * const code2error[];


/*
 * Ask for a bug report
 */
extern void __attribute__((noreturn)) freport_bug(FILE *fp, const char *format, ...);

#endif /* __FRONTEND_COMMON_H */
