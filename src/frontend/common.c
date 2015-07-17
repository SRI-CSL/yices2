/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <assert.h>
#include <stdio.h>
#include <stdarg.h>
#include <inttypes.h>

#include "api/yices_globals.h"
#include "frontend/common.h"
#include "yices.h"
#include "yices_exit_codes.h"


/*
 * Table to convert  smt_status to a string
 */
const char* const status2string[] = {
  "idle",
  "searching",
  "unknown",
  "sat",
  "unsat",
  "interrupted",
};


/*
 * Conversion of EF preprocessing codes to string
 */
const char * const efcode2error[NUM_EF_CODES] = {
  "no error",
  "assertions contain uninterpreted functions",
  "invalid quantifier nesting (not an exists/forall problem)",
  "non-atomic universal variables",
  "non-atomic existential variables",
  "internal error",
};


/*
 * Table to convert  ef-solver status to a string
 */
const char* const ef_status2string[] = {
  "idle",
  "searching",
  "unknown",
  "sat",
  "unsat",
  "interrupted",
  "subst error",
  "tval error",
  "check error",
  "assert error",
  "error",
};

/*
 * Conversion of internalization code to an error message
 */
const char * const code2error[NUM_INTERNALIZATION_ERRORS] = {
  "no error",
  "internal error",
  "type error",
  "formula contains free variables",
  "logic not supported",
  "the context does not support uninterpreted functions",
  "the context does not support scalar types",
  "the context does not support tuples",
  "the context does not support uninterpreted types",
  "the context does not support arithmetic",
  "the context does not support bitvectors",
  "the context does not support function equalities",
  "the context does not support quantifiers",
  "the context does not support lambdas",
  "not an IDL formula",
  "not an RDL formula",
  "non-linear arithmetic not supported",
  "too many variables for the arithmetic solver",
  "too many atoms for the arithmetic solver",
  "arithmetic solver exception",
  "bitvector solver exception",
};



void __attribute__((noreturn)) freport_bug(FILE *fp, const char *format, ...) {
  va_list p;

  fprintf(fp, "\n*************************************************************\n");
  fprintf(fp, "FATAL ERROR: ");
  va_start(p, format);
  vfprintf(fp, format, p);
  va_end(p);
  fprintf(fp, "\n*************************************************************\n");
  fprintf(fp, "Please report this bug to yices-bugs@csl.sri.com.\n");
  fprintf(fp, "To help us diagnose this problem, please include the\n"
                  "following information in your bug report:\n\n");
  fprintf(fp, "  Yices version: %s\n", yices_version);
  fprintf(fp, "  Build date: %s\n", yices_build_date);
  fprintf(fp, "  Platform: %s (%s)\n", yices_build_arch, yices_build_mode);
  fprintf(fp, "\n");
  fprintf(fp, "Thank you for your help.\n");
  fprintf(fp, "*************************************************************\n\n");
  fflush(fp);

  exit(YICES_EXIT_INTERNAL_ERROR);
}







