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



void fprint_error(FILE* fp, const char *format, ...) {
  va_list p;
  //FIXME
  //open_error();
  va_start(p, format);
  if (vfprintf(fp, format, p) < 0) {
    //failed_output();
  }
  va_end(p);
  //close_error();
}


/*
 * Print the translation code returned by assert
 */
void print_internalization_code(int32_t code, uint32_t verbosity) {
  assert(-NUM_INTERNALIZATION_ERRORS < code && code <= TRIVIALLY_UNSAT);
  if (code == TRIVIALLY_UNSAT) {
    fprintf(stderr, "unsat\n");
    fflush(stderr);
  } else if (verbosity > 0 && code == CTX_NO_ERROR) {
    //    report_ok(client);
  } else if (code < 0) {
    code = - code;
    fprint_error(stderr, code2error[code]);
  }
}

/*
 * Print the translation code returned by ef_analyze
 */
void print_ef_analyze_code(ef_code_t code, FILE *err) {
  if (code == EF_NO_ERROR) {
    //    report_ok(client);
  } else {
    fprint_error(err, efcode2error[code]);
  }
}



/*
 * Print the efsolver status
 */
void print_ef_status(ef_client_t *efc, uint32_t verbosity, FILE *err) {
  ef_status_t stat;
  int32_t error;
  ef_solver_t *efsolver;

  efsolver = efc->efsolver;

  assert(efsolver != NULL && efc->efdone);

  if (verbosity > 0) {
    printf("ef-solve: %"PRIu32" iterations\n", efsolver->iters);
  }

  stat = efsolver->status;
  error = efsolver->error_code;

  switch (stat) {
  case EF_STATUS_SAT:
  case EF_STATUS_UNKNOWN:
  case EF_STATUS_UNSAT:
  case EF_STATUS_INTERRUPTED:
    fputs(ef_status2string[stat], stdout);
    fputc('\n', stdout);
    if (verbosity > 0) {
      if (stat == EF_STATUS_SAT) {
        print_ef_solution(stdout, efsolver);
        fputc('\n', stdout);
      }
    }
    fflush(stdout);
    break;

  case EF_STATUS_SUBST_ERROR:
    if (error == -1) {
      fprint_error(err, "EF solver failed: degree overflow in substitution");
    } else {
      assert(error == -2);
      freport_bug(err, "EF solver failed: internal error");
    }
    break;

  case EF_STATUS_ASSERT_ERROR:
    assert(error < 0);
    print_internalization_code(error, verbosity);
    break;

  case EF_STATUS_MDL_ERROR:
  case EF_STATUS_IMPLICANT_ERROR:
  case EF_STATUS_PROJECTION_ERROR:
  case EF_STATUS_TVAL_ERROR:
  case EF_STATUS_CHECK_ERROR:
  case EF_STATUS_ERROR:
  case EF_STATUS_IDLE:
  case EF_STATUS_SEARCHING:
    freport_bug(err, "ef-status: %s\n", ef_status2string[stat]);
    break;

  }
}

