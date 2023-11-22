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

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>

#include "api/yices_error.h"
#include "frontend/yices/yices_tstack_ops.h"
#include "parser_utils/term_stack_error.h"

#include "yices.h"
#include "yices_exit_codes.h"


/*
 * Error messages
 */
static const char * const code2string[NUM_TSTACK_ERRORS] = {
  "no error",
  "internal error",
  "operation not supported",
  "undefined term",
  "undefined type",
  "undefined type macro",
  "invalid rational format",
  "invalid float format",
  "invalid bitvector binary format",
  "invalid bitvector hexadecimal format",
  "cannot redefine type",
  "cannot redefine term",
  "cannot redefine type macro",
  "duplicate name",
  "duplicate variable name",
  "duplicate type name",
  "invalid operation",
  "wrong number of arguments",
  "constant too large",
  "exponent must be non-negative",
  "constant is not an integer",
  "string required",
  "symbol required",
  "numerical constant required",
  "type required",
  "error in arithmetic operation",
  "division by zero",
  "divisor is not a constant",
  "size must be positive",
  "bitvectors have incompatible sizes",
  "number cannot be converted to a bitvector",
  "error in bitvector arithmetic operation",
  "error in bitvector operation",
  "incompatible types in define",
  "strings are not terms",
  "variable values are not matching",
  "not a constant",
  "not a variable",
  "yices error",
};


/*
 * Translation of term-stack opcodes to string.
 *
 * We use two tables because some operators have a different name in
 * the SMT-LIB notation and in the Yices language.
 */
static const char * const opcode2smt_string[NUM_BASE_OPCODES] = {
  "no_op",

  "define-type",
  "define",

  "bind",
  "var declaration",
  "type-var declaration",  // for SMT2
  "let",

  "bitvector type",
  "scalar type",   // not in SMT
  "tuple type",    // not in SMT
  "function type",
  "macro application",  // for SMT2

  "function application",
  "if-then-else",
  "equality",
  "disequality",
  "distinct",
  "not",
  "or",
  "and",
  "xor",
  "iff",
  "implies",
  "mk-tuple", // not in SMT
  "select",   // not in SMT
  "tuple update", // not in SMT
  "store",
  "forall",
  "exists",
  "lambda",  // not in SMT

  "addition",
  "subtraction",
  "negation",
  "multiplication",
  "division",
  "exponentiation", // not in SMT
  "inequality",
  "inequality",
  "inequality",
  "inequality",

  "bv constant",
  "bvadd",
  "bvsub",
  "bvmul",
  "bvneg",
  "bvpow",   // not in SMT
  "bvudiv",
  "bvurem",
  "bvsdiv",
  "bvsrem",
  "bvsmod",

  "bvnot",
  "bvand",
  "bvor",
  "bvxor",
  "bvnand",
  "bvnor",
  "bvxnor",

  "shift_left0",
  "shift_left1",
  "shift_right0",
  "shift_right1",
  "ashift_right",
  "rotate_left",
  "rotate_right",

  "bvshl",
  "bvlshr",
  "bvashr",

  "extract",
  "concat",
  "repeat",
  "sign_extend",
  "zero_extend",

  "bvredand",
  "bvredor",
  "bvcomp",

  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",

  "bool-to-bv",  // not in SMT
  "bit",         // not in SMT

  "floor",       // not in SMT
  "ceil",        // not in SMT
  "abs",         // not in SMT
  "div",         // not in SMT
  "mod",         // not in SMT
  "divides",     // not in SMT
  "is_int",      // not in SMT

  "build term",
  "build type",
};



/*
 * Translate opcode to string: Yices version has more opcodes
 */
static const char * const opcode2yices_string[NUM_YICES_OPCODES] = {
  "no_op",

  "define-type",
  "define",

  "bind",
  "var declaration",
  "type-var declaration",  // SMT2 only
  "let",

  "bitvector type",
  "scalar type",
  "tuple type",
  "function type",
  "type-macro application", // SMT2

  "function application",
  "if-then-else",
  "equality",
  "disequality",
  "distinct",
  "not",
  "or",
  "and",
  "xor",
  "<=>",
  "=>",
  "mk-tuple",
  "select",
  "tuple update",
  "update",
  "forall",
  "exists",
  "lambda",

  "addition",
  "subtraction",
  "negation",
  "multiplication",
  "division",
  "exponentiation",
  "inequality",
  "inequality",
  "inequality",
  "inequality",

  "mk-bv",
  "bv-add",
  "bv-sub",
  "bv-mul",
  "bv-neg",
  "bv-pow",
  "bv-udiv",
  "bv-urem",
  "bv-sdiv",
  "bv-srem",
  "bv-smod",

  "bv-not",
  "bv-and",
  "bv-or",
  "bv-xor",
  "bv-nand",
  "bv-nor",
  "bv-xnor",

  "bv-shift-left0",
  "bv-shift-left1",
  "bv-shift-right0",
  "bv-shift-right1",
  "bv-ashift-right",
  "bv-rotate-left",
  "bv-rotate-right",

  "bv-shl",
  "bv-lshr",
  "bv-ashr",

  "bv-extract",
  "bv-concat",
  "bv-repeat",
  "bv-sign-extend",
  "bv-zero-extend",

  "bv-redand",
  "bv-redor",
  "bv-comp",

  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",

  "bool-to-bv",
  "bit",

  "floor",
  "ceil",
  "abs",
  "div",
  "mod",
  "divides",
  "is_int",
  "build term",
  "build type",

  // commands in yices_tstack_ops.h
  "define-type",
  "define",
  "exit",
  "assert",
  "check",
  "show-model",
  "eval",
  "push",
  "pop",
  "reset",
  "echo",
  "include",
  "set-param",
  "show-param",
  "show-params",
  "show-stats",
  "reset-stats",
  "set-timeout",
  "show-timeout",
  "help",
  "ef-solve",
  "export-to-dimacs",
  "show-implicant",
  "dump-context",
};




/*
 * BUG in Yices: Print an error message then exit
 */
void report_bug(const char *s) {
  fprintf(stderr, "\n*************************************************************\n");
  fprintf(stderr, "FATAL ERROR: %s\n\n", s);
  fprintf(stderr, "Please report this bug to yices-bugs@csl.sri.com.\n");
  fprintf(stderr, "To help us diagnose this problem, please include the\n"
                  "following information in your bug report:\n\n");
  fprintf(stderr, "  Yices version: %s\n", yices_version);
  fprintf(stderr, "  Build date: %s\n", yices_build_date);
  fprintf(stderr, "  Platform: %s (%s)\n", yices_build_arch, yices_build_mode);
  fprintf(stderr, "\n");
  fprintf(stderr, "Thank you for your help.\n");
  fprintf(stderr, "*************************************************************\n\n");
  fflush(stderr);

  exit(YICES_EXIT_INTERNAL_ERROR);
}




/*
 * Error reported by term_api:
 * - tstack->error_op = operation being executed
 * - tstack->error_loc = location of the argument expression (approximative)
 *   that triggered the error
 * - opcode2string = either opcoode2yicse_string or opecode2smt_string
 */
static void yices_error(FILE *f, const char *name, tstack_t *tstack, const char * const opcode2string[]) {
  if (name != NULL) {
    fprintf(f, "%s: ", name);
  }
  fprintf(f, "error in %s, line %"PRId32", column %"PRId32": ",
          opcode2string[tstack->error_op], tstack->error_loc.line, tstack->error_loc.column);

  print_error(f);
}



/*
 * Print an error message for the given exception
 */
static void base_term_stack_error(FILE *f, const char *name, tstack_t *tstack, tstack_error_t exception, const char * const opcode2string[]) {
  assert(exception != TSTACK_NO_ERROR);

  if (exception == TSTACK_YICES_ERROR) {
    yices_error(f, name, tstack, opcode2string);
    return;
  }

  if (name == NULL) {
    fprintf(f, "Error: %s ", code2string[exception]);
  } else {
    fprintf(f, "%s: %s ", name, code2string[exception]);
  }

  switch (exception) {
  case TSTACK_INTERNAL_ERROR:
  case TSTACK_INVALID_OP:
  case TSTACK_NOT_A_SYMBOL:
  case TSTACK_NOT_A_TYPE:
  case TSTACK_STRINGS_ARE_NOT_TERMS:  // should never be raised by the yices or smt1 parser
    fprintf(f, "Internal exception: opcode = %"PRId32"\n", (int32_t) tstack->error_op);
    report_bug("Term-stack error");
    break;

  case TSTACK_INVALID_FRAME:
  case TSTACK_NONPOSITIVE_BVSIZE:
    fprintf(f, "in %s (line %"PRId32", column %"PRId32")\n",
            opcode2string[tstack->error_op], tstack->error_loc.line, tstack->error_loc.column);
    break;

  case TSTACK_OP_NOT_IMPLEMENTED:
    fprintf(f, "(%s)\n", opcode2string[tstack->error_op]);
    break;

  case TSTACK_UNDEF_TERM:
  case TSTACK_UNDEF_TYPE:
  case TSTACK_UNDEF_MACRO:
  case TSTACK_DUPLICATE_SCALAR_NAME:
  case TSTACK_DUPLICATE_VAR_NAME:
  case TSTACK_DUPLICATE_TYPE_VAR_NAME:
  case TSTACK_RATIONAL_FORMAT:
  case TSTACK_FLOAT_FORMAT:
  case TSTACK_BVBIN_FORMAT:
  case TSTACK_BVHEX_FORMAT:
  case TSTACK_TYPENAME_REDEF:
  case TSTACK_TERMNAME_REDEF:
  case TSTACK_MACRO_REDEF:
    fprintf(f, "%s (line %"PRId32", column %"PRId32")\n",
            tstack->error_string, tstack->error_loc.line, tstack->error_loc.column);
    break;

  case TSTACK_INTEGER_OVERFLOW:
  case TSTACK_NEGATIVE_EXPONENT:
  case TSTACK_NOT_AN_INTEGER:
  case TSTACK_NOT_A_STRING:
  case TSTACK_NOT_A_RATIONAL:
  case TSTACK_ARITH_ERROR:
  case TSTACK_DIVIDE_BY_ZERO:
  case TSTACK_NON_CONSTANT_DIVISOR:
  case TSTACK_INVALID_BVCONSTANT:
  case TSTACK_INCOMPATIBLE_BVSIZES:
  case TSTACK_BVARITH_ERROR:
  case TSTACK_BVLOGIC_ERROR:
  case TSTACK_TYPE_ERROR_IN_DEFTERM:
  case TSTACK_VARIABLES_VALUES_NOT_MATCHING:
    fprintf(f, "(line %"PRId32", column %"PRId32")\n",
            tstack->error_loc.line, tstack->error_loc.column);
    break;

  default:
    fprintf(f, "Invalid error code: %"PRId32"\n", (int32_t) exception);
    report_bug("Term-stack error");
    break;
  }
}


/*
 * Error codes defined in yices_types:
 *   0 to  99 --> reserved for basic errors in term/type construction
 * 100 to 299 --> reserved for parser errors
 * 300 to 399 --> reserved for errors in context operations
 * 400 to ... --> other error codes
 *
 * The term_stack should only trigger error codes in the range [0..99]
 * (more exactly in the range [0 .. BAD_TYPE_DECREF].
 * We assign a severity to these errors, as defined below.
 */
#define NUM_YICES_ERRORS (BAD_TYPE_DECREF+1)

/*
 * Severity of an error:
 * - severity 0: means caused by incorrect input
 * - severity 1: means bug in SMT parser or something related
 * - severity 2: means bug in term_stack or Yices parser
 */
static const uint8_t severity[NUM_YICES_ERRORS] = {
  2, // NO_ERROR (should never be raised)
  2, // INVALID_TYPE
  2, // INVALID_TERM
  2, // INVALID_CONSTANT_INDEX (bug in scalar-type construction)
  2, // INVALID_VAR_INDEX (bug in declare-var)
  1, // INVALID_TUPLE_INDEX (no tuples in SMT-LIB)
  2, // INVALID_RATIONAL_FORMAT (raised by yices_parse_rational, which is not used in term_stack)
  2, // INVALID_FLOAT_FORMAT (raised by yices_parse_float, which is not used in term_stack)
  2, // INVALID_BVBIN_FORMAT (raised by yices_parse_bvbin)
  2, // INVALID_BVHEX_FORMAT (raised by yices_parse_bvhex)
  0, // INVALID_BITSHIFT
  0, // INVALID_BVEXTRACT
  0, // INVALID_BITEXTRACT
  0, // TOO_MANY_ARGUMENTS
  0, // TOO_MANY_VARS,
  0, // MAX_BVSIZE_EXCEEDED
  0, // DEGREE_OVERFLOW
  0, // DIVISION_BY_ZERO
  0, // POS_INT_REQUIRED
  0, // NONNEG_INT_REQUIREF
  2, // SCALAR_OR_UTYPE_REQUIRED (bug in scalar-type construction)
  0, // FUNCTION_REQUIRED
  1, // TUPLE_REQUIRED (no tuples in SMT-LIB)
  2, // VARIABLE_REQUIRED (bug in term_stack)
  0, // ARITHTERM_REQUIRED
  0, // BITVECTOR_REQUIRED
  0, // SCALAR_TERM_REQUIRED
  0, // WRONG_NUMBER_OF_ARGUMENTS
  0, // TYPE_MISMATCH
  0, // INCOMPATIBLE_TYPES
  2, // DUPLICATE_VARIABLE (bug in term_stack).
  0, // INCOMPATIBLE_BVSIZES
  2, // EMPTY_BITVECTOR
  2, // ARITHCONSTANT_REQUIRED (should never be raised by term stack, see eval_mk_div)
  2, // INVALID_MACRO (bug in term_stack)
  0, // TOO_MANY_MACRO_PARAMS (used for SMT-LIB 2)
  2, // TYPE_VAR_REQUIRED (bug in term_stack)
  0, // DUPLICATE_TYPE_VAR (used in SMT-LIB 2)
  2, // BVTYPE_REQUIRED (not used anywhere)
  2, // BAD_TERM_DECREF (not used by term_stack)
  2, // BAD_TYPE_DECREF (not used by term_stack)
};


/*
 * Check for fatal errors in YICES
 * - return true if the error is a bug
 */
static inline bool fatal_error(error_code_t error) {
  return severity[error] >= 2;
}

/*
 * Check for fatal errors in SMT-LIB
 * - return true if the error involve operations that do not exist in SMT-LIB
 */
static inline bool fatal_smt_error(error_code_t error) {
  return severity[error] >= 1;
}



/*
 * Print an error message on stream f for the given exception.
 * - if name is non- NULL, the error message is
 *   'name: message ...'
 * - if name is NULL the error message is
 *   'Error: message ...'
 * The term-stack location, top-operator, etc. are used to help locate the error.
 *
 * Abort and print a request for a bug report if the error is
 * internal to Yices.
 */
void term_stack_error(FILE *f, const char *name, tstack_t *tstack, tstack_error_t exception) {
  base_term_stack_error(f, name, tstack, exception, opcode2yices_string);
  if (exception == TSTACK_YICES_ERROR && fatal_error(yices_error_code())) {
    report_bug("Internal error");
  }
}


/*
 * Same thing but also abort for exceptions that should not occur in
 * SMT-LIB input (e.g., error codes involving tuples).
 */
void term_stack_smt_error(FILE *f, const char *name, tstack_t *tstack, tstack_error_t exception) {
  base_term_stack_error(f, name, tstack, exception, opcode2smt_string);
  if (exception == TSTACK_YICES_ERROR && fatal_smt_error(yices_error_code())) {
    report_bug("Internal error (SMT-LIB)");
  }
}
