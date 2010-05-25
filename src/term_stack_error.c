/*
 * ERROR MESSAGES/DIAGNOSIS ON EXCEPTION RAISED BY TERM STACK
 */

#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>

#include "yices_error.h"
#include "yices_version.h"
#include "yices_exit_codes.h"
#include "yices.h"

#include "term_stack_error.h"




/*
 * Error messages
 */
static const char * const code2string[NUM_TSTACK_ERRORS] = {
  "no error",
  "internal error",
  "operation not supported",
  "undefined term",
  "undefined type",
  "invalid rational format",
  "invalid float format",
  "invalid bitvector binary format",
  "invalid bitvector hexadecimal format",
  "cannot redefine type",
  "cannot redefine term",
  "duplicate name",
  "duplicate variable name",
  "invalid operation",
  "wrong number of arguments",
  "constant too large",
  "constant is not an integer",
  "symbol required",
  "numerical constant required",
  "type required",
  "error in arithmetic operation",
  "division by zero",
  "divisor is not a constant",
  "bitsize must be positive",
  "bitvectors have incompatible sizes",
  "number cannot be converted to a bitvector",
  "error in bitvector arithmetic operation",
  "error in bitvector operation",
  "incompatible types in define",
  "yices error",
};


/*
 * Translation of term-stack opcodes to string.
 *
 * We use two tables because some operators have a different name in
 * the SMT-LIB notation and in the Yices language.
 */
static const char * const opcode2smt_string[NUM_OPCODES] = {
  "no_op",
  "define-type",
  "define",
  "bind",
  "declare_var",
  "let",

  "bitvector type",
  "scalar type",   // not in SMT
  "tuple type",    // not in SMT
  "function type",

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
  "store",
  "forall",
  "exists",

  "addition",
  "subtraction",
  "negation",
  "multiplication",
  "division",
  "inequality",
  "inequality",
  "inequality",
  "inequality",

  "bv constant",
  "bvadd",
  "bvsub",
  "bvmul",
  "bvneg",
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
  "extract",
  "concat",
  "repeat",
  "sign_extend",
  "zero_extend",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",

  "bvshl",
  "bvlshr",
  "bvashr",
  "bvdiv",
  "bvrem",
  "bvsdiv",
  "bvsrem",
  "bvsmod",
  "bvredor",
  "bvredand",
  "bvcomp",

  "build term",
  "build type",

  "exit",
  "check",
  "echo",
  "include",
  "assert",
  "push",
  "pop",
  "dump-context",
};



/*
 * Translate opcode to string
 */
static const char * const opcode2yices_string[NUM_OPCODES] = {
  "no_op",
  "define-type",
  "define",
  "bind",
  "declare_var",
  "let",

  "bitvector type",
  "scalar type",
  "tuple type",
  "function type",

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
  "update",
  "forall",
  "exists",

  "addition",
  "subtraction",
  "negation",
  "multiplication",
  "division",
  "inequality",
  "inequality",
  "inequality",
  "inequality",

  "mk-bv",
  "bv-add",
  "bv-sub",
  "bv-mul",
  "bv-neg",
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
  "bv-extract",
  "bv-concat",
  "bv-repeat",
  "bv-sign-extend",
  "bv-zero-extend",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",
  "bitvector inequality",

  "bv-shl",
  "bv-lshr",
  "bv-ashr",
  "bv-udiv",
  "bv-urem",
  "bv-sdiv",
  "bv-srem",
  "bv-smod",
  "bv-redor",
  "bv-redand",
  "bv-comp",

  "build term",
  "build type",

  "exit",
  "check",
  "echo",
  "include",
  "assert",
  "push",
  "pop",
  "reset",
  "show-model",
  "eval",
  "dump-context",
};



/*
 * Global pointer: either equal to opcode2yices_string or to opcode2smt_string.
 */
static const char * const *opcode2string;





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
 */
static void yices_error(FILE *f, char *name, tstack_t *tstack) {
  if (name == NULL) {
    fprintf(f, "%s: ", name);
  }
  fprintf(f, "error in %s, line %"PRId32", column %"PRId32": ",
	  opcode2string[tstack->error_op], tstack->error_loc.line, tstack->error_loc.column);

  yices_print_error(f);
}



/*
 * Print an error message for the given exception
 */
static void base_term_stack_error(FILE *f, char *name, tstack_t *tstack, tstack_error_t exception) {
  assert(exception != TSTACK_NO_ERROR);

  if (exception == TSTACK_YICES_ERROR) {
    yices_error(f, name, tstack);
    return;
  }

  if (name == NULL) {
    name = "Error";
  }  
  fprintf(f, "%s: %s ", name, code2string[exception]);

  switch (exception) {    
  case TSTACK_INTERNAL_ERROR:
  case TSTACK_INVALID_OP:
  case TSTACK_NOT_A_SYMBOL:
  case TSTACK_NOT_A_TYPE:
    fprintf(f, "Internal exception: opcode = %"PRId32"\n", (int32_t) tstack->error_op);
    report_bug("Term-stack error");
    break;

  case TSTACK_INVALID_FRAME:
    fprintf(f, "in %s (line %"PRId32", column %"PRId32")\n",
	    opcode2string[tstack->error_op], tstack->error_loc.line, tstack->error_loc.column);
    break;

  case TSTACK_OP_NOT_IMPLEMENTED:
   fprintf(f, "(%s)\n", opcode2string[tstack->error_op]);
    break;

  case TSTACK_UNDEF_TERM:
  case TSTACK_UNDEF_TYPE:
  case TSTACK_DUPLICATE_SCALAR_NAME:
  case TSTACK_DUPLICATE_VAR_NAME:
  case TSTACK_RATIONAL_FORMAT:
  case TSTACK_FLOAT_FORMAT:
  case TSTACK_BVBIN_FORMAT:
  case TSTACK_BVHEX_FORMAT:
  case TSTACK_TYPENAME_REDEF:
  case TSTACK_TERMNAME_REDEF:
    fprintf(f, "%s (line %"PRId32", column %"PRId32")\n",
	    tstack->error_string, tstack->error_loc.line, tstack->error_loc.column);
    break;

  case TSTACK_NOT_A_RATIONAL:
  case TSTACK_INTEGER_OVERFLOW:
  case TSTACK_NOT_AN_INTEGER:
  case TSTACK_ARITH_ERROR:
  case TSTACK_DIVIDE_BY_ZERO:
  case TSTACK_NON_CONSTANT_DIVISOR:
  case TSTACK_NEGATIVE_BVSIZE:
  case TSTACK_INVALID_BVCONSTANT:
  case TSTACK_INCOMPATIBLE_BVSIZES:
  case TSTACK_BVARITH_ERROR:
  case TSTACK_BVLOGIC_ERROR:
  case TSTACK_TYPE_ERROR_IN_DEFTERM:
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
 * Severity of an error:
 * - severity 0: means caused by incorrect input
 * - severity 1: means bug in SMT parser or something related
 * - severity 2: means bug in term_stack or Yices parser
 */
static uint8_t severity[NUM_YICES_ERRORS] = {
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
  0, // WRONG_NUMBER_OF_ARGUMENTS
  0, // TYPE_MISMATCH
  0, // INCOMPATIBLE_TYPES
  2, // DUPLICATE_VARIABLE (bug in term_stack).
  0, // INCOMPATIBLE_BVSIZES
  2, // EMPTY_BITVECTOR

  /*
   * The following errors are handled directly by the parser
   * so they should not occur. Since they are benign, they
   * can have severity 0 anyway.
   */
  0, // INVALID_TOKEN
  0, // SYNTAX_ERROR
  0, // UNDEFINED_TYPE_NAME
  0, // UNDEFINED_TERM_NAME
  0, // REDEFINED_TYPE_NAME 
  0, // REDEFINED_TERM_NAME
  0, // DUPLICATE_NAME_IN_SCALAR
  0, // DUPLICATE_VAR_NAME
  0, // INTEGER_OVERFLOW
  0, // INTEGER_REQUIRED
  0, // RATIONAL_REQUIRED
  0, // SYMBOL_REQUIRED
  0, // NON_CONSTANT_DIVISOR
  0, // NEGATIVE_BVSIZE
  0, // ARITH_ERROR
  0, // BVARITH_ERROR,
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
void term_stack_error(FILE *f, char *name, tstack_t *tstack, tstack_error_t exception) {
  opcode2string = opcode2yices_string;
  base_term_stack_error(f, name, tstack, exception);
  if (exception == TSTACK_YICES_ERROR && fatal_error(yices_error_code())) {
    report_bug("Internal error");
  }
}


/*
 * Same thing but also abort for exceptions that should not occur in
 * SMT-LIB input (e.g., error codes involving tuples).
 */
void term_stack_smt_error(FILE *f, char *name, tstack_t *tstack, tstack_error_t exception) {
  opcode2string = opcode2smt_string;
  base_term_stack_error(f, name, tstack, exception);

  if (exception == TSTACK_YICES_ERROR && fatal_smt_error(yices_error_code())) {
    report_bug("Internal error (SMT-LIB)");
  }
}
