/*
 * ALL SMT-LIB 2 COMMANDS
 */

#if defined(CYGWIN) || defined(MINGW)
#define EXPORTED __declspec(dllexport)
#define __YICES_DLLSPEC__ EXPORTED
#else
#define EXPORTED __attribute__((visibility("default")))
#endif


#include <stdio.h>
#include <stdarg.h>
#include <inttypes.h>
#include <string.h>
#include <assert.h>

#include "refcount_strings.h"
#include "attribute_values.h"
#include "smt_logic_codes.h"
#include "smt2_lexer.h"
#include "smt2_commands.h"

#include "yices.h"
#include "yices_exit_codes.h"
#include "yices_extensions.h"
#include "yices_globals.h"


/*
 * NAME STACKS
 */

/*
 * Initialize; nothing allocated yet
 */
static void init_smt2_name_stack(smt2_name_stack_t *s) {
  s->names = NULL;
  s->top = 0;
  s->size = 0;
}

/*
 * Make room for some names to be pushed
 */
static void extend_smt2_name_stack(smt2_name_stack_t *s) {
  uint32_t n;

  n = s->size;
  if (n == 0) {
    n = DEF_SMT2_NAME_STACK_SIZE;
    assert(n <= MAX_SMT2_NAME_STACK_SIZE);
    s->names = (char **) safe_malloc(n * sizeof(char *));
    s->size = n;
  } else {
    n += (n >> 1) + 1;
    if (n > MAX_SMT2_NAME_STACK_SIZE) {
      out_of_memory();
    }
    s->names = (char **) safe_realloc(s->names, n * sizeof(char *));
    s->size = n;
  }
}


/*
 * Push name on top of the stack
 * - name must be a refcount strincg
 * - name's reference counter is incremented
 */
static void smt2_push_name(smt2_name_stack_t *s, char *name) {
  uint32_t i;

  i = s->top;
  if (i == s->size) {
    extend_smt2_name_stack(s);
  }
  assert(i < s->size);
  s->names[i] = name;
  string_incref(name);
  s->top = i+1;
}


/*
 * Remove names on top of the stack
 * - ptr = new top: names[0 ... ptr-1] are kept
 */
static void smt2_pop_names(smt2_name_stack_t *s, uint32_t ptr) {
  uint32_t n;

  n = s->top;
  while (n > ptr) {
    n --;
    string_decref(s->names[n]);
  }
  s->top = n;
}


/*
 * Deletion
 */
static void delete_smt2_name_stack(smt2_name_stack_t *s) {
  smt2_pop_names(s, 0);
  safe_free(s->names);
  s->names = NULL;
}


/*
 * PUSH/POP STACK
 */

/*
 * Initialize: nothing allocated yet
 */
static void init_smt2_stack(smt2_stack_t *s) {
  s->data = NULL;
  s->top = 0;
  s->size = 0;
}

/*
 * Make room
 */
static void extend_smt2_stack(smt2_stack_t *s) {
  uint32_t n;

  n = s->size;
  if (n == 0) {
    n = DEF_SMT2_STACK_SIZE;
    assert(n <= MAX_SMT2_STACK_SIZE);
    s->data = (smt2_push_rec_t *) safe_malloc(n * sizeof(smt2_push_rec_t));
    s->size = n;
  } else {
    n += (n >> 1) + 1;
    if (n > MAX_SMT2_STACK_SIZE) {
      out_of_memory();
    }
    s->data = (smt2_push_rec_t *) safe_realloc(s->data, n * sizeof(smt2_push_rec_t));
    s->size = n;
  }
}


/*
 * Push data:
 * - m = multiplicity
 * - terms, types, macros = number of term/type/macro declarations
 */
static void smt2_stack_push(smt2_stack_t *s, uint32_t m, uint32_t terms, uint32_t types, uint32_t macros) {
  uint32_t i;

  i = s->top;
  if (i == s->size) {
    extend_smt2_stack(s);
  }
  assert(i < s->size);
  s->data[i].multiplicity = m;
  s->data[i].term_decls = terms;
  s->data[i].type_decls = types;
  s->data[i].macro_decls = macros;
  s->top = i+1;
}


/*
 * Get the top element:
 * - warning: this pointer may become invalid is data is pushed on s
 */
static inline smt2_push_rec_t *smt2_stack_top(smt2_stack_t *s) {
  assert(s->top > 0);
  return s->data + (s->top - 1);
}


/*
 * Remove the top element
 */
static inline void smt2_stack_pop(smt2_stack_t *s) {
  assert(s->top > 0);
  s->top --;
}

/*
 * Delete
 */
static void delete_smt2_stack(smt2_stack_t *s) {
  safe_free(s->data);
  s->data = NULL;
}


/*
 * REQUIRED INFO
 */
static const char *yices_name = "Yices";
static const char *yices_authors = "Bruno Dutertre";
static const char *error_behavior = "immediate-exit";

/*
 * GLOBAL OBJECTS
 */
static bool done;    // set to true on exit
static attr_vtbl_t avtbl; // attribute values


// exported globals
smt2_globals_t __smt2_globals;

// search parameters
static param_t parameters;


/*
 * MAJOR ERRORS
 */

/*
 * If something goes wrong while writing to the output channel
 * or when closing it
 */
static void __attribute__((noreturn)) failed_output(void) {
  fprintf(stderr, "\n**************************************\n");
  fprintf(stderr, "FATAL ERROR\n");
  perror(__smt2_globals.out_name);
  fprintf(stderr, "\n**************************************\n\n");

  exit(YICES_EXIT_SYSTEM_ERROR);
}


/*
 * bug report
 */
static void __attribute__((noreturn)) report_bug(FILE *f) {
  fprintf(f, "\n*************************************************************\n");
  fprintf(f, "Please report this bug to yices-bugs@csl.sri.com.\n");
  fprintf(f, "To help us diagnose this problem, please include the\n"
                  "following information in your bug report:\n\n");
  fprintf(f, "  Yices version: %s\n", yices_version);
  fprintf(f, "  Build date: %s\n", yices_build_date);
  fprintf(f, "  Platform: %s (%s)\n", yices_build_arch, yices_build_mode);
  fprintf(f, "\n");
  fprintf(f, "Thank you for your help.\n");
  fprintf(f, "*************************************************************\n\n");
  fflush(f);

  exit(YICES_EXIT_INTERNAL_ERROR);
}



/*
 * OUTPUT FUNCTIONS
 */

/*
 * Formatted output: like printf but use __smt2_globals.out
 */
static void print_out(const char *format, ...) {
  va_list p;

  va_start(p, format);
  if (vfprintf(__smt2_globals.out, format, p) < 0) {
    failed_output();
  }
  va_end(p);
}


/*
 * Flush the output channel
 */
static inline void flush_out(void) {
  if (fflush(__smt2_globals.out) == EOF) {
    failed_output();
  }
}


/*
 * Report success
 */
static void report_success(void) {
  if (__smt2_globals.print_success) {
    print_out("success\n");
    flush_out();
  }
}




/*
 * ERROR REPORTS
 */

/*
 * Error prefix/suffix
 * - SMT2 wants errors to be printed as 
 *        (error "explanation")
 *   on the current output channel
 * - start_error(l, c) prints '(error "at line x, column y: '
 * - open_error() prints '(error "
 * - close_error() prints '")' and a newline then flush the output channel
 */
static void start_error(uint32_t line, uint32_t column) {
  print_out("(error \"at line %"PRIu32", column %"PRIu32": ", line, column);
}

static void open_error(void) {
  print_out("(error \"");
}

static void close_error(void) {
  print_out("\")\n");
  flush_out();
}


/*
 * Formatted error: like printf but add the prefix and close
 */
static void print_error(const char *format, ...) {
  va_list p;

  open_error();
  va_start(p, format);
  if (vfprintf(__smt2_globals.out, format, p) < 0) {
    failed_output();
  }
  va_end(p);
  close_error();
}


/*
 * Syntax error (reported by tstack)
 * - lex = lexer 
 * - expected_token = either an smt2_token or -1
 *
 * lex is as follows: 
 * - current_token(lex) = token that caused the error
 * - current_token_value(lex) = corresponding string
 * - current_token_length(lex) = length of that string
 * - lex->tk_line and lex->tk_column = start of the token in the input
 * - lex->reader.name  = name of the input file (NULL means input is stdin)
 */
static inline char *tkval(lexer_t *lex) {
  return current_token_value(lex);
}

void smt2_syntax_error(lexer_t *lex, int32_t expected_token) {
  reader_t *rd;
  smt2_token_t tk;

  tk = current_token(lex);
  rd = &lex->reader;

  start_error(rd->line, rd->column);

  switch (tk) {
  case SMT2_TK_INVALID_STRING:
    print_out("missing string terminator");
    break;

  case SMT2_TK_INVALID_NUMERAL:
    print_out("invalid numeral %s", tkval(lex));
    break;

  case SMT2_TK_INVALID_DECIMAL:
    print_out("invalid decimal %s", tkval(lex));
    break;

  case SMT2_TK_INVALID_HEXADECIMAL:
    print_out("invalid hexadecimal constant %s", tkval(lex));
    break;

  case SMT2_TK_INVALID_BINARY:
    print_out("invalid binary constant %s", tkval(lex));
    break;

  case SMT2_TK_INVALID_SYMBOL:
    print_out("invalid symbol");
    break;

  case SMT2_TK_INVALID_KEYWORD:
    print_out("invalid keyword");
    break;

  case SMT2_TK_ERROR:
    print_out("invalid token %s", tkval(lex));
    break;
    
  default:
    if (expected_token >= 0) {
      print_out("syntax error: %s expected", smt2_token_to_string(expected_token));
    } else if (expected_token == -2 && tk == SMT2_TK_SYMBOL) {
      print_out("syntax error: %s is not a command", tkval(lex));
    } else {
      print_out("syntax error");
    }
    break;
  }

  close_error();
}


/*
 * ERROR FROM YICES (in yices_error_report)
 */

/*
 * If full is true: print (error <message>)
 * Otherwise: print <message>
 */
static void print_yices_error(bool full) {
  error_report_t *error;

  if (full) open_error();

  error = yices_error_report();
  switch (error->code) {
  case INVALID_BITSHIFT:
    print_out("invalid index in rotate");
    break;
  case INVALID_BVEXTRACT:
    print_out("invalid indices in bit-vector extract");
    break;
  case TOO_MANY_ARGUMENTS:
    print_out("too many arguments. Function arity is at most %"PRIu32, YICES_MAX_ARITY);
    break;
  case TOO_MANY_VARS:
    print_out("too many variables in quantifier. Max is %"PRIu32, YICES_MAX_VARS);
    break;
  case MAX_BVSIZE_EXCEEDED:
    print_out("bit-vector size too large. Max is %"PRIu32, YICES_MAX_BVSIZE);
    break;
  case DEGREE_OVERFLOW:
    print_out("maximal polynomial degree exceeded");
    break;
  case DIVISION_BY_ZERO:
    print_out("division by zero");    
    break;
  case POS_INT_REQUIRED:
    print_out("integer argument must be positive");
    break;
  case NONNEG_INT_REQUIRED:
    print_out("integer argument must be non-negative");
    break;
  case FUNCTION_REQUIRED:
    print_out("argument is not a function");
    break;
  case ARITHTERM_REQUIRED:
    print_out("argument is not an arithmetic term");
    break;
  case BITVECTOR_REQUIRED:
    print_out("argument is not a bit-vector term");
    break;
  case WRONG_NUMBER_OF_ARGUMENTS:
    print_out("wrong number of arguments");
    break;
  case TYPE_MISMATCH:
    print_out("type error");
    break;
  case INCOMPATIBLE_TYPES:
    print_out("incompatible types");
    break;
  case INCOMPATIBLE_BVSIZES:
    print_out("arguments do not have the same number of bits");
    break;
  case EMPTY_BITVECTOR:
    print_out("bit-vectors can't have 0 bits");
    break;
  case ARITHCONSTANT_REQUIRED:
    print_out("argument is not an arithmetic constant");
    break;
  case TOO_MANY_MACRO_PARAMS:
    print_out("too many arguments in sort constructor. Max is %"PRIu32, TYPE_MACRO_MAX_ARITY);
    break;

  case CTX_FREE_VAR_IN_FORMULA:
  case CTX_LOGIC_NOT_SUPPORTED:
  case CTX_UF_NOT_SUPPORTED:
  case CTX_ARITH_NOT_SUPPORTED:
  case CTX_BV_NOT_SUPPORTED:
  case CTX_ARRAYS_NOT_SUPPORTED:
  case CTX_QUANTIFIERS_NOT_SUPPORTED:
  case CTX_NONLINEAR_ARITH_NOT_SUPPORTED:
  case CTX_FORMULA_NOT_IDL:
  case CTX_FORMULA_NOT_RDL:
  case CTX_TOO_MANY_ARITH_VARS:
  case CTX_TOO_MANY_ARITH_ATOMS:
  case CTX_TOO_MANY_BV_VARS:
  case CTX_TOO_MANY_BV_ATOMS:
  case CTX_ARITH_SOLVER_EXCEPTION:
  case CTX_BV_SOLVER_EXCEPTION:
  case CTX_ARRAY_SOLVER_EXCEPTION:
  case CTX_OPERATION_NOT_SUPPORTED:
  case CTX_INVALID_CONFIG:
  case CTX_UNKNOWN_PARAMETER:
  case CTX_INVALID_PARAMETER_VALUE:
  case CTX_UNKNOWN_LOGIC:
    print_out("context exception"); // expand
    break;

  case EVAL_UNKNOWN_TERM:
  case EVAL_FREEVAR_IN_TERM:
  case EVAL_QUANTIFIER:
  case EVAL_LAMBDA:
  case EVAL_OVERFLOW:
  case EVAL_FAILED:
    print_out("can't evaluate term value"); // expand
    break;

  case OUTPUT_ERROR:
    print_out(" IO error");
    break;

  default:
    print_out("BUG detected");
    if (full) close_error();
    report_bug(__smt2_globals.err);
    break;
  }

  if (full) close_error();
}



/*
 * EXCEPTIONS
 */

/*
 * Error messages for tstack exceptions
 * NULL means that this should never occur (i.e., fatal exception)
 */
static const char * const exception_string[NUM_SMT2_EXCEPTIONS] = {
  NULL,                                 // TSTACK_NO_ERROR
  NULL,                                 // TSTACK_INTERNAL_ERROR
  "operation not implemented",          // TSTACK_OP_NOT_IMPLEMENTED
  "undefined term",                     // TSTACK_UNDEF_TERM
  "undefined sort",                     // TSTACK_UNDEF_TYPE
  "undefined sort constructor",         // TSTACK_UNDEF_MACRO,
  "invalid numeral",                    // TSTACK_RATIONAL_FORMAT
  "invalid decimal'",                   // TSTACK_FLOAT_FORMAT
  "invalid binary",                     // TSTACK_BVBIN_FORMAT
  "invalid hexadecimal",                // TSTACK_BVHEX_FORMAT
  "can't redefine sort",                // TSTACK_TYPENAME_REDEF
  "can't redefine term",                // TSTACK_TERMNAME_REDEF
  "can't redefine sort constructor",    // TSTACK_MACRO_REDEF
  NULL,                                 // TSTACK_DUPLICATE_SCALAR_NAME
  "duplicate variable name",            // TSTACK_DUPLICATE_VAR_NAME
  "duplicate variable name",            // TSTACK_DUPLICATE_TYPE_VAR_NAME
  NULL,                                 // TSTACK_INVALID_OP
  "wrong number of arguments",          // TSTACK_INVALID_FRAME
  "constant too large",                 // TSTACK_INTEGER_OVERFLOW
  NULL,                                 // TSTACK_NEGATIVE_EXPONENT
  "integer required",                   // TSTACK_NOT_AN_INTEGER
  "string required",                    // TSTACK_NOT_A_STRING
  "symbol required",                    // TSTACK_NOT_A_SYMBOL 
  "numeral required",                   // TSTACK_NOT_A_RATIONAL
  "sort required",                      // TSTACK_NOT_A_TYPE
  "error in arithmetic operation",      // TSTACK_ARITH_ERROR
  "division by zero",                   // TSTACK_DIVIDE_BY_ZERO
  "divisor must be constant",           // TSTACK_NON_CONSTANT_DIVISOR
  "size must be positive",              // TSTACK_NONPOSITIVE_BVSIZE
  "bitvectors have incompatible sizes", // TSTACK_INCOMPATIBLE_BVSIZES
  "number can't be converted to a bitvector constant", // TSTACK_INVALID_BVCONSTANT
  "error in bitvector arithmetic operation",  //TSTACK_BVARITH_ERROR
  "error in bitvector operation",       // TSTACK_BVLOGIC_ERROR
  "incompatible sort in definition",    // TSTACK_TYPE_ERROR_IN_DEFTERM
  NULL,                                 // TSTACK_YICES_ERROR
  "missing symbol in :named attribute", // SMT2_MISSING_NAME
  "no pattern given",                   // SMT2_MISSING_PATTERN
  "not a sort identifier",              // SMT2_SYMBOL_NOT_SORT
  "not an indexed sort identifier",     // SMT2_SYMBOL_NOT_IDX_SORT
  "not a sort constructor",             // SMT2_SYMBOL_NOT_SORT_OP
  "not an indexed sort constructor",    // SMT2_SYMBOL_NOT_IDX_SORT_OP
  "not a term identifier",              // SMT2_SYMBOL_NOT_TERM
  "not an indexed term identifier",     // SMT2_SYMBOL_NOT_IDX_TERM
  "not a function identifier",          // SMT2_SYMBOL_NOT_FUNCTION
  "not an indexed function identifier", // SMT2_SYMBOL_NOT_IDX_FUNCTION
  "undefined identifier",               // SMT2_UNDEF_IDX_SORT
  "undefined identifier",               // SMT2_UNDEF_IDX_SORT_OP
  "undefined identifier",               // SMT2_UNDEF_IDX_TERM
  "undefined identifier",               // SMT2_UNDEF_IDX_FUNCTION
  "invalid qualifier: types don't match",  // SMT2_TYPE_ERROR_IN_QUAL
  "sort qualifier not supported",       // SMT2_QUAL_NOT_IMPLEMENTED
  "invalid bitvector constant",         // SMT2_INVALID_IDX_BV
};


/*
 * Conversion of opcodes to strings
 */
static const char * const opcode_string[NUM_SMT2_OPCODES] = {
  NULL,                   // NO_OP
  "sort definition",      // DEFINE_TYPE (should not occur?)
  "term definition",      // DEFINE_TERM (should not occur?)
  "binding",              // BIND?
  "variable declaration", // DECLARE_VAR
  "sort-variable declaration", // DECLARE_TYPE_VAR
  "let",                  // LET
  "BitVec",               // MK_BV_TYPE
  NULL,                   // MK_SCALAR_TYPE
  NULL,                   // MK_TUPLE_TYPE
  "function type",        // MK_FUN_TYPE
  "type constructor",     // MK_APP_TYPE
  "function application", // MK_APPLY
  "ite",                  // MK_ITE
  "equality",             // MK_EQ
  "disequality",          // MK_DISEQ
  "distinct",             // MK_DISTINCT
  "not",                  // MK_NOT
  "or",                   // MK_OR
  "and",                  // MK_AND
  "xor",                  // MK_XOR
  "iff",                  // MK_IFF (not in SMT2?)
  "=>",                   // MK_IMPLIES
  NULL,                   // MK_TUPLE
  NULL,                   // MK_SELECT
  NULL,                   // MK_TUPLE_UPDATE
  NULL,                   // MK_UPDATE (replaced by SMT2_MK_STORE)
  "forall",               // MK_FORALL
  "exists",               // MK_EXISTS
  "lambda",               // MK_LAMBDA (not in SMT2)
  "addition",             // MK_ADD
  "subtraction",          // MK_SUB
  "negation",             // MK_NEG
  "multiplication",       // MK_MUL
  "division",             // MK_DIVISION
  "exponentiation",       // MK_POW
  "inequality",           // MK_GE
  "inequality",           // MK_GT
  "inequality",           // MK_LE
  "inequality",           // MK_LT
  "bitvector constant",   // MK_BV_CONST
  "bvadd",                // MK_BV_ADD
  "bvsub",                // MK_BV_SUB
  "bvmul",                // MK_BV_MUL
  "bvneg",                // MK_BV_NEG
  "bvpow",                // MK_BV_POW (not in SMT2)
  "bvudiv",               // MK_BV_DIV
  "bvurem",               // MK_BV_REM
  "bvsdiv",               // MK_BV_SDIV
  "bvurem",               // MK_BV_SREM
  "bvsmod",               // MK_BV_SMOD
  "bvnot",                // MK_BV_NOT
  "bvand",                // MK_BV_AND
  "bvor",                 // MK_BV_OR
  "bvxor",                // MK_BV_XOR
  "bvnand",               // MK_BV_NAND
  "bvnor",                // MK_BV_NOR
  "bvxnor",               // MK_BV_XNOR
  NULL,                   // MK_BV_SHIFT_LEFT0
  NULL,                   // MK_BV_SHIFT_LEFT1
  NULL,                   // MK_BV_SHIFT_RIGHT0
  NULL,                   // MK_BV_SHIFT_RIGHT1
  NULL,                   // MK_BV_ASHIFT_RIGHT
  "rotate_left",          // MK_BV_ROTATE_LEFT
  "rotate_right",         // MK_BV_ROTATE_RIGHT
  "bvshl",                // MK_BV_SHL
  "bvlshr",               // MK_BV_LSHR
  "bvashr",               // MK_BV_ASHR
  "extract",              // MK_BV_EXTRACT
  "concat",               // MK_BV_CONCAT
  "repeat",               // MK_BV_REPEAT
  "sign_extend",          // MK_BV_SIGN_EXTEND
  "zero_extend",          // MK_BV_ZERO_EXTEND
  "bvredand",             // MK_BV_REDAND (not in SMT2)
  "bvredor",              // MK_BV_REDOR (not in SMT2)
  "bvcomp",                // MK_BV_COMP
  "bvuge",                // MK_BV_GE,
  "bvugt",                // MK_BV_GT
  "bvule",                // MK_BV_LE
  "bvult",                // MK_BV_LT
  "bvsge",                // MK_BV_SGE
  "bvsgt",                // MK_BV_SGT
  "bvsle",                // MK_BV_SLE
  "bvslt",                // MK_BV_SLT
  "build term",           // BUILD_TERM
  "build_type",           // BUILD_TYPE
  // 
  "exit",                 // SMT2_EXIT
  "end of file",          // SMT2_SILENT_EXIT
  "get_assertions",       // SMT2_GET_ASSERTIONS
  "get_assignment",       // SMT2_GET_ASSIGNMENT
  "get_proof",            // SMT2_GET_PROOF
  "get_unsat_core",       // SMT2_GET_UNSAT_CORE
  "get_value",            // SMT2_GET_VALUE
  "get_option",           // SMT2_GET_OPTION
  "get_info",             // SMT2_GET_INFO
  "set_option",           // SMT2_SET_OPTION
  "set_info",             // SMT2_SET_INFO
  "set_logic",            // SMT2_SET_LOGIC
  "push",                 // SMT2_PUSH
  "pop",                  // SMT2_POP
  "assert",               // SMT2_ASSERT,
  "check_sat",            // SMT2_CHECK_SAT,
  "declare_sort",         // SMT2_DECLARE_SORT
  "define_sort",          // SMT2_DEFINE_SORT
  "declare_fun",          // SMT2_DECLARE_FUN
  "define_fun",           // SMT2_DEFINE_FUN
  "attributes",           // SMT2_MAKE_ATTR_LIST
  "term annotation",      // SMT2_ADD_ATTRIBUTES
  "Array",                // SMT2_MK_ARRAY
  "select",               // SMT2_MK_SELECT
  "store",                // SMT2_MK_STORE
  "indexed_sort",         // SMT2_INDEXED_SORT
  "sort expression",      // SMT2_APP_INDEXED_SORT
  "indexed identifier",   // SMT2_INDEXED_TERM
  "sort qualifier",       // SMT2_SORTED_TERM
  "sort qualifier",       // SMT2_SORTED_INDEXED_TERM
  "function application", // SMT2_INDEXED_APPLY
  "sort qualifier",       // SMT2_SORTED_APPLY
  "sort qualifier",       // SMT2_SORTED_INDEXED_APPLY
  // operations not supported
  "div",                  // SMT2_MK_DIV
  "mod",                  // SMT2_MK_MOD
  "abs",                  // SMT2_MK_ABS
  "to_real",              // SMT2_MK_TO_REAL
  "to_int",               // SMT2_MK_TO_INT
  "is_int",               // SMT2_MK_IS_INT
  "divisible",            // SMT2_MK_DIVISIBLE
};


/*
 * Exception raised by tstack
 * - tstack = term stack
 * - exception = error code (defined in term_stack2.h)
 *
 * Error location in the input file is given by 
 * - tstack->error_loc.line
 * - tstack->error_loc.column
 *
 * Extra fields (depending on the exception)
 * - tstack->error_string = erroneous input
 * - tstack->error_op = erroneous operation
 */
void smt2_tstack_error(tstack_t *tstack, int32_t exception) {
  start_error(tstack->error_loc.line, tstack->error_loc.column);

  switch (exception) {
  case TSTACK_OP_NOT_IMPLEMENTED:
    print_out("operation %s not implemented", opcode_string[tstack->error_op]);
    break;
    
  case TSTACK_UNDEF_TERM:
  case TSTACK_UNDEF_TYPE:
  case TSTACK_UNDEF_MACRO:
  case TSTACK_DUPLICATE_VAR_NAME:
  case TSTACK_DUPLICATE_TYPE_VAR_NAME:
  case TSTACK_RATIONAL_FORMAT:
  case TSTACK_FLOAT_FORMAT:
  case TSTACK_BVBIN_FORMAT:
  case TSTACK_BVHEX_FORMAT:
  case TSTACK_TYPENAME_REDEF:
  case TSTACK_TERMNAME_REDEF:
  case TSTACK_MACRO_REDEF:
  case SMT2_SYMBOL_NOT_SORT:
  case SMT2_SYMBOL_NOT_IDX_SORT:
  case SMT2_SYMBOL_NOT_SORT_OP:
  case SMT2_SYMBOL_NOT_IDX_SORT_OP:
  case SMT2_SYMBOL_NOT_TERM: 
  case SMT2_SYMBOL_NOT_IDX_TERM:
  case SMT2_SYMBOL_NOT_FUNCTION: 
  case SMT2_SYMBOL_NOT_IDX_FUNCTION:
  case SMT2_UNDEF_IDX_SORT:
  case SMT2_UNDEF_IDX_SORT_OP:
  case SMT2_UNDEF_IDX_TERM:
  case SMT2_UNDEF_IDX_FUNCTION:
    print_out("%s: %s", exception_string[exception], tstack->error_string);
    break;

  case TSTACK_INVALID_FRAME:
  case TSTACK_NONPOSITIVE_BVSIZE:
    print_out("%s in %s", exception_string[exception], opcode_string[tstack->error_op]);
    break;

  case TSTACK_INTEGER_OVERFLOW:
  case TSTACK_NOT_AN_INTEGER:
  case TSTACK_NOT_A_STRING:
  case TSTACK_NOT_A_SYMBOL:
  case TSTACK_NOT_A_RATIONAL:
  case TSTACK_NOT_A_TYPE:
  case TSTACK_ARITH_ERROR:
  case TSTACK_DIVIDE_BY_ZERO:
  case TSTACK_NON_CONSTANT_DIVISOR:
  case TSTACK_INCOMPATIBLE_BVSIZES:
  case TSTACK_INVALID_BVCONSTANT:
  case TSTACK_BVARITH_ERROR:
  case TSTACK_BVLOGIC_ERROR:
  case TSTACK_TYPE_ERROR_IN_DEFTERM:
  case SMT2_MISSING_NAME:
  case SMT2_MISSING_PATTERN:
  case SMT2_TYPE_ERROR_IN_QUAL:
  case SMT2_QUAL_NOT_IMPLEMENTED:
    print_out("%s", exception_string[exception]);
    break;

  case TSTACK_YICES_ERROR:
    // TODO: extract mode information from yices_error_report();
    print_out("in %s: ", opcode_string[tstack->error_op]);
    print_yices_error(false);
    break;

  case SMT2_INVALID_IDX_BV:
    print_out("%s", exception_string[exception]);
    break;

  case TSTACK_NO_ERROR:
  case TSTACK_INTERNAL_ERROR:
  case TSTACK_DUPLICATE_SCALAR_NAME:
  case TSTACK_INVALID_OP:
  case TSTACK_NEGATIVE_EXPONENT:
  default:
    print_out("FATAL ERROR");
    close_error();
    report_bug(__smt2_globals.err);
    break;
  }

  close_error();
}


/*
 * OUTPUT/ERROR FILES
 */

/*
 * Close the output file and delete its name
 */
static void close_output_file(smt2_globals_t *g) {
  if (g->out != stdout) {
    assert(g->out_name != NULL);
    if (fclose(g->out) == EOF) {
      failed_output();
    }
    string_decref(g->out_name);
    g->out_name = NULL;
  }
  assert(g->out_name == NULL);
}

/*
 * Same thing for the error file
 */
static void close_error_file(smt2_globals_t *g) {
  if (g->err != stderr) {
    assert(g->err_name != NULL);
    if (fclose(g->err) == EOF) {
      failed_output();
    }
    string_decref(g->err_name);
    g->err_name = NULL;
  }
  assert(g->err_name == NULL);;
}



/*
 * Allocate and initialize the trace object
 */
static tracer_t *get_tracer(smt2_globals_t *g) {
  tracer_t *tmp;

  tmp = g->tracer;
  if (tmp == NULL) {
    tmp = (tracer_t *) safe_malloc(sizeof(tracer_t));
    init_trace(tmp);
    set_trace_vlevel(tmp, g->verbosity);
    set_trace_file(tmp, g->err);
    g->tracer = tmp;
  }
  return tmp;
}


/*
 * Delete the trace object
 */
static void delete_tracer(smt2_globals_t *g) {
  if (g->tracer != NULL) {
    delete_trace(g->tracer);
    safe_free(g->tracer);
    g->tracer = NULL;
  }
}

/*
 * Change the trace file
 */
static void update_trace_file(smt2_globals_t *g) {
  if (g->tracer != NULL) {
    set_trace_file(g->tracer, g->err);
  }
}


/*
 * Change the verbosity level in g->tracer
 */
static void update_trace_verbosity(smt2_globals_t *g) {
  if (g->tracer != NULL) {
    set_trace_vlevel(g->tracer, g->verbosity);
  }
}



/*
 * INFO TABLE
 */

/*
 * Return the table (construct and initialize it if necessary)
 */
static strmap_t *get_info_table(smt2_globals_t *g) {
  strmap_t *hmap;

  hmap = g->info;
  if (hmap == NULL) {
    hmap = (strmap_t *) safe_malloc(sizeof(strmap_t));
    init_strmap(hmap, 0); // default size
    g->info = hmap;
  }

  return hmap;
}


/*
 * For deletion: decrement the reference counter of
 * all avals in the table.
 */
static void info_finalizer(void *aux, strmap_rec_t *r) {
  if (r->val >= 0) {
    aval_decref(aux, r->val);
  }
}

/*
 * Delete the table
 */
static void delete_info_table(smt2_globals_t *g) {
  strmap_t *hmap;

  hmap = g->info;
  if (hmap != NULL) {
    strmap_iterate(hmap, g->avtbl, info_finalizer);
    delete_strmap(hmap);
    safe_free(hmap);
    g->info = NULL;
  }
}


/*
 * Add info: 
 * - name = keyword
 * - val = attribute value (in g->avtbl)
 * - if there's info for name already, we overwrite it
 * - val may be -1 (AVAL_NULL)
 */
static void add_info(smt2_globals_t *g, const char *name, aval_t val) {
  strmap_t *info;
  strmap_rec_t *r;
  bool new;

  info = get_info_table(g);
  r = strmap_get(info, name, &new);
  if (!new && r->val >= 0) {
    aval_decref(g->avtbl, r->val);
  }
  r->val = val;
  if (val >= 0) {
    aval_incref(g->avtbl, val);
  }
}


/*
 * Check whether there's an info record for name
 * - if so return its value in *val and return true
 */
static bool has_info(smt2_globals_t *g, const char *name, aval_t *val) {
  strmap_t *info;
  strmap_rec_t *r;

  info = g->info;
  if (info != NULL) {
    r = strmap_find(info, name);
    if (r != NULL) {
      *val = r->val;
      return true;
    }
  }

  return false;
}



/*
 * SET-OPTION SUPPORT
 */

/*
 * Check whether v is a boolean. 
 * If so copy its value in *result, otherwise leave result unchanged
 */
static bool aval_is_boolean(attr_vtbl_t *avtbl, aval_t v, bool *result) {
  char *s;

  if (v >= 0 && aval_tag(avtbl, v) == ATTR_SYMBOL) {
    s = aval_symbol(avtbl, v);
    if (strcmp(s, "true") == 0) {
      *result = true;
      return true;
    }
    if (strcmp(s, "false") == 0) {
      *result = false;
      return true;
    }
  }

  return false;
}

/*
 * Check whether v is a rational
 * If so copy its value in *result
 */
static bool aval_is_rational(attr_vtbl_t *avtbl, aval_t v, rational_t *result) {
  if (v >= 0 && aval_tag(avtbl, v) == ATTR_RATIONAL) {
    q_set(result, aval_rational(avtbl, v));
    return true;
  }

  return false;
}



/*
 * Boolean option
 * - name = option name (keyword)
 * - value = value given (in g->avtbl)
 * - *flag = where to set the option
 */
static void set_boolean_option(smt2_globals_t *g, const char *name, aval_t value, bool *flag) {
  if (aval_is_boolean(g->avtbl, value, flag)) {
    report_success();
  } else {
    print_error("option %s requires a Boolean value", name);
  }
}


/*
 * Integer option
 * - name = option name
 * - val = value in (g->avtbl)
 * - *result = where to copy the value
 */
static void set_uint32_option(smt2_globals_t *g, const char *name, aval_t value, uint32_t *result) {
  rational_t aux;
  int64_t x;

  q_init(&aux);
  if (aval_is_rational(g->avtbl, value, &aux) && q_is_integer(&aux)) {
    if (q_is_neg(&aux)) {
      print_error("option %s must be non-negative", name);
    } else if (q_get64(&aux, &x) && x <= (int64_t) UINT32_MAX){ 
      assert(x >= 0);
      *result = (uint32_t) x;
      report_success();      
    } else {
      print_error("integer overflow: value must be at most %"PRIu32, UINT32_MAX);
    }
  } else {
    print_error("option %s requires an integer value", name);
  }
  q_clear(&aux);
}


/*
 * Set/change the output channel:
 * - name = keyword (should be :regular-output-channel
 * - val = value (should be a string)
 */
static void set_output_file(smt2_globals_t *g, const char *name, aval_t value) {
  FILE *f;
  char *file_name;

  if (value >= 0 && aval_tag(g->avtbl, value) == ATTR_STRING) {
    file_name = aval_string(g->avtbl, value);
    f = stdout;
    if (strcmp(file_name, "stdout") != 0) {
      f = fopen(file_name, "a"); // append
      if (f == NULL) {
	print_error("can't open file %s", file_name);
	return;
      } 
    }
    close_output_file(g);
    // change out_name
    if (f != stdout) {
      g->out_name = clone_string(file_name);
      string_incref(g->out_name);
    }
    g->out = f;
    report_success();
  } else {
    print_error("option %s requires a string value", name);
  }  
}


/*
 * Set/change the diagnostic channel
 * - name = keyword (should be :regular-output-channel
 * - val = value (should be a string)
 */
static void set_error_file(smt2_globals_t *g, const char *name, aval_t value) {
  FILE *f;
  char *file_name;

  if (value >= 0 && aval_tag(g->avtbl, value) == ATTR_STRING) {
    file_name = aval_string(g->avtbl, value);
    f = stderr;
    if (strcmp(file_name, "stderr") != 0) {
      f = fopen(file_name, "a"); // append
      if (f == NULL) {
	print_error("can't open file %s", file_name);
	return;
      } 
    }
    close_error_file(g);
    // change name
    if (f != stderr) {
      g->err_name = clone_string(file_name);
      string_incref(g->err_name);
    }
    g->err = f;
    update_trace_file(g);
    report_success();
  } else {
    print_error("option %s requires a string value", name);
  }  
}



/*
 * Set the verbosity level
 * - name = keyword (should be :verbosity)
 * - val = value (in g->avtbl)
 */
static void set_verbosity(smt2_globals_t *g, const char *name, aval_t value) {
  rational_t aux;
  int64_t x;

  q_init(&aux);
  if (aval_is_rational(g->avtbl, value, &aux) && q_is_integer(&aux)) {
    if (q_is_neg(&aux)) {
      print_error("option %s must be non-negative", name);
    } else if (q_get64(&aux, &x) && x <= (int64_t) UINT32_MAX) {
      /*
       * x = verbosity level
       */
      g->verbosity = (uint32_t) x;
      update_trace_verbosity(g);
      report_success();
    } else {
      print_error("integer overflow: %s must be at most %"PRIu32, UINT32_MAX);
    }
  } else {
    print_error("option %s requires an integer value", name);
  }
  q_clear(&aux);
}



/*
 * OUTPUT OF INFO AND OPTIONS
 */

/*
 * Print pair (keyword, value) 
 */
static void print_kw_string_pair(const char *keyword, const char *value) {
  print_out("(%s \"%s\")\n", keyword, value);  
}

static void print_kw_symbol_pair(const char *keyword, const char *value) {
  print_out("(%s %s)\n", keyword, value);
}

static const char * const string_bool[2] = { "false", "true" };

static void print_kw_boolean_pair(const char *keyword, bool value) {
  print_kw_symbol_pair(keyword, string_bool[value]);
}

static void print_kw_uint32_pair(const char *keyword, uint32_t value) {
  print_out("(%s %"PRIu32")\n", keyword, value);
}


/*
 * Print attribute values
 */
static void print_aval(smt2_globals_t *g, aval_t val); 

static void print_aval_list(smt2_globals_t *g, attr_list_t *d) {
  uint32_t i, n;

  n = d->nelems;
  assert(n > 0);
  print_out("(");
  print_aval(g, d->data[0]);
  for (i=1; i<n; i++) {
    print_out(" ");
    print_aval(g, d->data[i]);
  }
  print_out(")");
}

/*
 * We can't use bvconst_print here because it uses prefix 0b
 */
static void print_aval_bv(smt2_globals_t *q, bvconst_attr_t *bv) {
  uint32_t n;

  n = bv->nbits;
  assert(n > 0);
  print_out("#b");
  do {
    n --;
    print_out("%u", (unsigned) bvconst_tst_bit(bv->data, n));
  } while (n > 0);
}

static void print_aval_rational(smt2_globals_t *g, rational_t *q) {
  q_print(g->out, q);
  if (ferror(g->out)) {
    failed_output();
  }
}

static void print_aval(smt2_globals_t *g, aval_t val) {
  assert(good_aval(g->avtbl, val));
  switch (aval_tag(g->avtbl, val)) {
  case ATTR_RATIONAL:
    print_aval_rational(g, aval_rational(g->avtbl, val));
    break;

  case ATTR_BV:
    print_aval_bv(g, aval_bvconst(g->avtbl, val));
    break;

  case ATTR_STRING:
    print_out("\"%s\"", aval_string(g->avtbl, val));
    break;

  case ATTR_SYMBOL:
    print_out("%s", aval_symbol(g->avtbl, val));
    break;

  case ATTR_LIST:
    print_aval_list(g, aval_list(g->avtbl, val));
    break;

  case ATTR_DELETED:
    report_bug(g->err);
    break;    
  }
}

/*
 * Print pair keyword/val
 */
static void print_kw_value_pair(smt2_globals_t *g, const char *name, aval_t val) {
  if (val < 0) {
    print_out("(%s)\n", name);
  } else {
    print_out("(%s ", name);
    print_aval(g, val);
    print_out(")\n");
  }
}



/*
 * Check whether the logic is set
 * - if not print an error
 */
static bool check_logic(void) {
  if (__smt2_globals.logic_code == SMT_UNKNOWN) {
    print_error("no logic set");
    return false;
  }
  return true;
}


/*
 * Converse: make sure that no logic is set
 * - if it is, print (error "...") and return false
 */
static bool option_can_be_set(const char *option_name) {
  if (__smt2_globals.logic_code != SMT_UNKNOWN) {
    print_error("option %s can't be set now. It must be set before (set-logic ...)", option_name);
    return false;
  }
  return true;
}


/*
 * CONTEXT INITIALIZATION
 */

/*
 * Conversion of SMT logic code to architecture code
 * -1 means not supported
 */
static const int32_t logic2arch[NUM_SMT_LOGICS] = {
  -1,                  // NONE: not a real SMT logic (treat as unsupported)
  -1,                  // AUFLIA
  -1,                  // AUFLIRA
  -1,                  // AUFNIRA
  -1,                  // LRA
  CTX_ARCH_EGFUNBV,    // QF_ABV
  CTX_ARCH_EGFUNBV,    // QF_AUFBV
  CTX_ARCH_EGFUNSPLX,  // QF_AUFLIA
  CTX_ARCH_EGFUN,      // QF_AX
  CTX_ARCH_BV,         // QF_BV
  CTX_ARCH_AUTO_IDL,   // QF_IDL
  CTX_ARCH_SPLX,       // QF_LIA
  CTX_ARCH_SPLX,       // QF_LRA
  -1,                  // QF_NIA
  -1,                  // QF_NRA
  CTX_ARCH_AUTO_RDL,   // QF_RDL
  CTX_ARCH_EG,         // QF_UF
  CTX_ARCH_EGBV,       // QF_UFBV[xx]
  CTX_ARCH_EGSPLX,     // QF_UFIDL
  CTX_ARCH_EGSPLX,     // QF_UFLIA
  CTX_ARCH_EGSPLX,     // QF_UFLRA
  -1,                  // QF_UFNRA
  -1,                  // UFLRA
  -1,                  // UFNIA
};

/*
 * Specify whether the integer solver should be activated
 */
static const bool logic2iflag[NUM_SMT_LOGICS] = {
  false,  // NONE
  true,   // AUFLIA
  true,   // AUFLIRA
  true,   // AUFNIRA
  false,  // LRA
  false,  // QF_ABV
  false,  // QF_AUFBV
  true,   // QF_AUFLIA
  false,  // QF_AX
  false,  // QF_BV
  false,  // QF_IDL
  true,   // QF_LIA
  false,  // QF_LRA
  true,   // QF_NIA
  false,  // QF_NRA
  false,  // QF_RDL
  false,  // QF_UF
  false,  // QF_UFBV[x]
  false,  // QF_UFIDL
  true,   // QF_UFLIA
  false,  // QF_UFLRA
  false,  // QF_UFNRA
  false,  // UFLRA
  true,   // UFNIA
};


/*
 * Specify whether quantifier support is needed
 */
static const bool logic2qflag[NUM_SMT_LOGICS] = {
  false,  // NONE
  true,   // AUFLIA
  true,   // AUFLIRA
  true,   // AUFNIRA
  true,   // LRA
  false,  // QF_ABV
  false,  // QF_AUFBV
  false,  // QF_AUFLIA
  false,  // QF_AX
  false,  // QF_BV
  false,  // QF_IDL
  false,  // QF_LIA
  false,  // QF_LRA
  false,  // QF_NIA
  false,  // QF_NRA
  false,  // QF_RDL
  false,  // QF_UF
  false,  // QF_UFBV[x]
  false,  // QF_UFIDL
  false,  // QF_UFLIA
  false,  // QF_UFLRA
  false,  // QF_UFNRA
  true,   // UFLRA
  true,   // UFNIA
};


/*
 * Allocate and initialize the context based on g->logic
 * - also initialize the global parameter table
 * - make sure the logic is supported before calling this
 */
static void init_smt2_context(smt2_globals_t *g) {
  context_arch_t arch;
  context_mode_t mode;
  bool iflag;
  bool qflag;

  assert(logic2arch[g->logic_code] >= 0);

  // default: assume g->benchmark is true
  mode = CTX_MODE_ONECHECK;
  arch = (context_arch_t) logic2arch[g->logic_code];
  iflag = logic2iflag[g->logic_code];
  qflag = logic2qflag[g->logic_code];

  if (! g->benchmark) {
    // change mode and arch 
    // to support push/pop, we can't use the Floyd-Warshall solver
    mode = CTX_MODE_PUSHPOP;
    if (arch == CTX_ARCH_AUTO_RDL || arch == CTX_ARCH_AUTO_IDL) {
      arch = CTX_ARCH_SPLX;
    }
  }

  g->ctx = yices_create_context(arch, mode, iflag, qflag);
  yices_set_default_params(g->ctx, &parameters);
  assert(g->ctx != NULL);
  if (g->verbosity > 0) {
    context_set_trace(g->ctx, get_tracer(g));
  }
}



/*
 * DELAYED ASSERTION/CHECK_SAT
 */

/*
 * Check whether term t requires the Egraph
 * - seen = hset of all terms seen so far (none of them requires the Egraph)
 */
static bool needs_egraph(int_hset_t *seen, term_t t);

static bool composite_needs_egraph(int_hset_t *seen, composite_term_t *d) {
  uint32_t i, n;

  n = d->arity;
  for (i=0; i<n; i++) {
    if (needs_egraph(seen, d->arg[i])) return true;
  }
  return false;
}

static bool product_needs_egraph(int_hset_t *seen, pprod_t *p) {
  uint32_t i, n;

  n = p->len;
  for (i=0; i<n; i++) {
    if (needs_egraph(seen, p->prod[i].var)) return true;
  }
  return false;
}

static bool poly_needs_egraph(int_hset_t *seen, polynomial_t *p) {
  uint32_t i, n;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) {
    i ++;
  }
  while (i < n) {
    if (needs_egraph(seen, p->mono[i].var)) return true;
    i ++;
  }
  return false;
}

static bool bvpoly64_needs_egraph(int_hset_t *seen, bvpoly64_t *p) {
  uint32_t i, n;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) {
    i ++;
  }
  while (i < n) {
    if (needs_egraph(seen, p->mono[i].var)) return true;
    i ++;
  }
  return false;
}

static bool bvpoly_needs_egraph(int_hset_t *seen, bvpoly_t *p) {
  uint32_t i, n;

  n = p->nterms;
  i = 0;
  if (p->mono[0].var == const_idx) {
    i ++;
  }
  while (i < n) {
    if (needs_egraph(seen, p->mono[i].var)) return true;
    i ++;
  }
  return false;
}



static bool needs_egraph(int_hset_t *seen, term_t t) {
  term_table_t *terms;
  bool result;

  result = false;
  t = unsigned_term(t); // clear polarity
  if (int_hset_add(seen, t)) {
    // not seen yet
    terms = __yices_globals.terms;
    switch (term_kind(terms, t)) {
    case UNUSED_TERM:
    case RESERVED_TERM:
      assert(false);
      break;

    case CONSTANT_TERM:
    case VARIABLE:
    case UNINTERPRETED_TERM:
      result = is_utype_term(terms, t);
      break;

    case ARITH_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
      result = false;
      break;

    case ARITH_EQ_ATOM:
    case ARITH_GE_ATOM:
      result = needs_egraph(seen, arith_atom_arg(terms, t));
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
    case EQ_TERM:
    case DISTINCT_TERM:
    case OR_TERM:
    case XOR_TERM:
    case ARITH_BINEQ_ATOM:
    case BV_ARRAY:
    case BV_DIV:
    case BV_REM:
    case BV_SDIV:
    case BV_SREM:
    case BV_SMOD:
    case BV_SHL:
    case BV_LSHR:
    case BV_ASHR:
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM:
      result = composite_needs_egraph(seen, composite_term_desc(terms, t));
      break;

    case BIT_TERM:
      result = needs_egraph(seen, bit_term_arg(terms, t));
      break;

    case APP_TERM:
    case UPDATE_TERM:
    case TUPLE_TERM:
    case FORALL_TERM:
    case LAMBDA_TERM:
    case SELECT_TERM:
      result = true;
      break;

    case POWER_PRODUCT:
      result = product_needs_egraph(seen, pprod_term_desc(terms, t));
      break;

    case ARITH_POLY:
      result = poly_needs_egraph(seen, poly_term_desc(terms, t));
      break;

    case BV64_POLY:
      result = bvpoly64_needs_egraph(seen, bvpoly64_term_desc(terms, t));
      break;

    case BV_POLY:
      result = bvpoly_needs_egraph(seen, bvpoly_term_desc(terms, t));
      break;
    }
  }

  return result;
}

/*
 * Check whether any formula is a[0...n-1] contains an uninterpreted function
 */
static bool has_uf(term_t *a, uint32_t n) {
  int_hset_t seen; // set of visited terms
  bool result;
  uint32_t i;

  result = false;
  init_int_hset(&seen, 32);
  for (i=0; i<n; i++) {
    result = needs_egraph(&seen, a[i]);
    if (result) break;
  }
  delete_int_hset(&seen);

  return result;
}

/*
 * Add a assertion t to g->assertions
 * - do nothing if t is true
 * - if t is false, set g->trivially_unsat to true
 */
static void add_assertion(smt2_globals_t *g, term_t t) {
  if (t != true_term) {
    ivector_push(&g->assertions, t);
    if (t == false_term) {
      g->trivially_unsat = true;
    }
  }
}


/*
 * Check satisfiability of all assertions
 */
static void check_assertions(smt2_globals_t *g) {
  int32_t code;
  smt_status_t status;

  if (g->trivially_unsat) {
    print_out("unsat\n");
  } else if (g->assertions.size == 0) {
    print_out("sat\n");
  } else {
    /*
     * check for mislabeled benchmarks: some benchmarks 
     * marked as QF_UFIDL do not require the Egraph (should be QF_IDL)
     */
    if (g->benchmark && g->logic_code == QF_UFIDL && 
	!has_uf(g->assertions.data, g->assertions.size)) {
      fprintf(g->err, "Warning: switching logic to QF_IDL\n");
      g->logic_code = QF_IDL;
    }
    init_smt2_context(g);
    code = yices_assert_formulas(g->ctx, g->assertions.size, g->assertions.data);
    if (code < 0) {
      // error during assertions
      print_yices_error(true);
      return;
    }
    status = yices_check_context(g->ctx, NULL);
    switch (status) {
    case STATUS_IDLE:
    case STATUS_SEARCHING:
      print_error("Unexpected context status");
      report_bug(g->err);
      break;

    case STATUS_SAT:
      print_out("sat\n");
      break;

    case STATUS_UNSAT:
      print_out("unsat\n");
      break;

    case STATUS_UNKNOWN:
    case STATUS_INTERRUPTED:
      print_out("unknown\n");
      break;

    case STATUS_ERROR:
      print_yices_error(true);
      break;
    }
  }
  flush_out();
}




/*
 * MAIN CONTROL FUNCTIONS
 */

/*
 * Initialize g to defaults
 */
static void init_smt2_globals(smt2_globals_t *g) {
  g->logic_code = SMT_UNKNOWN;
  g->benchmark = false;
  g->logic_name = NULL;
  g->out = stdout;
  g->err = stderr;
  g->out_name = NULL;
  g->err_name = NULL;
  g->tracer = NULL;
  g->print_success = true;
  g->expand_definitions = false;
  g->interactive_mode = false;
  g->produce_proofs = false;
  g->produce_unsat_cores = false;
  g->produce_models = false;
  g->produce_assignments = false;
  g->random_seed = 0;
  g->verbosity = 0;
  g->avtbl = NULL;
  g->info = NULL;
  g->ctx = NULL;
  g->model = NULL;

  init_smt2_stack(&g->stack);
  init_smt2_name_stack(&g->term_names);
  init_smt2_name_stack(&g->type_names);
  init_smt2_name_stack(&g->macro_names);

  init_ivector(&g->assertions, 0);
  g->trivially_unsat = false;
  g->frozen = false;
}


/*
 * Cleanup: close out and err if different from the defaults
 * - delete all internal structures (except avtbl)
 */
static void delete_smt2_globals(smt2_globals_t *g) {
  delete_info_table(g);
  if (g->logic_name != NULL) {
    string_decref(g->logic_name);
    g->logic_name = NULL;
  }
  if (g->ctx != NULL) {
    yices_free_context(g->ctx);
    g->ctx = NULL;
  }
  if (g->model != NULL) {
    yices_free_model(g->model);
    g->model = NULL;
  }
  delete_ivector(&g->assertions);

  delete_smt2_stack(&g->stack);
  delete_smt2_name_stack(&g->term_names);
  delete_smt2_name_stack(&g->type_names);
  delete_smt2_name_stack(&g->macro_names);

  close_output_file(g);
  close_error_file(g);
  delete_tracer(g);
}


/*
 * Initialize all internal structures
 * - benchmark: if true, the input is assumed to be an SMT-LIB 2.0 benchmark
 *  (i.e., a set of assertions followed by a single call to check-sat)
 *  In this mode, destructive simplifications are allowed.
 * - this is called after yices_init so all Yices internals are ready
 */
void init_smt2(bool benchmark) {
  done = false;
  init_smt2_globals(&__smt2_globals);
  init_attr_vtbl(&avtbl);
  __smt2_globals.benchmark = benchmark;
  __smt2_globals.avtbl = &avtbl;
}


/*
 * Delete all structures and close output/trace files
 */
void delete_smt2(void) {
  delete_smt2_globals(&__smt2_globals);
  delete_attr_vtbl(&avtbl); // must be done last
}


/*
 * Check whether the smt2 solver is ready
 * - this must be true after init_smt2()
 * - this must return false if smt2_exit has been called or after
 *   an unrecoverable error
 */
bool smt2_active(void) {
  return !done;
}


/*
 * TOP-LEVEL SMT2 COMMANDS
 */

/*
 * Exit function
 */
void smt2_exit(void) {
  done = true;
  report_success();
}


/*
 * Variant: for end-of-file
 */
void smt2_silent_exit(void) {
  done = true;
}


/*
 * Show all formulas asserted so far
 */
void smt2_get_assertions(void) {
  if (check_logic()) {
    print_out("get_assertions: unsupported\n");
    flush_out();
  }
}


/*
 * Show the truth value of named Boolean terms 
 * (i.e., those that have a :named attribute)
 */
void smt2_get_assignment(void) {
  if (check_logic()) {
    print_out("get_assignment: unsupported\n");  
    flush_out();
  }
}


/*
 * Show a proof when context is unsat
 */
void smt2_get_proof(void) {
  if (check_logic()) { 
    print_out("get_proof: unsupported\n");
    flush_out();
  }
}


/*
 * Get the unsat core: subset of :named assertions that form an unsat core
 */
void smt2_get_unsat_core(void) {
  if (check_logic()) {
    print_out("get_unsat_core: unsupported\n");  
    flush_out();
  }
}


/*
 * Get the values of terms in the model
 * - the terms are listed in array a
 * - n = number of elements in the array
 */
void smt2_get_value(term_t *a, uint32_t n) {
  if (check_logic()) {
    print_out("get_value: unsupported\n");  
    flush_out();
  }
}


/*
 * Get the value of an option
 * - name = option name (a keyword)
 */
void smt2_get_option(const char *name) {
  smt2_globals_t *g;
  char *s;
  smt2_keyword_t kw;
  uint32_t n;

  g = &__smt2_globals;
  n = strlen(name);
  kw = smt2_string_to_keyword(name, n);
  switch (kw) {
  case SMT2_KW_PRINT_SUCCESS:
    print_kw_boolean_pair(name, g->print_success);
    break;
    
  case SMT2_KW_EXPAND_DEFINITIONS:
    print_kw_boolean_pair(name, g->expand_definitions);
    break;
    
  case SMT2_KW_INTERACTIVE_MODE:
    print_kw_boolean_pair(name, g->interactive_mode);
    break;
    
  case SMT2_KW_PRODUCE_PROOFS:
    print_kw_boolean_pair(name, g->produce_proofs);
    break;

  case SMT2_KW_PRODUCE_UNSAT_CORES:
    print_kw_boolean_pair(name, g->produce_unsat_cores);
    break;

  case SMT2_KW_PRODUCE_MODELS: 
    print_kw_boolean_pair(name, g->produce_models);
    break;

  case SMT2_KW_PRODUCE_ASSIGNMENTS:
    print_kw_boolean_pair(name, g->produce_assignments);
    break;

  case SMT2_KW_REGULAR_OUTPUT:
    s = g->out_name;
    if (s == NULL) {
      assert(g->out == stdout);
      s = "stdout";
    }
    print_kw_string_pair(name, s);
    break;

  case SMT2_KW_DIAGNOSTIC_OUTPUT:
    s = g->err_name;
    if (s == NULL) {
      assert(g->err == stderr);
      s = "stderr";
    }
    print_kw_string_pair(name, s);
    break;

  case SMT2_KW_RANDOM_SEED:
    print_kw_uint32_pair(name, g->random_seed);
    break;

  case SMT2_KW_VERBOSITY:
    print_kw_uint32_pair(name, g->verbosity);
    break;

  default:
    print_out("unsupported\n");
    break;   
  }
}


/*
 * Get some info
 * - name = keyword
 */
void smt2_get_info(const char *name) {
  smt2_globals_t *g;
  smt2_keyword_t kw;
  uint32_t n;
  aval_t value;

  n = strlen(name);
  kw = smt2_string_to_keyword(name, n);
  switch (kw) {
  case SMT2_KW_ERROR_BEHAVIOR:
    print_kw_symbol_pair(name, error_behavior);
    report_success();
    break;

  case SMT2_KW_NAME:
    print_kw_string_pair(name, yices_name);
    report_success();
    break;

  case SMT2_KW_AUTHORS:
    print_kw_string_pair(name, yices_authors);
    report_success();
    break;

  case SMT2_KW_VERSION:
    print_kw_string_pair(name, yices_version);
    report_success();
    break;

  case SMT2_KW_REASON_UNKNOWN:
  case SMT2_KW_ALL_STATISTICS:
    // TBD
    print_out("unsupported\n");
    break;

  default:
    g = &__smt2_globals;
    if (has_info(g, name, &value)) {
      print_kw_value_pair(g, name, value);
      report_success();
    } else {
      print_error("no info for %s", name);
    }
    break;
  }
}


/*
 * Set an option:
 * - name = option name (keyword)
 * - value = value (stored in the attribute_value table)
 *
 * SMT2 allows the syntax (set-option :keyword). In such a case,
 * this function is called with value = NULL_VALUE (i.e., -1).
 */
void smt2_set_option(const char *name, aval_t value) {
  smt2_globals_t *g;
  smt2_keyword_t kw;
  uint32_t n;

  g = &__smt2_globals;
  n = strlen(name);
  kw = smt2_string_to_keyword(name, n);

  switch (kw) {
  case SMT2_KW_PRINT_SUCCESS:
    // required
    set_boolean_option(g, name, value, &g->print_success);
    break;

  case SMT2_KW_EXPAND_DEFINITIONS:
    // optional: influence term printing (we ignore it)
    set_boolean_option(g, name, value, &g->expand_definitions);
    break;

  case SMT2_KW_INTERACTIVE_MODE:
    // optional: if true, get-assertions can be used
    if (option_can_be_set(name)) {
      set_boolean_option(g, name, value, &g->interactive_mode);
    }
    break;

  case SMT2_KW_PRODUCE_PROOFS:
    // optional: if true, get-proof can be used
    if (option_can_be_set(name)) {
      set_boolean_option(g, name, value, &g->produce_proofs);
    }
    break;

  case SMT2_KW_PRODUCE_UNSAT_CORES:
    // optional: if true, get-unsat-core can be used
    if (option_can_be_set(name)) {
      set_boolean_option(g, name, value, &g->produce_unsat_cores);
    }
    break;

  case SMT2_KW_PRODUCE_MODELS:
    // optional: if true, get-value can be used
    if (option_can_be_set(name)) {
      set_boolean_option(g, name, value, &g->produce_models);
    }
    break;

  case SMT2_KW_PRODUCE_ASSIGNMENTS:
    // optional: if true, get-assignment can be used
    if (option_can_be_set(name)) {
      set_boolean_option(g, name, value, &g->produce_assignments);
    }
    break;

  case SMT2_KW_REGULAR_OUTPUT:
    // required
    set_output_file(g, name, value);
    break;

  case SMT2_KW_DIAGNOSTIC_OUTPUT:
    // required
    set_error_file(g, name, value);
    break;

  case SMT2_KW_RANDOM_SEED:
    // optional
    set_uint32_option(g, name, value, &g->random_seed);
    break;

  case SMT2_KW_VERBOSITY:
    // optional
    set_verbosity(g, name, value);
    break;

  default:
    print_out("unsupported\n");
    break;
  }
}


/*
 * Set some info field
 * - same conventions as set_option
 */
void smt2_set_info(const char *name, aval_t value) {
  smt2_keyword_t kw;
  uint32_t n;

  n = strlen(name);
  kw = smt2_string_to_keyword(name, n);
  switch (kw) {
  case SMT2_KW_ERROR_BEHAVIOR:
  case SMT2_KW_NAME:
  case SMT2_KW_AUTHORS:
  case SMT2_KW_VERSION:
  case SMT2_KW_REASON_UNKNOWN:
  case SMT2_KW_ALL_STATISTICS:
    print_error("can't overwrite %s", name);
    break;

  default:
    add_info(&__smt2_globals, name, value);
    report_success();
    break;
  }
}


/*
 * Set the logic:
 * - name = logic name (using the SMT-LIB conventions)
 */
void smt2_set_logic(const char *name) {
  smt_logic_t code;

  if (__smt2_globals.logic_code != SMT_UNKNOWN) {
    print_error("the logic is already set");
    return;
  }

  code = smt_logic_code(name);
  if (code == SMT_UNKNOWN) {
    print_error("unknown logic: %s", name);
    return;
  }

  if (logic2arch[code] < 0) {
    print_error("logic %s is not supported", name);
    return;
  }

  smt2_lexer_activate_logic(code);
  __smt2_globals.logic_code = code;
  __smt2_globals.logic_name = clone_string(name);
  string_incref(__smt2_globals.logic_name);
  report_success();
}


/*
 * Push 
 * - n = number of scopes to push
 * - if n = 0, nothing should be done
 */
void smt2_push(uint32_t n) {
  if (check_logic()) {
    print_out("push: unsupported\n");
    flush_out();
  }
}


/*
 * Pop:
 * - n = number of scopes to remove
 * - if n = 0 nothing should be done
 * - if n > total number of scopes then an error should be printed
 *   and nothing done
 */
void smt2_pop(uint32_t n) {
  if (check_logic()) {
    print_out("pop: unsupported\n");
    flush_out();
  }
}


/*
 * Assert one formula t
 * - if t is a :named assertion then it should be recorded for unsat-core
 */
void smt2_assert(term_t t) {
  if (check_logic()) {
    if (yices_term_is_bool(t)) {
      if (__smt2_globals.benchmark) {
	// delayed assertion
	add_assertion(&__smt2_globals, t);
	report_success();
      } else {
	// TBD
	print_out("assert: not supported\n");
	flush_out();
      }
    } else {
      // not a Boolean term
      print_error("type error in assert: Boolean term required");
    }
  }
}


/*
 * Check satisfiability of the current set of assertions
 */
void smt2_check_sat(void) {
  if (check_logic()) {
    if (__smt2_globals.benchmark) {
      check_assertions(&__smt2_globals);
    } else {
      print_out("check_sat: unsupported\n");
      flush_out();
    }
  }
}


/*
 * Declare a new sort:
 * - name = sort name
 * - arity = arity
 *
 * If arity is 0, this defines a new uninterpreted type.
 * Otherwise, this defines a new type constructor.
 */
void smt2_declare_sort(const char *name, uint32_t arity) {
  type_t tau;
  int32_t macro;

  if (check_logic()) {
    if (arity == 0) {
      tau = yices_new_uninterpreted_type();
      yices_set_type_name(tau, name);
      report_success();
    } else {
      macro = yices_type_constructor(name, arity);
      if (macro < 0) {
	print_yices_error(true);
      } else {
	report_success();
      }
    }
  }

}


/*
 * Define a new type macro
 * - name = macro name
 * - n = number of variables
 * - var = array of type variables
 * - body = type expressions
 */
void smt2_define_sort(const char *name, uint32_t n, type_t *var, type_t body) {
  int32_t macro;

  if (check_logic()) {
    if (n == 0) {
      yices_set_type_name(body, name);
      report_success();      
    } else {
      macro = yices_type_macro(name, n, var, body);
      if (macro < 0) {
	print_yices_error(true);
      } else {
	report_success();
      }
    }
  }
}


/*
 * Declare a new uninterpreted function symbol
 * - name = function name
 * - n = arity + 1
 * - tau = array of n types
 *
 * If n = 1, this creates an uninterpreted constant of type tau[0]
 * Otherwise, this creates an uninterpreted function of type tau[0] x ... x tau[n-1] to tau[n] 
 */
void smt2_declare_fun(const char *name, uint32_t n, type_t *tau) {
  term_t t;
  type_t sigma;

  assert(n > 0);

  if (check_logic()) {
    n --;
    sigma = tau[n]; // range
    if (n > 0) {
      sigma = yices_function_type(n, tau, sigma);
    }
    assert(sigma != NULL_TYPE);

    t = yices_new_uninterpreted_term(sigma);
    assert(t != NULL_TERM);
    yices_set_term_name(t, name);

    report_success();
  }
}


/*
 * Define a function
 * - name = function name
 * - n = arity
 * - var = array of n term variables
 * - body = term
 * - tau = expected type of body
 *
 * If n = 0, this is the same as (define <name> :: <type> <body> )
 * Otherwise, a lambda term is created.
 */
void smt2_define_fun(const char *name, uint32_t n, term_t *var, term_t body, type_t tau) {
  term_t t;

  if (check_logic()) {
    if (! yices_check_term_type(body, tau)) {
      // ? print a better error message?
      print_yices_error(true);
      return;
    }

    t = body;
    if (n > 0) {
      t = yices_lambda(n, var, t);
      if (t < 0) {
	print_yices_error(true);
	return;
      }
    }
    yices_set_term_name(t, name);

    report_success();
  }
}



/*
 * ATTRIBUTES
 */

/*
 * Add a :named attribute to term t
 */
void smt2_add_name(term_t t, const char *name) {
  // TBD
}


/*
 * Add a :pattern attribute to term t
 * - the pattern is an array p of n terms
 */
void smt2_add_pattern(term_t t, term_t *p, uint32_t n) {
  // TBD
}
