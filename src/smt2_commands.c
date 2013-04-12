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
  fprintf(f, "FATAL ERROR\n\n");
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
 *   on the current output channnel
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
    print_out("maximal polynomial degree exceeeded");
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
    print_out("type error: invalid arguments");
    break;
  case INCOMPATIBLE_TYPES:
    print_out("incomaptible types");
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
  "undefinedd term",                    // TSTACK_UNDEF_TERM
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
  "expponetiation",       // MK_POW
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
  "bvsrme",               // MK_BV_SREM
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
  "sign_extenrd",         // MK_BV_SIGN_EXTEND
  "zero_extend",          // MK_BV_ZERO_EXTEND
  "bvredand",             // MK_BV_REDAND (not in SMT2)
  "bvredor",              // MK_BV_REDOR (not in SMT2)
  "bvomp",                // MK_BV_COMP
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
  "get_unsat_CORE",       // SMT2_GET_UNSAT_CORE
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
  "as",                   // SMT2_SORTED_TERM
  "as",                   // SMT2_SORTED_INDEXED_TERM
  "function application", // SMT2_INDEXED_APPLY
  "function application", // SMT2_SORTED_APPLY
  "function application", // SMT2_SORTED_INDEXED_APPLY
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
 * INFO TABLE
 */

/*
 * Return the table (construct and initialize it if necessary)
 */
static strmap_t *get_info_table(smt2_globals_t *g) {
  strmap_t *hmap;

  hmap = g->info;
  if (hmap == NULL) {
    hmap = (strmap_t *) safe_malloc(sizeof(smt2_globals_t));
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
 * If so copy its value in *resul, otherwise leave result unchanged
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
 * - *result = wher to copy the value
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
 * Set/change the dianostic channel
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
    report_success();
  } else {
    print_error("option %s requires a string value", name);
  }  
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
 * General case: val is an attribute value in g->avbtl
 */
static void print_kw_value_pair(smt2_globals_t *g, const char *name, aval_t val) {
  attr_vtbl_t *avtbl;
  bvconst_attr_t *bv;

  if (val < 0) {
    print_out("(%s)\n", name);
  } else {
    avtbl = g->avtbl;
    switch (aval_tag(avtbl, val)) {
    case ATTR_RATIONAL:
      print_out("(%s ", name);
      q_print(g->out, aval_rational(avtbl, val));
      print_out(")\n");
      break;

    case ATTR_BV:
      bv = aval_bvconst(avtbl, val);
      print_out("(%s ", name);
      bvconst_print(g->out, bv->data, bv->nbits);
      print_out(")\n");
      break;

    case ATTR_STRING:
      print_kw_string_pair(name, aval_string(avtbl, val));
      break;

    case ATTR_SYMBOL:
      print_kw_symbol_pair(name, aval_symbol(avtbl, val));
      break;

    case ATTR_LIST:
      // TBD
      print_out("(%s (...))\n");
      break;

    case ATTR_DELETED:
      report_bug(__smt2_globals.err);
      break;
    }
  }
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
}


/*
 * Cleanup: close out and err if different from the defaults
 * - delete all internal structures (except avtbl)
 */
static void delete_smt2_globals(smt2_globals_t *g) {
  delete_info_table(g);
  if (g->ctx != NULL) {
    yices_free_context(g->ctx);
    g->ctx = NULL;
  }
  if (g->model != NULL) {
    yices_free_model(g->model);
    g->model = NULL;
  }
  close_output_file(g);
  close_error_file(g);
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
  print_out("get_assertions: unsupported\n");
  flush_out();
}


/*
 * Show the truth value of named Boolean terms 
 * (i.e., those that have a :named attribute)
 */
void smt2_get_assignment(void) {
  print_out("get_assignment: unsupported\n");  
  flush_out();
}


/*
 * Show a proof when context is unsat
 */
void smt2_get_proof(void) {
  print_out("get_proof: unsupported\n");
  flush_out();  
}


/*
 * Get the unsat core: subset of :named assertions that form an unsat core
 */
void smt2_get_unsat_core(void) {
  print_out("get_unsat_core: unsupported\n");  
  flush_out();  
}


/*
 * Get the values of terms in the model
 * - the terms are listed in array a
 * - n = number of elements in the array
 */
void smt2_get_value(term_t *a, uint32_t n) {
  print_out("get_value: unsupported\n");  
  flush_out();  
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
    set_boolean_option(g, name, value, &g->print_success);
    break;

  case SMT2_KW_EXPAND_DEFINITIONS:
    set_boolean_option(g, name, value, &g->expand_definitions);
    break;

  case SMT2_KW_INTERACTIVE_MODE:
    set_boolean_option(g, name, value, &g->interactive_mode);
    break;

  case SMT2_KW_PRODUCE_PROOFS:
    set_boolean_option(g, name, value, &g->produce_proofs);
    break;

  case SMT2_KW_PRODUCE_UNSAT_CORES:
    set_boolean_option(g, name, value, &g->produce_unsat_cores);
    break;

  case SMT2_KW_PRODUCE_MODELS:
    set_boolean_option(g, name, value, &g->produce_models);
    break;

  case SMT2_KW_PRODUCE_ASSIGNMENTS:
    set_boolean_option(g, name, value, &g->produce_assignments);
    break;

  case SMT2_KW_REGULAR_OUTPUT:
    set_output_file(g, name, value);
    break;

  case SMT2_KW_DIAGNOSTIC_OUTPUT:
    set_error_file(g, name, value);
    break;

  case SMT2_KW_RANDOM_SEED:
    set_uint32_option(g, name, value, &g->random_seed);
    break;

  case SMT2_KW_VERBOSITY:
    set_uint32_option(g, name, value, &g->verbosity);
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
    print_error("the logic is alreay set");
    return;
  }

  code = smt_logic_code(name);
  if (code == SMT_UNKNOWN) {
    print_error("unknown logic: %s", name);
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
  print_out("push: unsupported\n");
  flush_out();  
}


/*
 * Pop:
 * - n = number of scopes to remove
 * - if n = 0 nothing should be done
 * - if n > total number of scopes then an error should be printed
 *   and nothing done
 */
void smt2_pop(uint32_t n) {
  print_out("pop: unsupported\n");
  flush_out();
}


/*
 * Assert one formula t
 * - if t is a :named assertion then it should be recorded for unsat-core
 */
void smt2_assert(term_t t) {
  print_out("assert: unsupported\n");
  flush_out();
}


/*
 * Check satsifiability of the current set of assertions
 */
void smt2_check_sat(void) {
  print_out("check_sat: unsupported\n");
  flush_out();
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


/*
 * Define a new type macro
 * - name = macro name
 * - n = number of variables
 * - var = array of type variables
 * - body = type expressions
 */
void smt2_define_sort(const char *name, uint32_t n, type_t *var, type_t body) {
  int32_t macro;

  macro = yices_type_macro(name, n, var, body);
  if (macro < 0) {
    print_yices_error(true);
  } else {
    report_success();
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

  if (! yices_check_term_type(body, tau)) {
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
 * - the pattern is a term p
 */
void smt2_add_pattern(term_t t, term_t p) {
  // TBD
}
