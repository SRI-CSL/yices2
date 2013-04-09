/*
 * ALL SMT-LIB 2 COMMANDS
 */

#include <stdio.h>
#include <inttypes.h>
#include <assert.h>

#include "attribute_values.h"
#include "smt_logic_codes.h"
#include "smt2_lexer.h"
#include "smt2_commands.h"

/*
 * GLOBAL OBJECTS
 */
static FILE *err;     // error/trace output: default = stderr
static FILE *out;     // normal output: default = stdout

static char *logic_name;           // logic: initially NULL
static smt_logic_t logic_code;     // code: set after logic_name is given

static bool done;    // set to true on exit

static attr_vtbl_t avtbl; // attribute values


/*
 * ERROR REPORTS
 */

static inline char *tkval(lexer_t *lex) {
  return current_token_value(lex);
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
void smt2_syntax_error(lexer_t *lex, int32_t expected_token) {
  reader_t *rd;
  smt2_token_t tk;

  tk = current_token(lex);
  rd = &lex->reader;

  fprintf(out, "(error on line %"PRId32", column %"PRId32": ", rd->line, rd->column);

  switch (tk) {
  case SMT2_TK_INVALID_STRING:
    fprintf(out, "missing string terminator");
    break;

  case SMT2_TK_INVALID_NUMERAL:
    fprintf(out, "invalid numeral %s", tkval(lex));
    break;

  case SMT2_TK_INVALID_DECIMAL:
    fprintf(out, "invalid decimal %s", tkval(lex));
    break;

  case SMT2_TK_INVALID_HEXADECIMAL:
    fprintf(out, "invalid hexadecimal constant %s", tkval(lex));
    break;

  case SMT2_TK_INVALID_BINARY:
    fprintf(out, "invalid binary constant %s", tkval(lex));
    break;

  case SMT2_TK_INVALID_SYMBOL:
    fprintf(out, "invalid symbol");
    break;

  case SMT2_TK_INVALID_KEYWORD:
    fprintf(out, "invalid keyword");
    break;

  case SMT2_TK_ERROR:
    fprintf(out, "invalid token %s", tkval(lex));
    break;
    
  default:
    if (expected_token >= 0) {
      fprintf(out, "syntax error: %s expected", smt2_token_to_string(expected_token));
    } else {
      fprintf(out, "syntax error");
    }
    break;
  }
  fprintf(out, ")\n" );
  fflush(out);
}


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
  fprintf(out, "(error on line %"PRId32", column %"PRId32" tstack exception %"PRId32")\n",
	  tstack->error_loc.line, tstack->error_loc.column, exception);
  fflush(out);
}



/*
 * MAIN CONTROL FUNCTIONS
 */

/*
 * Initialize all internal structures
 * - benchmark: if true, the input is assumed to be an SMT-LIB 2.0 benchmark
 *  (i.e., a set of assertions followed by a single call to check-sat)
 *  In this mode, destructive simplifications are allowed.
 * - this is called after yices_init so all Yices internals are ready
 */
void init_smt2(bool benchmark) {
  err = stderr;
  out = stdout;
  logic_name = NULL;
  logic_code = SMT_UNKNOWN;
  done = false;
  init_attr_vtbl(&avtbl);
}


/*
 * Delete all structures (close files too)
 */
void delete_smt2(void) {
  if (out != stdout) {
    fclose(out);
  }
  if (err != stderr) {
    fclose(err);
  }
  delete_attr_vtbl(&avtbl);
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
 * Exit function (also called on end-of-file)
 */
void smt2_exit(void) {
  done = true;
}


/*
 * Show all formulas asserted so far
 */
void smt2_get_assertions(void) {
  fprintf(out, "unsupported");
  fflush(out);
}


/*
 * Show the truth value of named Boolean terms 
 * (i.e., those that have a :named attribute)
 */
void smt2_get_assignment(void) {
  fprintf(out, "unsupported");  
  fflush(out);
}


/*
 * Show a proof when context is unsat
 */
void smt2_get_proof(void) {
  fprintf(out, "unsupported");
  fflush(out);  
}


/*
 * Get the unsat core: subset of :named assertions that form an unsat core
 */
void smt2_get_unsat_core(void) {
  fprintf(out, "unsupported");  
  fflush(out);  
}


/*
 * Get the values of terms in the model
 * - the terms are listed in array a
 * - n = number of elements in the array
 */
void smt2_get_value(term_t *a, uint32_t n) {
  fprintf(out, "unsupported");  
  fflush(out);  
}


/*
 * Get the value of an option
 * - name = option name (a keyword)
 */
void smt2_get_option(const char *name) {
  fprintf(out, "unsupported");
  fflush(out);  
}


/*
 * Get some info
 * - name = keyword
 */
void smt2_get_info(const char *name) {
  fprintf(out, "unsupported");
  fflush(out);  
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
  fprintf(out, "unsupported");
  fflush(out);  
}


/*
 * Set some info field
 * - same conventions as set_option
 */
void smt2_set_info(const char *name, aval_t value) {
  fprintf(out, "unsupported");
  fflush(out);  
}


/*
 * Set the logic:
 * - name = logic name (using the SMT-LIB conventions)
 */
void smt2_set_logic(const char *name) {
  fprintf(out, "unsupported");
  fflush(out);
}


/*
 * Push 
 * - n = number of scopes to push
 * - if n = 0, nothing should be done
 */
void smt2_push(uint32_t n) {
  fprintf(out, "unsupported");
  fflush(out);  
}


/*
 * Pop:
 * - n = number of scopes to remove
 * - if n = 0 nothing should be done
 * - if n > total number of scopes then an error should be printed
 *   and nothing done
 */
void smt2_pop(uint32_t n) {
  fprintf(out, "unsupported");
  fflush(out);
}


/*
 * Assert one formula t
 * - if t is a :named assertion then it should be recorded for unsat-core
 */
void smt2_assert(term_t t) {
  fprintf(out, "unsupported");
  fflush(out);
}


/*
 * Check satsifiability of the current set of assertions
 */
void smt2_check_sat(void) {
  fprintf(out, "unsupported");
  fflush(out);
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
  fprintf(out, "unsupported");
  fflush(out);
}


/*
 * Define a new type macro
 * - name = macro name
 * - n = number of variables
 * - var = array of type variables
 * - body = type expressions
 */
void smt2_define_sort(const char *name, uint32_t n, type_t *var, type_t body) {
  fprintf(out, "unsupported");
  fflush(out);
}


/*
 * Declare a new uninterpreted function symbol
 * - name = function name
 * - n = arity
 * - tau = array of n+1 types
 *
 * If n = 0, this creates an uninterpreted constant of type tau[0]
 * Otherwise, this creates an uninterpreted function of type tau[0] x ... x tau[n-1] to tau[n] 
 */
void smt2_declare_fun(const char *name, uint32_t n, type_t *tau) {
  fprintf(out, "unsupported");
  fflush(out);
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
  fprintf(out, "unsupported");
  fflush(out);
}



/*
 * ATTRIBUTES
 */

/*
 * Convert rational q to an attribute value
 * - must return an aval_t index
 * - don't increment its refcounter
 */
aval_t smt2_rational_attr(rational_t *q) {
  return attr_vtbl_rational(&avtbl, q);
}

/*
 * Convert a bitvector constant to an attribute value
 * - must return an aval_t index
 * - don't increment its refcounter
 *
 * smt2_bv64_attr(n, c)
 * - n = number of bits (with 1 <= n <= 64)
 * - c = constant value (normalized modulo 2^n)
 *
 * smt2_bv_attr(n, c)
 * - n = number of bits (with 64 < n)
 * - c = constant value (normalized modulo 2^n)
 *   c is an array of 32bit words
 */
aval_t smt2_bv64_attr(uint32_t n, uint64_t c) {
  return attr_vtbl_bv64(&avtbl, n, c); 
}

aval_t smt_bv_attr(uint32_t n, uint32_t *c) {
  return attr_vtbl_bv(&avtbl, n, c);
}


/*
 * Convert a keyword or symbol to an attribute value
 * - must return an aval_t index
 * - don't increment its refcounter
 */
aval_t smt_symbol_attr(const char *name) {
  return attr_vtbl_symbol(&avtbl, name);
}


/*
 * Same thing for a string
 */
aval_t smt_string_attr(const char *name) {
  return attr_vtbl_string(&avtbl, name);
}


/*
 * Build an attribute list (s-expr)
 * - a[0] ... a[n-1] = list elements
 * - each element in the list is an aval_t index
 *   returned by the attr functions
 * - this must return an aval_t index representing the list
 * - don't increment its ref counter
 */
aval_t smt2_list_attr(uint32_t n, aval_t *a) {
  return attr_vtbl_list(&avtbl, n, a);
}


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
