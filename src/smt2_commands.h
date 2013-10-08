/*
 * SUPPORT FOR SMT-LIB 2.0: ALL COMMANDS
 */

/*
 * This module implements all the SMT-LIB 2 functions.
 * The intended use is as follows:
 *
 *   yices_init();
 *   init_smt2(flag);
 *   initialize parser + lexer;
 *   while (smt2_active()) {
 *     parse an smt2 command;
 *     // as a result, one of the functions below is called
 *   }
 *   delete parser and lexer;
 *   delete_smt2();
 *   yices_exit();
 *
 * The tstack in smt2_parser will invoke the top-level SMT2 commands
 * and will call the error-reporting functions on a syntax error or
 * exception raised by the term stack.
 */

#ifndef __SMT2_COMMANDS_H
#define __SMT2_COMMANDS_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#include "int_vectors.h"
#include "lexer.h"
#include "term_stack2.h"
#include "string_hash_map.h"
#include "tracer.h"


/*
 * New exception codes
 * - in SMT2, we distinguish between eight types of symbols
 * 
 *   sort name (e.g., Real)
 *   indexed sort name (e.g.,  BitVec)
 *   sort constructor (e.g., Array)
 *   indexed sort constructor (no example yet, but the standard allows them)
 *
 *   term name (e.g., true)
 *   indexed term (e.g. bv234 in (_ bv234 13)
 *   function name (e.g., distinct)
 *   indexed function name (e.g., sign-extend in ((_ sign-extend 3) x)
 *
 * - we raise different exceptions when a built-in symbol is misused and 
 *   when a symbol is undefined.
 */
enum smt2_errors {
  SMT2_MISSING_NAME = NUM_TSTACK_ERRORS,   // missing name in (! <term> ,,,, :name X ...)
  SMT2_MISSING_PATTERN,                    // missing p in (! <term> ... :pattern p ...)

  SMT2_SYMBOL_NOT_SORT,                    // misused as a sort name
  SMT2_SYMBOL_NOT_IDX_SORT,                // misused as an indexed sort name
  SMT2_SYMBOL_NOT_SORT_OP,                 // misused as a sort constuctor
  SMT2_SYMBOL_NOT_IDX_SORT_OP,             // misused as an indexed sort constructor
  SMT2_SYMBOL_NOT_TERM,
  SMT2_SYMBOL_NOT_IDX_TERM,
  SMT2_SYMBOL_NOT_FUNCTION,
  SMT2_SYMBOL_NOT_IDX_FUNCTION,

  SMT2_UNDEF_IDX_SORT,                     // undefined indexed sort
  SMT2_UNDEF_IDX_SORT_OP,                  // undefined indexed sort constructor
  SMT2_UNDEF_IDX_TERM,                     // undefined indexed term
  SMT2_UNDEF_IDX_FUNCTION,                 // undefined indexed function

  SMT2_TYPE_ERROR_IN_QUAL,                 // type mismatch in an (as ... <sort>) expression
  SMT2_QUAL_NOT_IMPLEMENTED,               // for the (as ... ) variants we don't support

  SMT2_INVALID_IDX_BV,                     // raised by (_ bv0xxx ...)
};


#define NUM_SMT2_EXCEPTIONS (SMT2_INVALID_IDX_BV+1)


/*
 * New opcodes:
 * - all top-level commands for SMT-LIB 2
 * - special constructors for indexed sort symbols, 
 *   indexed term symbols, and terms with sorts
 * - constructor for attribute list
 * - array theory sort and functions
 * - processing of term annotations
 */
enum smt2_opcodes {
  SMT2_EXIT = NUM_BASE_OPCODES,         // [exit]
  SMT2_SILENT_EXIT,                     // [silent-exit]
  SMT2_GET_ASSERTIONS,                  // [get-assertions]
  SMT2_GET_ASSIGNMENT,                  // [get-assignment]
  SMT2_GET_PROOF,                       // [get-proof]
  SMT2_GET_UNSAT_CORE,                  // [get-unsat-core]
  SMT2_GET_VALUE,                       // [get-value <term> ... <term> ]
  SMT2_GET_OPTION,                      // [get-option <keyword> ]
  SMT2_GET_INFO,                        // [get-info <keyword> ]
  SMT2_SET_OPTION,                      // [set-option <keyword> ] or [set-option <keyword> <value> ]
  SMT2_SET_INFO,                        // [set-info <keyword> ] or [set-info <keyword> <value> ]
  SMT2_SET_LOGIC,                       // [set-logic <symbol> ]
  SMT2_PUSH,                            // [push <numeral> ]
  SMT2_POP,                             // [pop <numeral> ]
  SMT2_ASSERT,                          // [assert <term> ]
  SMT2_CHECK_SAT,                       // [check-sat ]
  SMT2_DECLARE_SORT,                    // [declare-sort <symbol> <numeral> ]
  SMT2_DEFINE_SORT,                     // [define-sort <symbol> <type-binding> ... <type-binding> <sort> ]
  SMT2_DECLARE_FUN,                     // [declare-fun <symbol> <sort> ... <sort> ]
  SMT2_DEFINE_FUN,                      // [define-fun <symbol> <binding> ... <binding> <sort> <term> ]
  // attributes
  SMT2_MAKE_ATTR_LIST,                  // [make-attr-list <value> .... <value> ]
  SMT2_ADD_ATTRIBUTES,                  // [add-attribute <term> <keyword> <value> ... <keyword> <value>] (<value> may be omitted)
  // array theory
  SMT2_MK_ARRAY,                        // [mk-array <index-sort> <sort> ]
  SMT2_MK_SELECT,                       // [select <array> <index> ]
  SMT2_MK_STORE,                        // [store <array> <index> <value> ]
  // sort constructors
  SMT2_INDEXED_SORT,                    // [indexed-sort <symbol> <numeral> ... <numeral> ]
  SMT2_APP_INDEXED_SORT,                // [app-indexed-sort <symbol> <numeral> ... <numeral> <sort> ... <sort>]
  // term constructors
  SMT2_INDEXED_TERM,                    // [indexed-term <symbol> <numeral> ... <numeral> ]
  SMT2_SORTED_TERM,                     // [sorted-term <symbol> <sort> ]
  SMT2_SORTED_INDEXED_TERM,             // [sorted-indexed-term <symbol> <numeral> ... <numeral> <sort> ]
  SMT2_INDEXED_APPLY,                   // [indexed-apply <symbol> <numeral> ... <numeral> <term> ... <term>]
  SMT2_SORTED_APPLY,                    // [sorted-apply <symbol> <sort> <term> ... <term> ]
  SMT2_SORTED_INDEXED_APPLY,            // [sorted-indexed-apply <symbol> <numeral> ... <numeral> <sort> <term> ... <term> ]  
  // not implemented yet
  SMT2_MK_DIV,
  SMT2_MK_MOD,
  SMT2_MK_ABS,
  SMT2_MK_TO_REAL,
  SMT2_MK_TO_INT,
  SMT2_MK_IS_INT,
  SMT2_MK_DIVISIBLE,
} smt2_opcodes_t;

#define NUM_SMT2_OPCODES (SMT2_MK_DIVISIBLE+1)


/*
 * Stack to deal with push and pop.
 * SMT2 push/pop is complicated 
 * - push and pop take a numerical argument. In theory,
 *   one can write stuff like:
 *     (push 102898)
 *     (pop 102897)
 *   which should have the same effect as a simple (push 1)
 * - another issue is that declarations don't have global
 *   scope so we must remove symbols from the symbol tables
 *   on calls to (pop ...)
 * - we make the latter point optional (add an option that
 *   enable declarations to have global scope).
 *
 * To support these features:
 * - we use a stack that keeps tracks of (push n) and of 
 *   term/type/macro names.
 * - we convert (push n) when n > 1 to (n-1) no ops followed by a single 
 *   a real (push) on the context.
 *
 * We use three name_stacks to store symbols (for terms, types, and macros).
 * For each (push n): we store
 * - multiplicity = n
 * - term_dcls = number of term declarations so far
 * - type_dcls = number of type declarations 
 * - macro_dcls = number of type macro declarations
 *
 * For garbage collection, each name_stack keeps a counter of deleted names
 */
typedef struct smt2_name_stack_s {
  char **names;
  uint32_t top;
  uint32_t size;
  uint32_t deletions;
} smt2_name_stack_t;

#define DEF_SMT2_NAME_STACK_SIZE 1024
#define MAX_SMT2_NAME_STACK_SIZE (UINT32_MAX/sizeof(char *))

// what we keep for each push
typedef struct smt2_push_rec_s {
  uint32_t multiplicity;
  uint32_t term_decls;
  uint32_t type_decls;
  uint32_t macro_decls;
} smt2_push_rec_t;

// levels = sum of all multiplicities
typedef struct smt2_stack_s {
  smt2_push_rec_t *data;
  uint32_t top;
  uint32_t size;
  uint64_t levels;
} smt2_stack_t;

#define DEF_SMT2_STACK_SIZE 128
#define MAX_SMT2_STACK_SIZE (UINT32_MAX/sizeof(smt2_push_rec_t))



/*
 * Global structure initialized by init_smt2:
 * - include option flags mandated by SMT2
 * - the flag benchmark_mode is true for SMT2 benchmarks
 *   this is the same as mode=one-check for Yices
 * - gloabl_decls indicates whether declarations should
 *   be global or scoped. In scoped mode, declarations that
 *   occur after a (push ..) command are removed by the matching (pop ..).
 *   In global mode, declarations are kept independent of (push ..) and (pop ...)
 *   global_decls is false by default.
 *
 * The solver can be initialized in benchmark_mode by calling init_smt2(true).
 * This mode is intended for basic SMT2 benchmarks: a sequence of declarations,
 * and assert followed by a single call to (check-sat).
 * In this mode:
 * - push/pop are not supported
 * - destructive simplifications are applied to the assertions
 * - we delay the processing of assertions until the call to check_sat().
 *   So every call to smt2_assert(t) just adds t to the assertion vector.
 *
 * The solver is initialzed in incremental node by calling init_smt2(false).
 * In this mode, push/pop are supported. Some preprocessing is disabled 
 * (e.g., symmetry breaking).
 *
 * In incremental mode, we must accept commands such as (assert) and
 * (push) even if the context is already unsat. Since an unsat yices
 * context can't accept new assertions or push, we turn these into no-ops
 * (i.e., silently ignore them). Except that to correctly match the (push)
 * and (pop), we keep track of the number of calls to (push) after unsat.
 * This is kept in the push_after_unsat counter.
 * 
 * NOTE: all solvers I've tried use :print-success false by default
 * (even though the standard says otherwise).
 */
typedef struct smt2_globals_s {
  // logic: initially SMT_UNKNOWN 
  smt_logic_t logic_code;
  bool benchmark_mode;
  bool global_decls;

  // number of calls to push after the ctx is unsat
  uint32_t pushes_after_unsat;

  // logic name
  char *logic_name;

  // output/diagnostic channels
  FILE *out;                  // default = stdout
  FILE *err;                  // default = stderr
  
  // names of the output/dianostic channels
  char *out_name;             // default = NULL (means "stdout")
  char *err_name;             // default = NULL (means "stderr")

  // tracer object: used only if verbosity > 0
  tracer_t *tracer;

  // options
  bool print_success;         // default = true
  bool expand_definitions;    // default = false
  bool interactive_mode;      // default = false
  bool produce_proofs;        // default = false
  bool produce_unsat_cores;   // default = false
  bool produce_models;        // default = false
  bool produce_assignments;   // default = false
  uint32_t random_seed;       // default = 0
  uint32_t verbosity;         // default = 0

  // internals
  attr_vtbl_t *avtbl;        // global attribute table
  strmap_t *info;            // for set-info/get-info (initially NULL)
  context_t *ctx;            // context (initially NULL)
  model_t *model;            // model (ihitially NULL)

  // push/pop support
  smt2_stack_t stack;
  smt2_name_stack_t term_names;
  smt2_name_stack_t type_names;
  smt2_name_stack_t macro_names;

  /*
   * Support for delayed assertions
   * - assertions = a set of assertions
   * - trivially_unsat: true if one of the assertions simplifies to false
   * - frozen: set to true after the first call to check_sat if benchmark is true
   */
  ivector_t assertions;
  bool trivially_unsat; 
  bool frozen;
} smt2_globals_t;


extern smt2_globals_t __smt2_globals;



/*
 * Initialize all internal structures
 * - benchmark: if true, the input is assumed to be an SMT-LIB 2.0 benchmark
 *   (i.e., a set of assertions followed by a single call to check-sat)
 *   In this mode, destructive simplifications are allowed.
 * - this is called after yices_init so all Yices internals are ready
 */
extern void init_smt2(bool benchmark);


/*
 * Delete all internal structures (called after exit).
 */
extern void delete_smt2(void);


/*
 * Check whether the smt2 solver is ready
 * - this must be true after init_smt2()
 * - this must return false if smt2_exit has been called or after
 *   an unrecoverable error
 */
extern bool smt2_active(void);



/*
 * TOP-LEVEL SMT2 COMMANDS
 */

/*
 * Exit function
 */
extern void smt2_exit(void);


/*
 * Silent exits (on end-of-file)
 * - same as exit but never prints success
 */
extern void smt2_silent_exit(void);


/*
 * Show all formulas asserted so far
 */
extern void smt2_get_assertions(void);


/*
 * Show the truth value of named Boolean terms 
 * (i.e., those that have a :named attribute)
 */
extern void smt2_get_assignment(void);


/*
 * Show a proof when context is unsat
 */
extern void smt2_get_proof(void);


/*
 * Get the unsat core: subset of :named assertions that forms an unsat core
 */
extern void smt2_get_unsat_core(void);


/*
 * Get the values of terms in the model
 * - the terms are listed in array a
 * - n = number of elements in the array
 */
extern void smt2_get_value(term_t *a, uint32_t n);


/*
 * Get the value of an option
 * - name = option name (a keyword)
 */
extern void smt2_get_option(const char *name);


/*
 * Get some info
 * - name = keyword
 */
extern void smt2_get_info(const char *name);


/*
 * Set an option:
 * - name = option name (keyword)
 * - value = value (stored in the attribute_value table)
 *
 * SMT2 allows the syntax (set-option :keyword). In such a case,
 * this function is called with value = NULL_VALUE (i.e., -1).
 */
extern void smt2_set_option(const char *name, aval_t value);


/*
 * Set some info field
 * - same conventions as set_option
 */
extern void smt2_set_info(const char *name, aval_t value);


/*
 * Set the logic:
 * - name = logic name (using the SMT-LIB conventions)
 */
extern void smt2_set_logic(const char *name);


/*
 * Push 
 * - n = number of scopes to push
 * - if n = 0, nothing should be done
 */
extern void smt2_push(uint32_t n);


/*
 * Pop:
 * - n = number of scopes to remove
 * - if n = 0 nothing should be done
 * - if n > total number of scopes then an error should be printed
 *   and nothing else should be done
 */
extern void smt2_pop(uint32_t n);


/*
 * Assert a formula t
 * - if t is a :named assertion then it should be recorded for unsat-core
 */
extern void smt2_assert(term_t t);


/*
 * Check satsifiability of the current set of assertions
 */
extern void smt2_check_sat(void);


/*
 * Declare a new sort:
 * - name = sort name
 * - arity = arity
 *
 * If arity is 0, this defines a new uninterpreted type.
 * Otherwise, this defines a new type constructor.
 */
extern void smt2_declare_sort(const char *name, uint32_t arity);


/*
 * Define a new type macro
 * - name = macro name
 * - n = number of variables
 * - var = array of type variables
 * - body = type expression
 */
extern void smt2_define_sort(const char *name, uint32_t n, type_t *var, type_t body);


/*
 * Declare a new uninterpreted function symbol
 * - name = function name
 * - n = arity + 1
 * - tau = array of n types
 *
 * If n = 1, this creates an uninterpreted constant of type tau[0]
 * Otherwise, this creates an uninterpreted function of type tau[0] x ... x tau[n-1] to tau[n] 
 */
extern void smt2_declare_fun(const char *name, uint32_t n, type_t *tau);


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
extern void smt2_define_fun(const char *name, uint32_t n, term_t *var, term_t body, type_t tau);



/*
 * ATTRIBUTES
 */

/*
 * Add a :named attribute to term t
 */
extern void smt2_add_name(term_t t, const char *name);


/*
 * Add a :pattern attribute to term t
 * - the pattern is a an array p of n terms
 */
extern void smt2_add_pattern(term_t t, term_t *p, uint32_t n);



/*
 * ERROR REPORTING
 */

/*
 * Syntax error
 * - lex = lexer 
 * - expected_token = either an smt2_token or -1 or -2
 *
 * lex is as follows: 
 * - current_token(lex) = token that caused the error
 * - current_token_value(lex) = corresponding string
 * - current_token_length(lex) = length of that string
 * - lex->tk_line and lex->tk_column = start of the token in the input
 * - lex->reader.name  = name of the input file (NULL means input is stdin)
 *
 * expected token = -2, means 'command expected'
 */
extern void smt2_syntax_error(lexer_t *lex, int32_t expected_token);


/*
 * Exception raised by the tstack
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
extern void smt2_tstack_error(tstack_t *stack, int32_t exception);



#endif /* __SMT2_COMMANDS_H */
