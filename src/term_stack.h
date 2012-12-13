/*
 * Stack-based API for building terms and types
 * Intended to support parsing.
 *
 * The stack contains a nested sequence of frames.  Each frame
 * consists of an operator (term or type constructor) and a sequence
 * of arguments. The arguments are string (that may denote symbols),
 * bindings, rationals or bitvector constants, buffers, terms, or types. 
 *
 * Bindings are pairs <name, term>. They record temporary bindings from
 * names to terms (for let, forall, exists). The binding of name to term
 * is erased when the binding is deleted.
 *
 * To help reporting errors, each element on the stack has location information.
 *
 * Several commands call an external procedures:
 * - by default these procedures just print a message (for testing)
 * - they can be changed via the set_cmd functions
 * - the term_stack modules check that the arguments are correct
 *   then call the external procedure
 */

#ifndef __TERM_STACK_H
#define __TERM_STACK_H

#include <stdint.h>
#include <stdbool.h>
#include <setjmp.h>

#include "arena.h"
#include "terms.h"
#include "bvlogic_buffers.h"

/*
 * Objects on the stack
 * - tag = identifies the object's type
 * - val = union type
 * - loc = location information for error reporting
 *
 * For operators, we record an opcode, a multiplicity index (for associative
 * operators), and the index of the previous operator on the stack.
 */
typedef enum tag_enum {
  TAG_NONE,
  TAG_OP,               // operator
  TAG_SYMBOL,           // symbol or string
  TAG_BV64,             // bit-vector constant (1 to 64 bits)
  TAG_BV,               // bit-vector constant (more than 64 bits)
  TAG_RATIONAL,         // rational constant
  TAG_TERM,             // term index + polarity (from the global term table)
  TAG_TYPE,             // type index (from the global type table);
  TAG_ARITH_BUFFER,     // polynomial buffer (rational coefficients)
  TAG_BVARITH64_BUFFER, // polynomial buffer (bitvector coefficients, 1 to 64 bits)
  TAG_BVARITH_BUFFER,   // polynomial buffer (bitvector coefficients, more than 64 bits)
  TAG_BVLOGIC_BUFFER,   // array of bits
  TAG_BINDING,          // pair <name, term>
} tag_t;

#define NUM_TAGS (TAG_BINDING+1)

typedef enum opcode_enum {
  NO_OP,

  // deal with symbols and bindings
  DEFINE_TYPE,
  DEFINE_TERM,
  BIND,
  DECLARE_VAR,
  LET,

  // type constructors
  MK_BV_TYPE,
  MK_SCALAR_TYPE,
  MK_TUPLE_TYPE,
  MK_FUN_TYPE,

  // term constructors
  MK_APPLY, MK_ITE, MK_EQ, MK_DISEQ, MK_DISTINCT,
  MK_NOT, MK_OR, MK_AND, MK_XOR, MK_IFF, 
  MK_IMPLIES, MK_TUPLE, MK_SELECT, MK_TUPLE_UPDATE, MK_UPDATE,
  MK_FORALL, MK_EXISTS, MK_LAMBDA,

  // arithmetic
  MK_ADD, MK_SUB, MK_NEG, MK_MUL, MK_DIV, MK_POW, MK_GE, MK_GT, MK_LE, MK_LT,

  // bitvectors
  MK_BV_CONST,      // (mk-bv number size)
  MK_BV_ADD, MK_BV_SUB, MK_BV_MUL, MK_BV_NEG, MK_BV_POW,
  MK_BV_NOT, MK_BV_AND, MK_BV_OR, MK_BV_XOR,
  MK_BV_NAND, MK_BV_NOR, MK_BV_XNOR,
  MK_BV_SHIFT_LEFT0, MK_BV_SHIFT_LEFT1,
  MK_BV_SHIFT_RIGHT0, MK_BV_SHIFT_RIGHT1, MK_BV_ASHIFT_RIGHT,
  MK_BV_ROTATE_LEFT, MK_BV_ROTATE_RIGHT,
  MK_BV_EXTRACT, MK_BV_CONCAT, MK_BV_REPEAT,
  MK_BV_SIGN_EXTEND, MK_BV_ZERO_EXTEND,
  MK_BV_GE, MK_BV_GT, MK_BV_LE, MK_BV_LT,     // unsigned
  MK_BV_SGE, MK_BV_SGT, MK_BV_SLE, MK_BV_SLT, // signed

  // new SMT-LIB operators
  MK_BV_SHL, MK_BV_LSHR, MK_BV_ASHR,
  MK_BV_DIV, MK_BV_REM,                  // unsigned
  MK_BV_SDIV, MK_BV_SREM, MK_BV_SMOD,    // signed
  MK_BV_REDOR, MK_BV_REDAND, MK_BV_COMP,
  
  // other operations
  BUILD_TERM, BUILD_TYPE, 

  // external operations
  EXIT_CMD, CHECK_CMD, ECHO_CMD, INCLUDE_CMD, ASSERT_CMD,
  PUSH_CMD, POP_CMD, RESET_CMD, SHOWMODEL_CMD, EVAL_CMD, 
  SET_PARAM_CMD, SHOW_PARAM_CMD, SHOW_PARAMS_CMD, 
  SHOW_STATS_CMD, RESET_STATS_CMD, SET_TIMEOUT_CMD, 
  SHOW_TIMEOUT_CMD, HELP_CMD,

  // DUMP_CMD is used below. Keep it last
  DUMP_CMD,
} opcode_t;

#define NUM_OPCODES (DUMP_CMD+1)

// operator
typedef struct opval_s {
  opcode_t opcode;
  uint32_t multiplicity;
  uint32_t prev;
} opval_t;

// binding 
typedef struct binding_s {
  term_t term;
  char *symbol;
} binding_t;

// location: line + column number
typedef struct loc_s {
  uint32_t line; 
  uint32_t column;
} loc_t;

// two variant representations for bitvector constants
// one for bitsize between 1 and 64
// one for bitsize > 64
typedef struct bv64_s {
  uint32_t bitsize; // size in bits
  uint64_t value;   // value (padded to 64 bits)
} bv64_t;

typedef struct bv_s { 
  uint32_t bitsize; // size in bits
  uint32_t *data;   // value as an array of 32bit words
} bv_t;


// element on the stack
typedef struct stack_elem_s {
  tag_t tag;
  union {
    opval_t opval;
    char *symbol;
    bv64_t bv64;
    bv_t bv;
    rational_t rational;
    term_t term;
    type_t type;
    arith_buffer_t *arith_buffer;
    bvarith64_buffer_t *bvarith64_buffer;
    bvarith_buffer_t *bvarith_buffer;
    bvlogic_buffer_t *bvlogic_buffer;
    binding_t binding;
  } val;
  loc_t loc;
} stack_elem_t ;


/*
 * Argument to the setparam command encodes an immediate value
 * - the tag is given by the enumeration below
 * - PARAM_VAL_ERROR means an unexpected value was pushed
 * - the value is either a pointer to rational or a symbol 
 */
typedef enum param_val_enum {
  PARAM_VAL_FALSE,
  PARAM_VAL_TRUE,
  PARAM_VAL_RATIONAL,
  PARAM_VAL_SYMBOL,
  PARAM_VAL_ERROR,
} param_val_enum_t;

typedef struct param_val_s {
  param_val_enum_t tag;
  union {
    rational_t *rational;
    char *symbol;
  } val;
} param_val_t;



/*
 * External commands: currently the following commands are supported.
 * - void exit_cmd(void)
 * - void check_cmd(void)
 * - void showmodel_cmd(void)
 * - void push_cmd(void)
 * - void pop_cmd(void)
 * - void reset_cmd(void)
 * - void dump_cmd(void)
 * - void echo_cmd(char *s)
 * - void include_cmd(char *s)
 * - void assert_cmd(term_t t)
 * - void eval_cmd(term_t t)
 * - void setparam_cmd(char *param, param_val_t *val)
 * - void show_param_cmd(char *param)
 * - void show_params_cmd(void)
 * - void showstats_cmd(void)
 * - void resetstats_cmd(void)
 * - void settimeout_cmd(int32_t val)
 * - void showtimeout_cmd(void)
 * - void help_cmd(char *s)
 *
 * Two other commands are called within define-type or define-term: 
 * - void type_defined_cmd(char *name, type_t tau):
 *   called after (define-type name tau) 
 *             or (define-type name) is executed
 *
 * - void term_defined_cmd(char *name, term_t t)
 *   called after (define name::type t) 
 *            or (define name::type) is executed
 *
 * Added this to give some feedback to the user when yices_main
 * is used in verbose mode.
 */
typedef void (*exit_cmd_t)(void);
typedef void (*check_cmd_t)(void);
typedef void (*showmodel_cmd_t)(void);
typedef void (*push_cmd_t)(void);
typedef void (*pop_cmd_t)(void);
typedef void (*reset_cmd_t)(void);
typedef void (*dump_cmd_t)(void);
typedef void (*echo_cmd_t)(char *s);
typedef void (*include_cmd_t)(char *s);
typedef void (*assert_cmd_t)(term_t t);
typedef void (*eval_cmd_t)(term_t t);
typedef void (*setparam_cmd_t)(char *param, param_val_t *val);
typedef void (*showparam_cmd_t)(char *param);
typedef void (*showparams_cmd_t)(void);
typedef void (*showstats_cmd_t)(void);
typedef void (*resetstats_cmd_t)(void);
typedef void (*settimeout_cmd_t)(int32_t timeout);
typedef void (*showtimeout_cmd_t)(void);
typedef void (*help_cmd_t)(char *topic);
typedef void (*type_defined_cmd_t)(char *name, type_t tau);
typedef void (*term_defined_cmd_t)(char *name, term_t t);

typedef struct external_cmd_s {
  exit_cmd_t exit_cmd;
  check_cmd_t check_cmd;
  showmodel_cmd_t showmodel_cmd;
  push_cmd_t push_cmd;
  pop_cmd_t pop_cmd;
  reset_cmd_t reset_cmd;
  dump_cmd_t dump_cmd;
  echo_cmd_t echo_cmd;
  include_cmd_t include_cmd;
  assert_cmd_t assert_cmd;
  eval_cmd_t eval_cmd;
  setparam_cmd_t setparam_cmd;
  showparam_cmd_t showparam_cmd;
  showparams_cmd_t showparams_cmd;
  showstats_cmd_t showstats_cmd;
  resetstats_cmd_t resetstats_cmd;
  settimeout_cmd_t settimeout_cmd;
  showtimeout_cmd_t showtimeout_cmd;
  help_cmd_t help_cmd;
  type_defined_cmd_t type_defined_cmd;
  term_defined_cmd_t term_defined_cmd;
} external_cmd_t;


/*
 * Stack:
 * - array of stack_elements
 * - top = top of the stack
 *   elements are stored at indices 0 ... top-1
 *   a bottom marker is stored at index 0
 * - frame = index of the top-frame, element at that index must be an operator
 * - top_op = opcode of the element at index frame
 *
 * - mem = arena for allocation of strings/symbols
 *
 * - auxiliary buffers for internal computations
 * - a global counter for creating fresh variables
 * - a longjmp buffer for simulating exceptions
 *
 * - result: some operations store a term or type result in
 *   stack->term_result or stack->type_result
 *
 * - diagnosis data for error reporting is stored in
 *   error_loc = loc[i] if error occurred on element i 
 *   error_op = operator being evaluated when the error occurred 
 *          (or NO_OP if the error occurred on a push operation)
 *   error_string = null-terminated string value if the erroneous
 *          argument is a string (or NULL).
 *
 * - table of external commands
 */
typedef struct tstack_s {
  stack_elem_t *elem;

  uint32_t top;
  uint32_t size;
  uint32_t frame;
  opcode_t top_op;

  arena_t mem;

  // vector to store types or terms
  int32_t *aux_buffer;
  uint32_t aux_size;

  // buffer to convert stack elements to bitvector constants
  bvconstant_t bvconst_buffer;

  // dynamically allocated buffers
  arith_buffer_t *abuffer;
  bvarith64_buffer_t *bva64buffer;
  bvarith_buffer_t *bvabuffer;
  bvlogic_buffer_t *bvlbuffer;  

  union {
    term_t term;
    type_t type;
  } result;

  jmp_buf env;
  loc_t error_loc;
  opcode_t error_op;
  char *error_string;

  external_cmd_t externals;

} tstack_t;


/*
 * Default and maximal size
 */
#define DEFAULT_TERM_STACK_SIZE 256
#define MAX_TERM_STACK_SIZE (UINT32_MAX/64)

/*
 * Default and maximal size of the t_aux vector
 */
#define DEFAULT_AUX_SIZE 256
#define MAX_AUX_SIZE (UINT32_MAX/4)


/*
 * Exception handling via setjmp and longjmp:
 * -----------------------------------------
 * To set the handler call setjmp(stack->env)
 * The exception handler is called on any error
 * via longjmp(stack->env, error_code).
 *
 * When an exception is raised, the stack may be in an inconsistent
 * state. Do not do any operations on the stack without calling 
 * tstack_reset first.
 */

/*
 * Error codes
 */
typedef enum tstack_error_s {
  TSTACK_NO_ERROR = 0,
  TSTACK_INTERNAL_ERROR,
  TSTACK_OP_NOT_IMPLEMENTED,
  TSTACK_UNDEF_TERM,
  TSTACK_UNDEF_TYPE,
  TSTACK_RATIONAL_FORMAT,
  TSTACK_FLOAT_FORMAT,
  TSTACK_BVBIN_FORMAT,
  TSTACK_BVHEX_FORMAT,
  TSTACK_TYPENAME_REDEF,
  TSTACK_TERMNAME_REDEF,
  TSTACK_DUPLICATE_SCALAR_NAME,
  TSTACK_DUPLICATE_VAR_NAME,
  TSTACK_INVALID_OP,
  TSTACK_INVALID_FRAME,
  TSTACK_INTEGER_OVERFLOW,
  TSTACK_NEGATIVE_EXPONENT,
  TSTACK_NOT_AN_INTEGER,
  TSTACK_NOT_A_SYMBOL,
  TSTACK_NOT_A_RATIONAL,
  TSTACK_NOT_A_TYPE,
  TSTACK_ARITH_ERROR,
  TSTACK_DIVIDE_BY_ZERO,
  TSTACK_NON_CONSTANT_DIVISOR,
  TSTACK_NONPOSITIVE_BVSIZE,
  TSTACK_INCOMPATIBLE_BVSIZES,
  TSTACK_INVALID_BVCONSTANT,
  TSTACK_BVARITH_ERROR,
  TSTACK_BVLOGIC_ERROR,
  TSTACK_TYPE_ERROR_IN_DEFTERM,
  TSTACK_YICES_ERROR,
} tstack_error_t;

#define NUM_TSTACK_ERRORS (TSTACK_YICES_ERROR+1)


/*
 * Initialization and deletion
 */
extern void init_tstack(tstack_t *stack);
extern void delete_tstack(tstack_t *stack);


/*
 * Empty the stack
 */
extern void tstack_reset(tstack_t *stack);

/*
 * Push an operator op
 * - op must be a valid opcode
 * - loc = location
 *
 * raise exception TSTACK_INVALID_OP if op is invalid and set 
 *  stack->error_loc = loc
 *  stack->error_op = op
 *  stack->error_string = NULL
 */
extern void tstack_push_op(tstack_t *stack, opcode_t op, loc_t *loc);

/*
 * Push a string or symbol of length n
 * - copy s[0] ... s[n-1] and add '\0'
 * - s must be terminated by '\0'
 */
extern void tstack_push_string(tstack_t *stack, char *s, uint32_t n, loc_t *loc);

/*
 * For define-type or define term: push a name s on the stack.
 *
 * These functions are like push_string but they raise an exception if
 * name is already used (TSTACK_TYPENAME_REDEF or TSTACK_TERMNAME_REDEF)
 */
extern void tstack_push_free_typename(tstack_t *stack, char *s, uint32_t n, loc_t *loc);
extern void tstack_push_free_termname(tstack_t *stack, char *s, uint32_t n, loc_t *loc);


/*
 * Find the term or type of name s and push that term or type on the stack
 *
 * raise exception TSTACK_UNDEF_TERM or TSTACK_UNDEF_TYPE if the name is
 * not mapped to a term or type.
 */
extern void tstack_push_type_by_name(tstack_t *stack, char *s, loc_t *loc);
extern void tstack_push_term_by_name(tstack_t *stack, char *s, loc_t *loc);


/*
 * Convert a string to a rational and push that
 * - s must be null-terminated and of rational or floating point formats
 *  (cf. rational.h, yices.h)
 *
 * raise exception TSTACK_FORMAT_... if the string s does not have 
 * the right format, and set
 *   stack->error_loc = loc
 *   stack->error_op = NO_OP
 *   stack->error_string = s
 */
extern void tstack_push_rational(tstack_t *stack, char *s, loc_t *loc);
extern void tstack_push_float(tstack_t *stack, char *s, loc_t *loc);

/*
 * Convert a string to a bitvector constant an push that
 * - n = length of the string
 * - s must be a string of binary or hexadecimal digits (no prefix)
 *
 * raise exception TSTACK_FORMAT_... if the string s does not have 
 * the right format, and set
 *   stack->error_loc = loc
 *   stack->error_op = NO_OP
 *   stack->error_string = s
 */
extern void tstack_push_bvbin(tstack_t *stack, char *s, uint32_t n, loc_t *loc);
extern void tstack_push_bvhex(tstack_t *stack, char *s, uint32_t n, loc_t *loc);


/*
 * Push primitive types or terms
 */
extern void tstack_push_bool_type(tstack_t *stack, loc_t *loc);
extern void tstack_push_int_type(tstack_t *stack, loc_t *loc);
extern void tstack_push_real_type(tstack_t *stack, loc_t *loc);
extern void tstack_push_true(tstack_t *stack, loc_t *loc);
extern void tstack_push_false(tstack_t *stack, loc_t *loc);


/*
 * Push integer constants
 */
extern void tstack_push_int32(tstack_t *stack, int32_t val, loc_t *loc);


/*
 * Push terms or types built by other means: used for predefined SMT-LIB
 */
extern void tstack_push_term(tstack_t *stack, term_t t, loc_t *loc);
extern void tstack_push_type(tstack_t *stack, type_t tau, loc_t *loc);


/*
 * SMT-LIB mode: change eval operations to support SMT-LIB variants
 * of mk_eq and some bitvector operations. This cannot be undone.
 */
extern void tstack_set_smt_mode(void);


/*
 * Eval: execute the operation defined by the top-level operator OP,
 * applied to all the arguments on top of OP on the stack.
 *
 * Replace [op arg1 ... argn] by the result of the operation.
 */
extern void tstack_eval(tstack_t *stack);


/*
 * Check whether the stack is empty
 */
static inline bool tstack_is_empty(tstack_t *stack) {
  return stack->top == 1;
}

/*
 * Read result. 
 *
 * Call sequence to use these functions:
 * 1) tstack_push_op(stack, BUILD_TERM, xxx)
 * 2) sequence of push/eval to build the term
 * 3) when tstack_eval evaluates the BUILD_TERM command,
 *    stack->result.term is available.
 * 
 * Same thing for types, but replace by BUILD_TYPE.
 */
static inline term_t tstack_get_term(tstack_t *stack) {
  return stack->result.term;
}

static inline term_t tstack_get_type(tstack_t *stack) {
  return stack->result.type;
}


/*
 * Replace the default commands
 */
static inline void tstack_set_exit_cmd(tstack_t *stack, exit_cmd_t cmd) {
  stack->externals.exit_cmd = cmd;
}

static inline void tstack_set_check_cmd(tstack_t *stack, check_cmd_t cmd) {
  stack->externals.check_cmd = cmd;
}

static inline void tstack_set_showmodel_cmd(tstack_t *stack, showmodel_cmd_t cmd) {
  stack->externals.showmodel_cmd = cmd;
}

static inline void tstack_set_push_cmd(tstack_t *stack, push_cmd_t cmd) {
  stack->externals.push_cmd = cmd;
}

static inline void tstack_set_pop_cmd(tstack_t *stack, pop_cmd_t cmd) {
  stack->externals.pop_cmd = cmd;
}

static inline void tstack_set_reset_cmd(tstack_t *stack, reset_cmd_t cmd) {
  stack->externals.reset_cmd = cmd;
}

static inline void tstack_set_dump_cmd(tstack_t *stack, dump_cmd_t cmd) {
  stack->externals.dump_cmd = cmd;
}

static inline void tstack_set_echo_cmd(tstack_t *stack, echo_cmd_t cmd) {
  stack->externals.echo_cmd = cmd;
}

static inline void tstack_set_include_cmd(tstack_t *stack, include_cmd_t cmd) {
  stack->externals.include_cmd = cmd;
}

static inline void tstack_set_assert_cmd(tstack_t *stack, assert_cmd_t cmd) {
  stack->externals.assert_cmd = cmd;
}

static inline void tstack_set_eval_cmd(tstack_t *stack, eval_cmd_t cmd) {
  stack->externals.eval_cmd = cmd;
}

static inline void tstack_set_setparam_cmd(tstack_t *stack, setparam_cmd_t cmd) {
  stack->externals.setparam_cmd = cmd;
}

static inline void tstack_set_showparam_cmd(tstack_t *stack, showparam_cmd_t cmd) {
  stack->externals.showparam_cmd = cmd;
}

static inline void tstack_set_showparams_cmd(tstack_t *stack, showparams_cmd_t cmd) {
  stack->externals.showparams_cmd = cmd;
}

static inline void tstack_set_showstats_cmd(tstack_t *stack, showstats_cmd_t cmd) {
  stack->externals.showstats_cmd = cmd;
}

static inline void tstack_set_resetstats_cmd(tstack_t *stack, resetstats_cmd_t cmd) {
  stack->externals.resetstats_cmd = cmd;
}

static inline void tstack_set_settimeout_cmd(tstack_t *stack, settimeout_cmd_t cmd) {
  stack->externals.settimeout_cmd = cmd;
}

static inline void tstack_set_showtimeout_cmd(tstack_t *stack, showtimeout_cmd_t cmd) {
  stack->externals.showtimeout_cmd = cmd;
}

static inline void tstack_set_help_cmd(tstack_t *stack, help_cmd_t cmd) {
  stack->externals.help_cmd = cmd;
}

static inline void tstack_set_type_defined_cmd(tstack_t *stack, type_defined_cmd_t cmd) {
  stack->externals.type_defined_cmd = cmd;
}

static inline void tstack_set_term_defined_cmd(tstack_t *stack, term_defined_cmd_t cmd) {
  stack->externals.term_defined_cmd = cmd;
}


#endif /* __TERM_STACK_H */
