/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Lexer for the SMT-LIB language (the benchmarks part)
 *
 * Fix: 2007-07-02 removed SMT_TK_U. U is used as a term symbol
 * in some of the AUFLIA benchmarks, so we can't use it as a keyword.
 */

#ifndef __SMT_LEXER_H
#define __SMT_LEXER_H

#include <stdint.h>

#include "parser_utils/lexer.h"
#include "api/smt_logic_codes.h"


/*
 * Tokens:
 * - we consider ':' ']' and '[' as individual tokens to deal with
 *   extract and BitVec.
 * - the parser must then check proper formatting of BitVec[size]
 *   and extract[i:j]
 */
enum smt_token {
  // separators
  SMT_TK_LP, SMT_TK_RP, SMT_TK_LB, SMT_TK_RB, SMT_TK_COLON, SMT_TK_EOS,

  // strings, symbols, variables, attributes
  SMT_TK_STRING, SMT_TK_SYMBOL, SMT_TK_VAR, SMT_TK_FVAR,
  SMT_TK_ATTRIBUTE, SMT_TK_USER_VALUE,

  // numerals: more permissive than SMT LIB, we allow
  // rationals as <optional_sign><digits> or <optional_sign><digits>/<digits>
  // floats as <optional_sigm><digits>.<digits>
  SMT_TK_RATIONAL, SMT_TK_FLOAT,

  // bitvector constants "bv<digits>" (size is determined by the theory (e.g., QF_UFBV[32])
  // New bitvector theory: size is appended in the format "bv<digits>[i]"
  SMT_TK_BV_CONSTANT,

  // bitvector constants in binary "bvbin<bits>" and hexadecimal "bvhex<bits>"
  SMT_TK_BV_BINCONSTANT, SMT_TK_BV_HEXCONSTANT,

  // SMT-LIB keywords (independent of the logic and theories)
  SMT_TK_DISTINCT, SMT_TK_ITE, SMT_TK_EQ,

  SMT_TK_TRUE, SMT_TK_FALSE, SMT_TK_NOT, SMT_TK_IMPLIES, SMT_TK_IF_THEN_ELSE, SMT_TK_AND,
  SMT_TK_OR, SMT_TK_XOR, SMT_TK_IFF, SMT_TK_EXISTS, SMT_TK_FORALL, SMT_TK_LET, SMT_TK_FLET,

  // attribute for patterns
  SMT_TK_PAT, SMT_TK_NOPAT,

  // benchmark attributes and keywords
  SMT_TK_BENCHMARK, SMT_TK_SAT, SMT_TK_UNSAT, SMT_TK_UNKNOWN, SMT_TK_LOGIC,
  SMT_TK_ASSUMPTION, SMT_TK_FORMULA, SMT_TK_STATUS, SMT_TK_EXTRASORTS,
  SMT_TK_EXTRAFUNS, SMT_TK_EXTRAPREDS, SMT_TK_NOTES,

  // theories: sort symbols
  SMT_TK_ARRAY, SMT_TK_INT, SMT_TK_REAL,
  SMT_TK_ARRAY1, SMT_TK_ARRAY2, SMT_TK_BITVEC,

  // theories: function symbols
  SMT_TK_ADD, SMT_TK_SUB, SMT_TK_MUL, SMT_TK_DIV, SMT_TK_TILDE, SMT_TK_LT, SMT_TK_LE,
  SMT_TK_GT, SMT_TK_GE, SMT_TK_SELECT, SMT_TK_STORE,

  // old bitvector functions
  SMT_TK_BVADD, SMT_TK_BVSUB, SMT_TK_BVMUL, SMT_TK_BVNEG,
  SMT_TK_BVOR, SMT_TK_BVAND, SMT_TK_BVXOR, SMT_TK_BVNOT,
  SMT_TK_BVLT, SMT_TK_BVLEQ, SMT_TK_BVGT, SMT_TK_BVGEQ,
  SMT_TK_BVSLT, SMT_TK_BVSLEQ, SMT_TK_BVSGT, SMT_TK_BVSGEQ,
  SMT_TK_CONCAT, SMT_TK_EXTRACT, SMT_TK_SIGN_EXTEND, SMT_TK_SHIFT_LEFT0,
  SMT_TK_SHIFT_LEFT1, SMT_TK_SHIFT_RIGHT0, SMT_TK_SHIFT_RIGHT1, SMT_TK_BIT0, SMT_TK_BIT1,

  // new bitvector functions
  SMT_TK_BVUDIV, SMT_TK_BVUREM,
  SMT_TK_BVSDIV, SMT_TK_BVSREM, SMT_TK_BVSMOD,
  SMT_TK_BVSHL,  SMT_TK_BVLSHR, SMT_TK_BVASHR,
  SMT_TK_BVNAND, SMT_TK_BVNOR,  SMT_TK_BVXNOR,
  SMT_TK_BVREDOR, SMT_TK_BVREDAND, SMT_TK_BVCOMP,

  SMT_TK_REPEAT, SMT_TK_ZERO_EXTEND, SMT_TK_ROTATE_LEFT, SMT_TK_ROTATE_RIGHT,

  // new names of bitvector predicates
  SMT_TK_BVULT, SMT_TK_BVULE, SMT_TK_BVUGT, SMT_TK_BVUGE,
  SMT_TK_BVSLE, SMT_TK_BVSGE,

  // errors
  SMT_TK_OPEN_STRING, SMT_TK_OPEN_USER_VAL,
  SMT_TK_ZERO_DIVISOR, SMT_TK_INVALID_NUMBER,
  SMT_TK_ERROR,
};

typedef enum smt_token smt_token_t;

#define NUM_SMT_TOKENS (SMT_TK_ERROR+1)


/*
 * Initialization
 */
extern int32_t init_smt_file_lexer(lexer_t *lex, char *filename);

extern void init_smt_stream_lexer(lexer_t *lex, FILE *f, char *name);

static inline void init_smt_stdin_lexer(lexer_t *lex) {
  init_smt_stream_lexer(lex, stdin, "stdin");
}

extern void init_smt_string_lexer(lexer_t *lex, char *data, char *name);


/*
 * Select built-in symbols for logic
 */
extern void smt_lexer_activate_logic(smt_logic_t logic);


/*
 * Conversion from an SMT token to a string
 */
extern char *smt_token_to_string(smt_token_t tk);


/*
 * Read next token and return its type
 * - update lex->token (set it to tk)
 * - update lex->tk_pos, tk_line, tk_pos (to the start of token
 *   in the input stream)
 * - store token_value in lex->buffer.
 */
extern smt_token_t next_smt_token(lexer_t *lex);



#endif /* __SMT_LEXER_H */
