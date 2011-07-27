/*
 * Lexer for the SMT-LIB2 Language (scripts)
 */

#ifndef __SMT2_LEXER_H
#define __SMT2_LEXER_H

#include <stdint.h>

#include "lexer.h"
#include "smt_logic_codes.h"

/*
 * Tokens
 */
enum smt2_token {
  // open/close par
  SMT2_TK_LP,
  SMT2_TK_RP,

  // end of stream
  SMT2_TK_EOS,

  // atomic tokens
  SMT2_TK_NUMERAL,
  SMT2_TK_DECIMAL,
  SMT2_TK_HEXADECIMAL,
  SMT2_TK_BINARY,
  SMT2_TK_STRING,
  SMT2_TK_SYMBOL,
  SMT2_TK_KEYWORD,

  // special tokens used in the BV theory: (_ bv<numeral> <numereal>)
  SMT2_TK_BV_CONSTANT,

  /*
   * all predefined symbols, theory symbols, etc.
   */
  // Reserved words
  SMT2_TK_PAR,
  SMT2_TK_NUM,
  SMT2_TK_DEC,
  SMT2_TK_STR,
  SMT2_TK_UNDERSCORE,
  SMT2_TK_BANG,
  SMT2_TK_AS,
  SMT2_TK_LET,
  SMT2_TK_EXISTS,
  SMT2_TK_FORALL,

  // Commands
  SMT2_TK_ASSERT,
  SMT2_TK_CHECK_SAT,
  SMT2_TK_DECLARE_SORT,
  SMT2_TK_DECLARE_FUN,
  SMT2_TK_DEFINE_SORT,
  SMT2_TK_DEFINE_FUN,
  SMT2_TK_EXIT,
  SMT2_TK_GET_ASSERTIONS,
  SMT2_TK_GET_ASSIGNMENT,
  SMT2_TK_GET_INFO,
  SMT2_TK_GET_OPTION,
  SMT2_TK_GET_PROOF,
  SMT2_TK_GET_UNSAT_CORE,
  SMT2_TK_GET_VALUE,
  SMT2_TK_POP,
  SMT2_TK_PUSH,
  SMT2_TK_SET_LOGIC,
  SMT2_TK_SET_INFO,
  SMT2_TK_SET_OPTION,

  // Core theory
  SMT2_TK_BOOL,
  SMT2_TK_TRUE,
  SMT2_TK_FALSE,
  SMT2_TK_NOT,
  SMT2_TK_IMPLIES,
  SMT2_TK_AND,
  SMT2_TK_OR,
  SMT2_TK_XOR,
  SMT2_TK_EQ,
  SMT2_TK_DISTINCT,
  SMT2_TK_ITE,

  // Array theory
  SMT2_TK_ARRAY,
  SMT2_TK_SELECT,
  SMT2_TK_STORE,

  // Arithmetic symbols
  SMT2_TK_INT,
  SMT2_TK_REAL,
  SMT2_TK_MINUS,
  SMT2_TK_PLUS,
  SMT2_TK_TIMES,
  SMT2_TK_DIVIDES,
  SMT2_TK_LE,
  SMT2_TK_LT,
  SMT2_TK_GE,
  SMT2_TK_GT,
  SMT2_TK_DIV,
  SMT2_TK_MOD,
  SMT2_TK_ABS,
  SMT2_TK_TO_REAL,
  SMT2_TK_TO_INT,
  SMT2_TK_IS_INT,
  SMT2_TK_DIVISIBLE,

  // Bit-vector symbols
  SMT2_TK_BITVEC,
  SMT2_TK_CONCAT,
  SMT2_TK_EXTRACT,
  SMT2_TK_REPEAT,
  SMT2_TK_BVCOMP,
  SMT2_TK_BVREDOR,    // In SMT1.2 but not in SMT2.0 (keep it defined but inactive)
  SMT2_TK_BVREDAND,   // In SMT1.2 but not in SMT2.0 (same thing)

  SMT2_TK_BVNOT,
  SMT2_TK_BVAND,
  SMT2_TK_BVOR,
  SMT2_TK_BVNAND,
  SMT2_TK_BVNOR,
  SMT2_TK_BVXOR,
  SMT2_TK_BVXNOR,

  SMT2_TK_BVNEG,
  SMT2_TK_BVADD,
  SMT2_TK_BVSUB,
  SMT2_TK_BVMUL,
  SMT2_TK_BVUDIV,
  SMT2_TK_BVUREM,
  SMT2_TK_BVSDIV,
  SMT2_TK_BVSREM,
  SMT2_TK_BVSMOD,

  SMT2_TK_BVSHL,
  SMT2_TK_BVLSHR,
  SMT2_TK_BVASHR,
  SMT2_TK_ZERO_EXTEND,
  SMT2_TK_SIGN_EXTEND,
  SMT2_TK_ROTATE_LEFT,
  SMT2_TK_ROTATE_RIGHT,

  SMT2_TK_BVULT,
  SMT2_TK_BVULE,
  SMT2_TK_BVUGT,
  SMT2_TK_BVUGE,
  SMT2_TK_BVSLT,
  SMT2_TK_BVSLE,
  SMT2_TK_BVSGT,
  SMT2_TK_BVSGE,

  // Errors
  SMT2_TK_INVALID_STRING,
  SMT2_TK_INVALID_NUMERAL,
  SMT2_TK_INVALID_DECIMAL,
  SMT2_TK_INVALID_HEXADECIMAL,
  SMT2_TK_INVALID_BINARY,
  SMT2_TK_INVALID_SYMBOL,
  SMT2_TK_INVALID_KEYWORD,
  SMT2_TK_INVALID_BV_CONSTANT,
  SMT2_TK_ERROR,
};

typedef enum smt2_token smt2_token_t;

#define NUM_SMT2_TOKENS (SMT2_TK_ERROR+1)


/*
 * Initialization
 */
extern int32_t init_smt2_file_lexer(lexer_t *lex, char *filename);

extern void init_smt2_stream_lexer(lexer_t *lex, FILE *f, char *name);

static inline void init_smt2_stdin_lexer(lexer_t *lex) {
  init_smt2_stream_lexer(lex, stdin, "stdin");
}

extern void init_smt2_string_lexer(lexer_t *lex, char *data, char *name);


/*
 * Select built-in symbols for logic
 */
extern void smt2_lexer_activate_logic(smt_logic_t logic);


/*
 * Conversion from an SMT token to a string
 */
extern char *smt2_token_to_string(smt2_token_t tk);


/*
 * Read next token and return its type
 * - update lex->token (set it to tk)
 * - update lex->tk_pos, tk_line, tk_pos (to the start of token
 *   in the input stream)
 * - for any token other than '(', ')', EOF, or SMT2_TK_ERROR, the 
 *   token value is stored in lex->buffer (as a character string).
 */
extern smt2_token_t next_smt2_token(lexer_t *lex);


#endif /* __SMT2_LEXER_H */
