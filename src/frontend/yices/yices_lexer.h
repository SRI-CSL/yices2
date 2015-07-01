/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Lexer for Yices language with support for EF-solver
 * - separators are ( ) : and spaces
 *
 * - strings are delimited by " with escaped char \n, \t, etc. allowed
 *
 * - two kinds of numeric literals are recognized
 *     TK_NUM_RATIONAL:  <optional_sign><digits>/<digits>
 *                    or <optional_sign><digits>
 *     TK_NUM_FLOAT:
 *       <optional_sign> <digits> . <digits>
 *       <optional_sign> <digits> <exp> <optional_sign> <digits>
 *       <optional_sign> <digits> . <digits> <exp> <optional_sign> <digits>
 *
 *   (the two formats recognized by string-to-rational conversions in rational.c)
 *
 * - bit-vector literals are written 0b<binary digits> (cf. bv_constants.c)
 *   or 0x<hexa digits>
 *
 * - comments start with ; and extend to the end of the line
 *
 * 2013/12/12: added ef-solve token
 * 2014/03: added export-to-dimancs and show-implicants
 */

#ifndef __YICES_LEXER_H
#define __YICES_LEXER_H

#include "parser_utils/lexer.h"


/*
 * Tokens
 */
enum yices_token {
  // commands
  TK_DEFINE_TYPE, TK_DEFINE, TK_ASSERT, TK_CHECK,
  TK_PUSH, TK_POP, TK_RESET, TK_DUMP_CONTEXT, TK_EXIT,
  TK_ECHO, TK_INCLUDE, TK_SHOW_MODEL, TK_EVAL, TK_SET_PARAM,
  TK_SHOW_PARAM, TK_SHOW_PARAMS, TK_SHOW_STATS, TK_RESET_STATS,
  TK_SET_TIMEOUT, TK_SHOW_TIMEOUT, TK_HELP, TK_EF_SOLVE,
  TK_EXPORT_TO_DIMACS, TK_SHOW_IMPLICANT,

  // term constructors
  TK_UPDATE, TK_FORALL, TK_EXISTS, TK_LAMBDA, TK_LET,

  // separators and end-of-stream
  TK_LP, TK_RP, TK_COLON_COLON, TK_EOS,

  // literals
  TK_STRING, TK_NUM_RATIONAL, TK_NUM_FLOAT, TK_BV_CONSTANT, TK_HEX_CONSTANT,

  // any symbol that's not a keyword
  TK_SYMBOL,

  // type keywords
  TK_BOOL, TK_INT, TK_REAL, TK_BITVECTOR, TK_SCALAR, TK_TUPLE, TK_ARROW,

  // term keywords
  TK_TRUE, TK_FALSE, TK_IF, TK_ITE, TK_EQ, TK_DISEQ, TK_DISTINCT,
  TK_OR, TK_AND, TK_NOT, TK_XOR, TK_IFF, TK_IMPLIES, TK_MK_TUPLE,
  TK_SELECT, TK_UPDATE_TUPLE,

  // arithmetic keywords
  TK_ADD, TK_SUB, TK_MUL, TK_DIV, TK_POW, TK_LT, TK_LE, TK_GT, TK_GE,

  // bitvector keywords
  TK_MK_BV, TK_BV_ADD, TK_BV_SUB, TK_BV_MUL, TK_BV_NEG, TK_BV_POW,
  TK_BV_NOT, TK_BV_AND, TK_BV_OR, TK_BV_XOR, TK_BV_NAND, TK_BV_NOR, TK_BV_XNOR,

  TK_BV_SHIFT_LEFT0, TK_BV_SHIFT_LEFT1, TK_BV_SHIFT_RIGHT0,
  TK_BV_SHIFT_RIGHT1, TK_BV_ASHIFT_RIGHT, TK_BV_ROTATE_LEFT, TK_BV_ROTATE_RIGHT,
  TK_BV_EXTRACT, TK_BV_CONCAT, TK_BV_REPEAT,
  TK_BV_SIGN_EXTEND, TK_BV_ZERO_EXTEND,
  TK_BV_GE, TK_BV_GT, TK_BV_LE, TK_BV_LT,
  TK_BV_SGE, TK_BV_SGT, TK_BV_SLE, TK_BV_SLT,

  // more bitvector operators
  TK_BV_SHL, TK_BV_LSHR, TK_BV_ASHR,
  TK_BV_DIV, TK_BV_REM, TK_BV_SDIV, TK_BV_SREM, TK_BV_SMOD,
  TK_BV_REDOR, TK_BV_REDAND, TK_BV_COMP,

  // conversions between bitvectors and Booleans
  TK_BOOL_TO_BV, TK_BIT,

  // more arithmetic functions (inherited from SMT-LIB2 Ints theory)
  TK_FLOOR, TK_CEIL, TK_ABS, TK_IDIV, TK_MOD, TK_DIVIDES, TK_IS_INT, 

  // unrecognized tokens or other errors
  TK_OPEN_STRING, TK_EMPTY_BVCONST, TK_EMPTY_HEXCONST,
  TK_INVALID_NUM, TK_ZERO_DIVISOR, TK_ERROR,
};

#define NUM_YICES_TOKENS (TK_ERROR+1)

typedef enum yices_token yices_token_t;


/*
 * Lexer initialization:
 * - for file_lexer, return code 0 means OK, negative code means error
 *   (can't open the file).
 */
extern int32_t init_yices_file_lexer(lexer_t *lex, char *filename);

extern void init_yices_stream_lexer(lexer_t *lex, FILE *f, char *name);

static inline void init_yices_stdin_lexer(lexer_t *lex) {
  init_yices_stream_lexer(lex, stdin, "stdin");
}

extern void init_yices_string_lexer(lexer_t *lex, char *data, char *name);



/*
 * Conversion from a token type to a string.
 * The internal table is initialized by one of the
 * init_yices_lexer functions. This function should not be
 * called before the init function.
 */
extern char *yices_token_to_string(yices_token_t tk);


/*
 * Read next token and return its type tk
 * - set lex->token to tk
 * - set lex->tk_pos, etc.
 * - if token is TK_STRING, TK_NUM_RATIONAL, TK_NUM_FLOAT,
 *   TK_BV_CONSTANT, TK_SYMBOL, or TK_ERROR,
 * the token value is set in lex->buffer.
 */
extern yices_token_t next_yices_token(lexer_t *lex);




#endif /* __YICE_LEXER_H */
