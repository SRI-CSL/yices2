/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Generic parser operations. This provides utilities for constructing
 * recursive descent parsers. We use this somewhat complicated approach
 * to avoid issues with stack overflow that can be caused by deeply
 * nested formulas (especially in the SMT-LIB benchmarks).
 *
 * The same data structure should work for both the SMT-LIB and Yices languages.
 */

#ifndef __PARSER_H
#define __PARSER_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "parser_utils/lexer.h"
#include "parser_utils/term_stack2.h"


/*
 * Control states are assumed to fit in 8bits
 */
typedef uint8_t parser_state_t;


/*
 * Stack of states
 */
typedef struct parser_stack_s {
  parser_state_t *data;
  uint32_t top;
  uint32_t size;
} parser_stack_t;


#define DEFAULT_PARSER_STACK_SIZE 500
#define MAX_PARSER_STACK_SIZE (UINT32_MAX/sizeof(parser_state_t))


/*
 * Parser components:
 * - a lexer
 * - a term stack (for building terms)
 * - a stack of control states
 */
typedef struct parser_s {
  parser_stack_t pstack;
  lexer_t *lex;
  tstack_t *tstack;
} parser_t;


/*
 * Initialization:
 * - use lex and tstack for lexer and term stack (they must be initialized
 *   outside this function).
 */
extern void init_parser(parser_t *parser, lexer_t *lex, tstack_t *tstack);


/*
 * Delete: frees the state stack.
 * - lex and tstack must be deleted outside this function.
 */
extern void delete_parser(parser_t *parser);


/*
 * Start parsing from file:
 * - allocate and initialize a new lexer for that file
 * - input is read from that lexer until parser_pop_lexer is called.
 * - return a negative number if there's an error opening the file.
 * - return 0 otherwise
 */
extern int32_t parser_push_lexer(parser_t *parser, const char *filename);


/*
 * Close the top-level lexer and restore the previous lexer
 * - there must be a matching push_lexer call
 */
extern void parser_pop_lexer(parser_t *parser);



/*
 * Stack operations.
 */
extern void parser_push_state(parser_stack_t *stack, parser_state_t s);

// remove top state and return it. Fails if the stack is empty.
extern parser_state_t parser_pop_state(parser_stack_t *stack);

static inline bool parser_stack_is_empty(parser_stack_t *stack) {
  return stack->top == 0;
}

static inline void parser_stack_reset(parser_stack_t *stack) {
  stack->top = 0;
}


#endif /* __PARSER_H */
