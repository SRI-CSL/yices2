/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Generic parser operations. This provides utilities for constructing
 * recursive descent parsers. We use this somewhat complicated approach
 * to avoid issues with stack-overflow that can be caused by deeply
 * nested formulas (especially in the SMT-LIB benchmarks).
 *
 * The same data structure should work for both the SMT-LIB and Yices
 * languages.
 */

#include <assert.h>

#include "parser_utils/parser.h"
#include "utils/memalloc.h"



/*
 * Stack operations
 */
static void init_parser_stack(parser_stack_t *stack, uint32_t size) {
  if (size >= MAX_PARSER_STACK_SIZE) {
    out_of_memory();
  }

  stack->data = (parser_state_t *) safe_malloc(size * sizeof(parser_state_t));
  stack->top = 0;
  stack->size = size;
}

static void delete_parser_stack(parser_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
  stack->top = 0;
  stack->size = 0;
}

static void parser_stack_extend(parser_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += (n >> 1); // make it 50% larger

  if (n >= MAX_PARSER_STACK_SIZE) {
    out_of_memory();
  }

  stack->data = (parser_state_t *) safe_realloc(stack->data, n * sizeof(parser_state_t));
  stack->size = n;
}

extern void parser_push_state(parser_stack_t *stack, parser_state_t s) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    parser_stack_extend(stack);
  }
  assert(i < stack->size);
  stack->data[i] = s;
  stack->top = i+1;
}

// remove top state and return it. Fails if the stack is empty.
extern parser_state_t parser_pop_state(parser_stack_t *stack) {
  uint32_t i;

  i = stack->top;
  assert(i > 0);
  i --;
  stack->top = i;
  return stack->data[i];
}



/*
 * Nested parsing
 */

/*
 * Start parsing from file:
 * - allocate and initialize a new lexer for that file
 * - all input is read from that lexer until parser_pop_lexer is called.
 * - return a negative number if there's an error opening the file.
 * - return 0 otherwise
 */
int32_t parser_push_lexer(parser_t *parser, const char *filename) {
  lexer_t *new_lexer;
  int32_t code;

  new_lexer = (lexer_t *) safe_malloc(sizeof(lexer_t));
  code = init_nested_lexer(new_lexer, filename, parser->lex);
  if (code >= 0) {
    // no error
    parser->lex = new_lexer;
  } else {
    // cleanup
    safe_free(new_lexer);
  }

  return code;
}


/*
 * Remove the top-level lexer and the previous one.
 */
void parser_pop_lexer(parser_t *parser) {
  lexer_t *top_lexer;

  // there must be a previous one
  top_lexer = parser->lex;
  assert(top_lexer->next != NULL);
  parser->lex = top_lexer->next;
  close_lexer(top_lexer);
  safe_free(top_lexer);
}


/*
 * Remove all lexers until we reach the bottom one.
 */
static void parser_pop_all_lexers(parser_t *parser) {
  lexer_t *top, *next;

  top = parser->lex;
  next = top->next;
  while (next != NULL) {
    close_lexer(top);
    safe_free(top);
    top = next;
    next = top->next;
  }
  assert(top != NULL);
  parser->lex = top;
}


/*
 * Initialize/delete parser
 */
void init_parser(parser_t *parser, lexer_t *lex, tstack_t *tstack) {
  init_parser_stack(&parser->pstack, DEFAULT_PARSER_STACK_SIZE);
  parser->lex = lex;
  parser->tstack = tstack;
}

void delete_parser(parser_t *parser) {
  delete_parser_stack(&parser->pstack);
  parser_pop_all_lexers(parser);
  parser->lex = NULL;
  parser->tstack = NULL;
}




