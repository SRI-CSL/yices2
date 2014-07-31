/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Some SMT2 commands require to print SMT2 terms in the same exact
 * format as they were input. This means that we must keep track of
 * the parsed smt2 terms, and be able to pretty-print them later.
 *
 * This module is intended to do that:
 * - all we care about is that SMT2 terms are well-parenthesized
 *   expressions
 * - we keep track of a parenthesized expression as a sequence of tokens
 * - a token represents either an atomic token such as '+' 'x' '1/30'
 *   or the beginning or closing of a parenthesized sequence of tokens
 * - a sequence '( * 2 y z ) is represented by a sequence of n tokens:
 *     tk[i]   --> 'open' with val := i+5
 *     tk[i+1] --> '*'
 *     tk[i+2] --> '2'
 *     tk[i+3] --> 'y'
 *     tk[i+4] --> 'z'
 *     tk[i+5] --> 'close'
 *
 * So for an 'open' token such as tk[i] above, we keep track of the
 * matching 'close' token.
 *
 * Assuming all open parentheses are matched with a close parenthesis,
 * we can identify an expression by its start index i in the token array:
 * - if tk[i] is an 'open' token, then i is formed by all tokens
 *   in tk[i ... k] where k = tk[i].val
 * - if tk[i] is 'close' then i is not the start of a valid expression
 * - otherwise, tk[i] is an atomic expression
 *
 * The 'close' tokens are somewhat redundant but keeping them
 * explicitly simplifies pretty printing.
 */

#ifndef __PARENTHESIZED_EXPR_H
#define __PARENTHESIZED_EXPR_H

#include "utils/int_vectors.h"

#include <stdint.h>
#include <assert.h>

/*
 * Token structure:
 * - for atomic tokens:
 *   key and val can be anything as long as key >= 0
 *   ptr is either NULL or a pointer to a character string.
 * - for open tokens:
 *   key = ETK_OPEN (-1)
 *   val is the index of the matching close token
 *   ptr is NULL
 * - for close tokens
 *   key = ETK_CLOSE (-2)
 *   val is the index of the matching open token
 *   ptr is NULL
 *
 * During construction of a sequence, the val field of open
 * tokens is used to keep track of all 'open' tokens not
 * yet closed.
 */
typedef struct etoken_s {
  int32_t key;
  int32_t val;
  char *ptr;
} etoken_t;

enum {
  ETK_OPEN = -1,
  ETK_CLOSE = -2,
};

/*
 * To store copies of strings, we use a list of memory
 * blocks. Each block is a char array + a pointer to the
 * previous block. All blocks have the same default size.
 * If a string larger than this default is required, we
 * store it in its own block.
 *
 * We force data to align on a multiple of 8 (for 32bit
 * computers)
 */
typedef struct cblock_s cblock_t;

struct cblock_s {
  union {
    cblock_t *pre;
    char padding[8];
  } h;
  char data[0];
};

#define DEF_CBLOCK_SIZE 4088
#define MAX_CBLOCK_SIZE (UINT32_MAX - sizeof(cblock_t))


/*
 * Token queue
 * - tk = array of tokens
 * - size = size of this array
 * - top = index of the first free element in tk
 *   so all tokens are stored in tk[0 ... top-1]
 * - last_open = index of the rightmost open-scope token
 *   (or -1 if there's no open scope)
 * - mem = list of cblocks for copying strings
 *   mem = pointer to the last block
 * - free = free space in the last block
 *
 * When a token sequence is being built, we keep track of all open
 * tokens that have no matching close token (i.e. open scopes) by
 * using the val field:
 * - last_open = index of the last open token
 * - for any open token with no matching close: tk[i].val = the
 *   enclosing 'open' token (which is also not yet closed).
 */
typedef struct etk_queue_s {
  etoken_t *tk;
  uint32_t size;
  uint32_t top;
  int32_t last_open;
  uint32_t free;
  cblock_t *mem;
} etk_queue_t;


#define DEF_ETK_QUEUE_SIZE 200
#define MAX_ETK_QUEUE_SIZE (UINT32_MAX/sizeof(etoken_t))


/*
 * OPERATIONS
 */

/*
 * Initialize: nothing allocate yet
 */
extern void init_etk_queue(etk_queue_t *queue);

/*
 * Delete: free all memory used
 */
extern void delete_etk_queue(etk_queue_t *queue);

/*
 * Reset: remove all tokens
 * - also deleted all blocks but one
 */
extern void reset_etk_queue(etk_queue_t *queue);


/*
 * Start a new scope
 */
extern void etk_queue_open_scope(etk_queue_t *queue);


/*
 * Check whether there's an open scope: open token with no
 * matching close token yet.
 */
static inline bool etk_queue_is_open(etk_queue_t *queue) {
  return queue->last_open >= 0;
}


/*
 * Close the current scope:
 * - there must be an open scope (i.e., etk_queue_is_open(queue) must return true).
 */
extern void etk_queue_close_scope(etk_queue_t *queue);


/*
 * Push an atomic token:
 * - key, val, str = attributes for this token
 * - len = len of the string
 * - if str is NULL, it is ignored  (and len should be 0)
 * - otherwise, we make an internal copy of str[0 ... len-1]  (with a '\0' terminator).
 */
extern void etk_queue_push_token(etk_queue_t *queue, int32_t key, int32_t val, const char *str, uint32_t len);


/*
 * Check that i is a valid token
 */
static inline bool good_token(etk_queue_t *queue, int32_t i) {
  return 0 <= i && i < queue->top;
}


/*
 * Get token structure for i:
 * - warning: use with care. This pointer can become invalid if
 *   more tokens are added.
 */
static inline etoken_t *get_etoken(etk_queue_t *queue, int32_t i) {
  assert(good_token(queue, i));
  return queue->tk + i;
}


/*
 * Check token type
 */
static inline bool delimiter_token(etk_queue_t *queue, int32_t i) {
  assert(good_token(queue, i));
  return queue->tk[i].key < 0;
}

static inline bool open_token(etk_queue_t *queue, int32_t i) {
  assert(good_token(queue, i));
  return queue->tk[i].key == ETK_OPEN;
}

static inline bool close_token(etk_queue_t *queue, int32_t i) {
  assert(good_token(queue, i));
  return queue->tk[i].key == ETK_CLOSE;
}

static inline bool atomic_token(etk_queue_t *queue, int32_t i) {
  assert(good_token(queue, i));
  return queue->tk[i].key >= 0;
}



/*
 * Check whether the scope that starts with i is open or close
 * - i must be an 'open' token
 * - the scope is closed if tk[i].val > i
 * - it's open if tk[i].val < i
 */
static inline bool etk_scope_is_open(etk_queue_t *queue, int32_t i) {
  assert(open_token(queue, i));
  return queue->tk[i].val < i;
}

static inline bool etk_scope_is_close(etk_queue_t *queue, int32_t i) {
  assert(open_token(queue, i));
  return queue->tk[i].val > i;
}





/*
 * Check whether i is the start of a valid expression
 * - i must either be an atomic token or the opening
 *   token for a closed scope.
 */
extern bool start_token(etk_queue_t *queue, int32_t i);


/*
 * Right sibling of an expression i:
 * - i must be a start token
 * - if i is atomic, return i+1
 *   if i is an open token, return the index of the
 *   token that follows the matching close token.
 */
extern int32_t token_sibling(etk_queue_t *queue, int32_t i);


/*
 * Collect all subexpressions of i in vector v
 * - i must be the start of a valid expression
 * - if i is the start of ( <sub_1> ... <sub_n> )
 *   then the start indices of <sub_1> ... <sub_n> are
 *   added to v
 * - v must be initialized and empty (if not empty, the children
 *   are added to v).
 */
extern void collect_subexpr(etk_queue_t *queue, int32_t i, ivector_t *v);


#endif /* __PARENTHESIZE_EXPR_H */
