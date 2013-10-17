/*
 * Some SMT2 commands require to print SMT2 terms in the same
 * exact format as they were input. This means that we must
 * keep track of the abstract syntax tree of smt2 terms,
 * and be able to pretty-print these trees later.
 *
 * This module is intended to do that:
 * - for an input SMT2 expression such as (+ x (* 2 z y) 1/30)
 * - all we care about is that this thing is a well-scoped
 *   parenthesized expression
 * - we keep track of is as a sequence of tokens
 * - a token represents either an atomic token such as '+' 'x' '1/30'
 *   or the beginning of a parenthesized sequence of tokens
 * - a sequence '( * 2 y z ) is represented by a seqeunce of n tokens:
 *     tk[i]   --> 'scope' with val := i+5 
 *     tk[i+1] --> '*'
 *     tk[i+2] --> '2'
 *     tk[i+3] --> 'y'
 *     tk[i+4] --> 'z'
 *
 * So for a 'scope' token such as tk[i] above keeps track of where the 
 * scope closes (i.e., tk[i].val is the index i+5 where the scope closes,
 * which is also where the right sibling of i starts.
 *
 * An abstract syntax tree is identified by an index i in the token array:
 * If tk[i] is not 'scope' then this 'i' is a leaf in the AST
 * If tk[i] is 'scope' token then it's an AST formed by all tokens 
 * from i+1 to tk[i].val.
 */

#ifndef __SMT2_AST_H
#define __SMT2_AST_H

#include "int_vectors.h"

#include <stdint.h>
#include <assert.h>

/*
 * Token structure:
 * - for atomic tokens: key, val, ptr shold provide enough
 *   information that we can print the token.
 *   the key should be >= 0
 * - for scope tokens: we use the reserved key -1
 *   val is the sibling/closing pointer, ptr is NULL.
 */
typedef struct ast_token_s {
  int32_t key;
  int32_t val;
  char *ptr;
} ast_token_t;


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

#define DEF_CBLOCK_SIZE 4092
#define MAX_CBLOCK_SIZE (UINT32_MAX - sizeof(cblock_t))


/*
 * ast_store:
 * - tk = array of tokens
 * - size = size of this array
 * - top = index of the first free element in tk
 *   so all tokens are stored in tk[0 ... top-1]
 * - last_open = index of the rightmost open-scope token 
 *   (or -1 if there's no open scope)
 * - mem = list of cblocks for copying strings
 *   mem = pointer to the last block
 * - free = free space in the last block 
 */
typedef struct ast_store_s {
  ast_token_t *tk;
  uint32_t size;
  uint32_t top;
  int32_t last_open;
  uint32_t free;
  cblock_t *mem;
} ast_store_t;


#define DEF_AST_STORE_SIZE 200
#define MAX_AST_STORE_SIZE (UINT32_MAX/sizeof(ast_token_t))


/*
 * OPERATIONS
 */

/*
 * Initialize: nothing allocate yet
 */
extern void init_ast_store(ast_store_t *store);

/*
 * Delete: free all memory used
 */
extern void delete_ast_store(ast_store_t *store);

/*
 * Reset: remove all tokens
 * - also deleted all blocks but one
 */
extern void reset_ast_store(ast_store_t *store);


/*
 * Start a new scope
 */
extern void ast_store_open_scope(ast_store_t *store);


/*
 * Close the current scope
 */
extern void ast_store_close_scope(ast_store_t *store);


/*
 * Push an atomic token:
 * - key, val, str = attributes for this token
 * - len = len of the string
 * - if len is 0, str is ignored (should be NULL)
 *   we make an internal copy of str[0 ... len-1]  (with a '\0' terminator).
 */
extern void ast_store_push_token(ast_store_t *store, int32_t key, int32_t val, const char *str, uint32_t len);


/*
 * Check that i is a valid token
 */
static inline bool good_ast_token(ast_store_t *store, int32_t i) {
  return 0 <= i && i < store->top;
}


/*
 * Check whether i is a scope or an atomic token
 */
static inline bool ast_token_is_scope(ast_store_t *store, int32_t i) {
  assert(good_ast_token(store, i));
  return store->tk[i].key < 0;
}

static inline bool ast_token_is_atomic(ast_store_t *store, int32_t i) {
  assert(good_ast_token(store, i));
  return store->tk[i].key >= 0;
}


/*
 * Check whether scope that start with i is open or close
 * - for an open scope, we have tk[i] = index of the enclosing close so that's less than i
 * - for a close scope, we have tk[i] >= i
 */
static inline bool ast_scope_is_open(ast_store_t *store, int32_t i) {
  assert(ast_token_is_scope(store, i));
  return store->tk[i].val < i;
}

static inline bool ast_scope_is_close(ast_store_t *store, int32_t i) {
  assert(ast_token_is_scope(store, i));
  return store->tk[i].val >= i;
}

/*
 * Get token i:
 * - warning: use with care. This pointer can become invalid if 
 *   more tokens are added.
 */
static inline ast_token_t *ast_token(ast_store_t *store, int32_t i) {
  assert(good_ast_token(store, i));
  return store->tk + i;
}


/*
 * Right sibling of i: i must be a good token
 * - return store->top i has no right sibling
 */
extern int32_t ast_sibling(ast_store_t *store, int32_t i);


/*
 * Collect all children of i in vector v
 * - i must be a closed scope
 * - v must be initialized and empty (if not empty, the children
 *   are added to v).
 */
extern void get_ast_children(ast_store_t *store, int32_t i, ivector_t *v);


#endif /* __SMT2_AST_H */
