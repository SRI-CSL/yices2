/*
 * SUPPORT FOR STORING SMT2 ABSTRACT SYNTAX TREES
 */

#include <string.h>

#include "memalloc.h"
#include "smt2_ast.h"


/*
 * Initialize store
 */
void init_ast_store(ast_store_t *store) {
  store->tk = NULL;
  store->size = 0;
  store->top = 0;
  store->last_open = -1;
  store->free = 0;
  store->mem = NULL;
}


/*
 * Delete all blocks started from blk
 */
static void free_cblocks(cblock_t *blk) {
  cblock_t *p;

  while (blk != NULL) {
    p = blk->h.pre;
    safe_free(blk);
    blk = p;
  }
}

/*
 * Delete all blocks and the token array
 */
void delete_ast_store(ast_store_t *store) {
  safe_free(store->tk);
  free_cblocks(store->mem);
  store->tk = NULL;
  store->mem = NULL;
}


/*
 * Remove all tokens and delete all blocks except the current
 * store->mem.
 */
void reset_ast_store(ast_store_t *store) {  
  cblock_t *p;

  store->top = 0;
  store->last_open = -1;
  p = store->mem;
  if (p != NULL) {  
    store->free = DEF_CBLOCK_SIZE;
    free_cblocks(p->h.pre);
    p->h.pre = NULL;
  }
}



/*
 * Allocate the array tk or make it larger
 */
static void extend_ast_store(ast_store_t *store) {
  uint32_t n;

  n = store->size;
  if (n == 0) {
    n = DEF_AST_STORE_SIZE;
    store->tk = (ast_token_t *) safe_malloc(n * sizeof(ast_token));
    store->size = n;
  } else {
    n += n>>1;
    assert(n > store->size);
    if (n > MAX_AST_STORE_SIZE) {
      out_of_memory();
    }
    store->tk = (ast_token_t *) safe_realloc(store->tk, n * sizeof(ast_token));
    store->size = n;
  }
}


/*
 * Get the next token index and enlarge the store if needed
 */
static int32_t ast_store_next_idx(ast_store_t *store) {
  int32_t i;

  i = store->top;
  if (i == store->size) {
    extend_ast_store(store);
  }
  assert(i < store->size);
  store->top = i+1;

  return i;
}


/*
 * STRING ALLOCATION
 */

/*
 * Allocate a memory block of size n
 */
static cblock_t *new_cblock(uint32_t n) {
  if (n > MAX_CBLOCK_SIZE) {
    out_of_memory();
  }
  return (cblock_t *) safe_malloc(sizeof(cblock_t) + n);
}


/*
 * Add blk to the list of blocks: before the current mem
 */
static void pre_insert_cblock(ast_store_t *store, cblock_t *blk) {
  cblock_t *m;

  assert(store->mem != NULL);

  m = store->mem;
  blk->h.pre = m->h.pre;
  m->h.pre = blk;
}


/*
 * Add block blk after the current store->mem
 */
static void insert_cblock(ast_store_t *store, cblock_t *blk) {
  blk->h.pre = store->mem;
  store->mem = blk;
}


/*
 * Return a pointer to an array of n char
 * - if free counter is updated, we clear its three low-order bits
 * - this ensures that all allocated pointers are aligned on an address that's a 
 *   multiple of eight.
 */
static char *cblock_alloc(ast_store_t *store, uint32_t n) {
  cblock_t *blk;
  char *p;

  if (n <= store->free) {
    /*
     * Allocate in the current block
     */
    blk = store->mem;
    p = blk->data + (DEF_CBLOCK_SIZE - n);
    assert(blk->data <= p && p + n < blk->data + DEF_CBLOCK_SIZE);
    store->free -= n;
    store->free &= ~(uint32_t)7; 
  } else if (n <= DEF_CBLOCK_SIZE) {
    /*
     * Add a bew block
     */
    blk = new_cblock(DEF_CBLOCK_SIZE);
    p = blk->data;
    insert_cblock(store, blk);
    store->mem = blk;
    store->free = DEF_CBLOCK_SIZE - n;
    store->free &= ~(uint32_t)7;
  } else {
    /*
     * Allocate a large block
     * make sure store->mem is a standard-size block first
     */
    if (store->mem == NULL) {
      blk = new_cblock(DEF_CBLOCK_SIZE);
      blk->h.pre = NULL;
      store->mem = blk;
      store->free = DEF_CBLOCK_SIZE;
    }
    blk = new_cblock(n);
    p  = blk->data;
    pre_insert_cblock(store, blk);
  }

  return p;
}


/*
 * Make a copy of string s:
 * - n = length of s
 */
static char *ast_store_strcpy(ast_store_t *store, const char *s, uint32_t n) {
  char *p;

  if (n == UINT32_MAX)  out_of_memory();
  p = cblock_alloc(store, n + 1);
  return strncpy(p, s, n+1);
}



/*
 * TOKENS
 */

/*
 * Start a new scope
 */
void ast_store_open_scope(ast_store_t *store) {
  int32_t i;

  i = ast_store_next_idx(store);
  store->tk[i].key = -1; // scope marker
  store->tk[i].val = store->last_open;
  store->tk[i].ptr = NULL;
}


/*
 * Close the last_open scope
 */
void ast_close_open_scope(ast_store_t *store) {
  int32_t i;

  i = store->last_open;
  assert(ast_scope_is_open(store, i));
  store->last_open = store->tk[i].val;
  store->tk[i].val = store->top;
}


/*
 * Push an atomic token:
 * - key, val, str = attributes for this token
 * - len = len of the string
 * - if len is 0, str is ignored (should be NULL)
 *   we make an internal copy of str[0 ... len-1]  (with a '\0' terminator).
 */
void ast_store_push_token(ast_store_t *store, int32_t key, int32_t val, const char *str, uint32_t len) {
  char *p;
  int32_t i;

  assert(key >= 0);

  p = NULL;
  if (len > 0) {
    p = ast_store_strcpy(store, str, len);
  }

  i = ast_store_next_idx(store);
  store->tk[i].key = key;
  store->tk[i].val = val;
  store->tk[i].ptr = p;
}


/*
 * Right sibling of i
 */
int32_t ast_sibling(ast_store_t *store, int32_t i) {
  int32_t k;

  assert(good_ast_token(store, i));
  k = i+1;
  if (store->tk[i].key < 0) {
    k = store->tk[i].val;
    if (k < i) k = store->top; // i is not close yet: no sibling
  }
  return k;
}


/*
 * Collect all children of i in vector v
 * - i must be a closed scope
 * - v must be initialized and empty (if not empty, the children
 *   are added to v).
 */
void get_ast_children(ast_store_t *store, int32_t i, ivector_t *v) {
  int32_t k, n;

  assert(ast_scope_is_close(store, i));
  n = store->tk[i].val;
  k = i+1;
  while (k < n) {
    assert(good_ast_token(store, k));
    ivector_push(v, k);
    k = ast_sibling(store, k);
  }
  assert(k == n);
}
