/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SUPPORT FOR STORING SMT2 ABSTRACT SYNTAX TREES
 */

#include <string.h>

#include "frontend/smt2/parenthesized_expr.h"
#include "utils/memalloc.h"


/*
 * Initialize queue
 */
void init_etk_queue(etk_queue_t *queue) {
  queue->tk = NULL;
  queue->size = 0;
  queue->top = 0;
  queue->last_open = -1;
  queue->free = 0;
  queue->mem = NULL;
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
void delete_etk_queue(etk_queue_t *queue) {
  safe_free(queue->tk);
  free_cblocks(queue->mem);
  queue->tk = NULL;
  queue->mem = NULL;
}


/*
 * Remove all tokens and delete all blocks except the current
 * queue->mem.
 */
void reset_etk_queue(etk_queue_t *queue) {
  cblock_t *p;

  queue->top = 0;
  queue->last_open = -1;
  p = queue->mem;
  if (p != NULL) {
    queue->free = DEF_CBLOCK_SIZE;
    free_cblocks(p->h.pre);
    p->h.pre = NULL;
  }
}



/*
 * Allocate the array tk or make it larger
 */
static void extend_etk_queue(etk_queue_t *queue) {
  uint32_t n;

  n = queue->size;
  if (n == 0) {
    n = DEF_ETK_QUEUE_SIZE;
    queue->tk = (etoken_t *) safe_malloc(n * sizeof(etoken_t));
    queue->size = n;
  } else {
    n += n>>1;
    assert(n > queue->size);
    if (n > MAX_ETK_QUEUE_SIZE) {
      out_of_memory();
    }
    queue->tk = (etoken_t *) safe_realloc(queue->tk, n * sizeof(etoken_t));
    queue->size = n;
  }
}


/*
 * Get the next token index and enlarge the queue if needed
 */
static int32_t etk_queue_next_idx(etk_queue_t *queue) {
  int32_t i;

  i = queue->top;
  if (i == queue->size) {
    extend_etk_queue(queue);
  }
  assert(i < queue->size);
  queue->top = i+1;

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
static void pre_insert_cblock(etk_queue_t *queue, cblock_t *blk) {
  cblock_t *m;

  assert(queue->mem != NULL);

  m = queue->mem;
  blk->h.pre = m->h.pre;
  m->h.pre = blk;
}


/*
 * Add block blk after the current queue->mem
 */
static void insert_cblock(etk_queue_t *queue, cblock_t *blk) {
  blk->h.pre = queue->mem;
  queue->mem = blk;
}


/*
 * Return a pointer to an array of n char
 * - if free counter is updated, we clear its three low-order bits
 * - this ensures that all allocated pointers are aligned on an address that's a
 *   multiple of eight.
 */
static char *cblock_alloc(etk_queue_t *queue, uint32_t n) {
  cblock_t *blk;
  char *p;

  if (n <= queue->free) {
    /*
     * Allocate in the current block
     */
    blk = queue->mem;
    p = blk->data + (DEF_CBLOCK_SIZE - queue->free);
    assert(blk->data <= p && p + n <= blk->data + DEF_CBLOCK_SIZE);
    queue->free -= n;
    queue->free &= ~(uint32_t)7;
  } else if (n <= DEF_CBLOCK_SIZE) {
    /*
     * Add a new block
     */
    blk = new_cblock(DEF_CBLOCK_SIZE);
    p = blk->data;
    insert_cblock(queue, blk);
    queue->mem = blk;
    queue->free = DEF_CBLOCK_SIZE - n;
    queue->free &= ~(uint32_t)7;
  } else {
    /*
     * Allocate a large block
     * make sure queue->mem is a standard-size block first
     */
    if (queue->mem == NULL) {
      blk = new_cblock(DEF_CBLOCK_SIZE);
      blk->h.pre = NULL;
      queue->mem = blk;
      queue->free = DEF_CBLOCK_SIZE;
    }
    blk = new_cblock(n);
    p  = blk->data;
    pre_insert_cblock(queue, blk);
  }

  return p;
}


/*
 * Make a copy of string s:
 * - n = length of s
 */
static char *etk_queue_strcpy(etk_queue_t *queue, const char *s, uint32_t n) {
  char *p;

  if (n == UINT32_MAX)  out_of_memory();
  p = cblock_alloc(queue, n + 1);
  return strncpy(p, s, n+1);
}



/*
 * TOKENS
 */

/*
 * Start a new scope
 */
void etk_queue_open_scope(etk_queue_t *queue) {
  int32_t i;

  i = etk_queue_next_idx(queue);
  queue->tk[i].key = ETK_OPEN;
  queue->tk[i].val = queue->last_open;
  queue->tk[i].ptr = NULL;

  queue->last_open = i;
}


/*
 * Close the last_open scope
 */
void etk_queue_close_scope(etk_queue_t *queue) {
  int32_t i, j;

  i = queue->last_open;
  assert(etk_scope_is_open(queue, i));

  j = etk_queue_next_idx(queue);
  queue->tk[j].key = ETK_CLOSE;
  queue->tk[j].val = i; // matching open token
  queue->tk[j].ptr = NULL;

  queue->last_open = queue->tk[i].val;
  queue->tk[i].val = j;
}


/*
 * Push an atomic token:
 * - key, val, str = attributes for this token
 * - len = len of the string
 * - if len is 0, str is ignored (should be NULL)
 *   we make an internal copy of str[0 ... len-1]  (with a '\0' terminator).
 */
void etk_queue_push_token(etk_queue_t *queue, int32_t key, int32_t val, const char *str, uint32_t len) {
  char *p;
  int32_t i;

  assert(key >= 0);

  p = NULL;
  if (str != NULL) {
    p = etk_queue_strcpy(queue, str, len);
  }

  i = etk_queue_next_idx(queue);
  queue->tk[i].key = key;
  queue->tk[i].val = val;
  queue->tk[i].ptr = p;
}


/*
 * Check whether i is the start of a valid expression
 * - i must either be an atomic token or the opening
 *   token for a closed scope.
 */
bool start_token(etk_queue_t *queue, int32_t i) {
  etoken_t *token;

  assert(good_token(queue, i));
  token = queue->tk + i;
  return token->key >= 0 || (token->key == ETK_OPEN && token->val > i);
}


/*
 * Right sibling of i
 */
int32_t token_sibling(etk_queue_t *queue, int32_t i) {
  int32_t k;

  assert(start_token(queue, i));

  k = i+1;
  if (queue->tk[i].key < 0) {
    assert(queue->tk[i].key == ETK_OPEN && queue->tk[i].val > i);
    k = queue->tk[i].val + 1;
  }
  return k;
}


/*
 * Collect all children of i in vector v
 * - i must be the start of a valid expression
 * - v must be initialized and empty (if not empty, the children
 *   are added to v).
 */
void collect_subexpr(etk_queue_t *queue, int32_t i, ivector_t *v) {
  int32_t k, n;

  assert(start_token(queue, i));
  if (queue->tk[i].key == ETK_OPEN) {
    n = queue->tk[i].val;
    k = i+1;
    while (k < n) {
      assert(good_token(queue, k));
      ivector_push(v, k);
      k = token_sibling(queue, k);
    }
    assert(k == n);
  }
}
