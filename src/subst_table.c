/*
 * TERM SUBSTITUTION
 */

#include <assert.h>

#include "subst_table.h"


/*
 * Initialize:
 * - n = initial size of all tables (0 means use default sizes)
 * - terms = attached term table
 * - the table stores the empty substitution
 */
void init_subst_table(subst_table_t *subst, uint32_t n, term_table_t *terms) {
  init_int32_array(&subst->parent, NULL_TERM, n);
  init_int32_array(&subst->type, NULL_TYPE, n);
  init_uint8_array(&subst->rank, 0, n);
  subst->terms = terms;
  subst->types = terms->types;

  init_ivector(&subst->aux_vector, 10);
  subst->cache = NULL;
  subst->queue = NULL;
}


/*
 * Delete: free memory
 */
void delete_subst_table(subst_table_t *subst) {
  delete_int32_array(&subst->parent);
  delete_int32_array(&subst->type);
  delete_uint8_array(&subst->rank);
  delete_ivector(&subst->aux_vector);

  if (subst->cache != NULL) {
    delete_int_hset(subst->cache);
    safe_free(subst->cache);
    subst->cache = NULL;
  }

  if (subst->queue != NULL) {
    delete_int_queue(subst->queue);
    safe_free(subst->queue);
    subst->queue = NULL;
  }
}


/*
 * Reset to the empty substitution
 */
void reset_subst_table(subst_table_t *subst) {
  reset_int32_array(&subst->parent);
  reset_int32_array(&subst->type);
  reset_uint8_array(&subst->rank);
  ivector_reset(&subst->aux_vector);
}


/*
 * Push/pop
 */
void subst_table_push(subst_table_t *subst) {
  int32_array_push(&subst->parent);
  int32_array_push(&subst->type);
  uint8_array_push(&subst->rank);  
}

void subst_table_pop(subst_table_t *subst) {
  int32_array_pop(&subst->parent);
  int32_array_pop(&subst->type);
  uint8_array_pop(&subst->rank);  
}



/*
 * Get the internal cache. 
 * Allocate and initialize it if needed.
 */
static int_hset_t *subst_get_cache(subst_table_t *subst) {
  int_hset_t *tmp;

  tmp = subst->cache;
  if (tmp == NULL) {
    tmp = (int_hset_t *) safe_malloc(sizeof(int_hset_t));
    init_int_hset(tmp, 64);
    subst->cache = tmp;
  }
  return tmp;
}


/*
 * Same thing for the internal queue
 */
static int_queue_t *subst_get_queue(subst_table_t *subst) {
  int_queue_t *tmp;

  tmp = subst->queue;
  if (tmp == NULL) {
    tmp = (int_queue_t *) safe_malloc(sizeof(int_queue_t));
    init_int_queue(tmp, 100);
    subst->queue = tmp;
  }
  return tmp;
}




/*
 * UNION-FIND OPERATIONS
 */


/*
 * Get the term mapped to t in the substitution table
 * - t must be an uninterpreted term
 * - return t if t is not present in the table
 *   return the root of t's class otherwise (which may be t itself)
 */
term_t subst_value(subst_table_t *subst, term_t t) {
  term_t y, r;

  assert(term_kind(subst->terms, t) == UNINTERPRETED_TERM);

  y = ai32_read(&subst->parent, t);
  if (y == NULL_TERM || y == t) {
    return t;
  }

  // y is t's parent. 
  // check whether it's the root of t's class
  r = ai32_get(&subst->parent, y);
  if (r == y) {
    return r;
  }

  // find the root of t's class
  do {
    y = r;
    r = ai32_get(&subst->parent, y);
  } while (r != y);


  // path compression: r is t's root
  do {
    y = ai32_get(&subst->parent, t);
    ai32_write(&subst->parent, t, r); // parent[t] := r
    t = y;
  } while (t != r);

  return r;
}


/*
 * Variant: don't apply path compression
 * Get the term mapped to t in the substitution table
 * - t must be an uninterpreted term
 * - return t if t is not present in the table
 *   return the root of t's class otherwise (which may be t itself)
 */
term_t find_subst_value(subst_table_t *subst, term_t t) {
  term_t y, r;

  assert(term_kind(subst->terms, t) == UNINTERPRETED_TERM);

  y = ai32_read(&subst->parent, t);
  if (y == NULL_TERM || y == t) {
    return t;
  }

  // find the root of t's class
  do {
    r = y;
    y = ai32_get(&subst->parent, y);
  } while (r != y);

  return r;
}


/*
 * Add t to the partition:
 * - t must not be present already and it must be UNINTERPRETED
 * - this creates a singleton class with t as unique element
 *   and with rank[t] = 0.
 */
static void partition_add(subst_table_t *subst, term_t t) {
  type_t tau;

  assert(is_pos_term(t) && 
         ai32_read(&subst->parent, t) == NULL_TERM &&
         term_kind(subst->terms, t) == UNINTERPRETED_TERM);

  tau = term_type(subst->terms, t);
  ai32_write(&subst->parent, t, t); // parent[t] := t
  ai32_write(&subst->type, t, tau); // type[t] := tau
  au8_write(&subst->rank, t, 0);  // rank[t] := 0
}


/*
 * Add t to the partition as a frozen class
 * - t must not be present already
 * - this creates a singleton class as above, but with rank[t] = 255.
 */
static void partition_add_root(subst_table_t *subst, term_t t) {
  type_t tau;

  assert(ai32_read(&subst->parent, t) == NULL_TERM);

  tau = term_type(subst->terms, t);
  ai32_write(&subst->parent, t, t); // parent[t] := t
  ai32_write(&subst->type, t, tau); // type[t] := tau
  au8_write(&subst->rank, t, 255);  // rank[t] := 255
}


/*
 * Merge the classes of x and y
 * - x and y must be two distinct roots
 * - their classes must have compatible types
 */
static void partition_merge(subst_table_t *subst, term_t x, term_t y) {
  uint8_t r_x, r_y;

  assert(subst_table_is_root(subst, x) && 
         subst_table_is_root(subst, y) && 
         term_type(subst->terms, x) == term_type(subst->terms, y) && 
         x != y); 

  r_x = au8_get(&subst->rank, x);
  r_y = au8_get(&subst->rank, y);

  assert(r_x < 255 || r_y < 255);
        
  if (r_x < r_y) {
    // y stays root, parent[x] := y
    ai32_write(&subst->parent, x, y);    
  } else {
    // x stays root, parent[y] := x
    ai32_write(&subst->parent, y, x);
    if (r_x == r_y) {
      au8_write(&subst->rank, x, r_x + 1);
    }
  }
}




/*
 * CYCLE DETECTION
 */

#ifndef NDEBUG

/*
 * Check whether t is a root or absent
 */
static bool is_pseudo_root(subst_table_t *subst, term_t t) {
  term_t y;

  assert(term_kind(subst->terms, t) == UNINTERPRETED_TERM);
  y = ai32_read(&subst->parent, t);
  return y == t || y == NULL_TERM;
}

#endif


/*
 * Add term x to queue and cache if it's not present in cache
 * - replace x by its root if x is uninterpreted
 */
static void bfs_add_term(subst_table_t *subst, term_t x) { 
  if (term_kind(subst->terms, x) == UNINTERPRETED_TERM) {
    x = subst_value(subst, x);
  }
  if (int_hset_add(subst->cache, x)) {
    int_queue_push(subst->queue, x);
  }
}


/*
 * Add children of composite terms
 */
static void bfs_add_composite(subst_table_t *subst, composite_term_t *c) {
  uint32_t i, n;

  n = c->arity;
  for (i=0; i<n; i++) {
    bfs_add_term(subst, c->arg[i]);
  }
}


/*
 * Check whether t occurs in v
 * - t must be uninterpreted and either not in the table or root of its class
 * - v must be a valid term of same type as t
 */
static bool dfs_occurs_check(subst_table_t *subst, term_t t, term_t v) {
  term_table_t *terms;
  int_queue_t *queue;
  int_hset_t *cache;
  term_t x;
  bool found;

  assert(is_pseudo_root(subst, t));
  
  terms = subst->terms;
  queue = subst_get_queue(subst);
  cache = subst_get_cache(subst);

  assert(int_queue_is_empty(queue) && int_hset_is_empty(cache));

  int_queue_push(queue, v);
  int_hset_add(cache, v);
  found = false;

  do {
    x = int_queue_pop(queue);
    switch (term_kind(terms, x)) {
    case CONSTANT_TERM:
    case ARITH_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
    case VARIABLE:
      break;

    case UNINTERPRETED_TERM:
      assert(is_pseudo_root(subst, x));
      if (x == t) {
        // found a cycle
        found = true;
        goto done;
      }
      break;

    case ARITH_EQ_ATOM:
    case ARITH_GE_ATOM:
      bfs_add_term(subst, arith_atom_arg(terms, x));
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
    case APP_TERM:
    case UPDATE_TERM:
    case TUPLE_TERM:
    case EQ_TERM:
    case DISTINCT_TERM:
    case FORALL_TERM:
    case OR_TERM:
    case XOR_TERM:
    case ARITH_BINEQ_ATOM:
    case BV_ARRAY:
    case BV_DIV:
    case BV_REM:
    case BV_SDIV:
    case BV_SREM:
    case BV_SMOD:
    case BV_SHL:
    case BV_LSHR:
    case BV_ASHR:
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM:
      bfs_add_composite(subst, composite_term_desc(terms, x));
      break;

    case SELECT_TERM:
      bfs_add_term(subst, select_term_arg(terms, x));
      break;

    case BIT_TERM:
      bfs_add_term(subst, bit_term_arg(terms, x));
      break;

    case POWER_PRODUCT:
    case ARITH_POLY:
    case BV64_POLY:
    case BV_POLY:
      break;
      
    default:
      assert(false);
      abort();
      break;
    }

  } while (! int_queue_is_empty(queue));

 done:
  int_hset_reset(cache);
  int_queue_reset(queue);

  return found;
}


/*
 * Check whether the substitution [t := v] is valid:
 * - t must be an uninterpreted term
 * - v must be a valid term of type compatible with t's type
 *
 * If v is an uninterpreted term then the substitution is valid if the
 * classes of t and v can be merged in the union-find structure:
 */
bool subst_is_valid(subst_table_t *subst, term_t t, term_t v) {  
  term_t r;

  assert(term_kind(subst->terms, t) == UNINTERPRETED_TERM);

  r = subst_value(subst, t);
  if (term_kind(subst->terms, r) != UNINTERPRETED_TERM) {  
    // there's already a substitution [ t := r]
    // and r is not a variable
    return false;
  }

  if (term_kind(subst->terms, v) == UNINTERPRETED_TERM) {
    v = subst_value(subst, v);
  }

  switch (term_kind(subst->terms, v)) {
  case CONSTANT_TERM:
  case ARITH_CONSTANT:
  case BV64_CONSTANT:
  case BV_CONSTANT:
    return true;

  case UNINTERPRETED_TERM:
    assert(is_pseudo_root(subst, v));
    return true;

  default:
    return ! dfs_occurs_check(subst, r, v);
  }
}


/*
 * Add the substitution [t := v] to the table.
 * - t must be uninterpreted
 * - v must be a valid term of type compatible with t's type.
 * - the substitution must be valid.
 */
void subst_table_add(subst_table_t *subst, term_t t, term_t v) {
  assert(subst_is_valid(subst, t, v));

  if (ai32_read(&subst->parent, t) == NULL_TERM) {
    partition_add(subst, t);
  }
  assert(subst_table_is_root(subst, t));

  if (ai32_read(&subst->parent, v) == NULL_TERM) {
    partition_add_root(subst, v);
  }

  if (v != t) {
    assert(subst_table_is_root(subst, v) && au8_get(&subst->rank, v) == 255);
    partition_merge(subst, t, v);
  }
}


/*
 * Merge the classes of t and v:
 * - both must be uninterpreted and either root of their class or absent
 *   from the substitution table.
 * - this adds the substitution [t := v] or [v := t]
 */
void subst_table_merge(subst_table_t *subst, term_t t, term_t v) {
  assert(is_pseudo_root(subst, t) && is_pseudo_root(subst, v));

  if (ai32_read(&subst->parent, t) == NULL_TERM) {
    partition_add(subst, t);
  }

  if (ai32_read(&subst->parent, v) == NULL_TERM) {
    partition_add(subst, v);
  }

  if (v != t) {
    partition_merge(subst, t, v);
  }
}

