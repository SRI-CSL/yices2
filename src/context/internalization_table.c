/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * MAPPING OF TERMS TO SOLVER OBJECTS
 */

/*
 * An internalization table keeps track of variable substitutions and
 * of the internal object (egraph term or other) mapped to terms.  The
 * table stores a partition of term indices in a union-find data
 * structure.  All the elements of an equivalence class are equal and
 * mapped to the same solver object.  Each class contains a
 * distinguished root element. All elements other than the root are
 * uninterpreted term indices (i.e., variables).
 *
 * - For a root r we store:
 *      map[r] = object mapped to the class (or NULL)
 *     type[r] = type of the class
 *     rank[r] = an 8bit value for balancing the union-find structure
 *
 *   If rank[r] is 255 then the root is frozen. This means either that
 *   r is not an uninterpreted term or that r is mapped to a non-NULL object.
 *   It's not possible to merge two classes whose roots are both frozen.
 *
 *   If rank[r] is less than 255, then the root is free. This means
 *   that r is an uninterpreted term and is not mapped to any object
 *   yet (i.e., map[r] = NULL). The class of r contains has size >=
 *   2^rank[r] and all elements in the class are uninterpreted. It's
 *   possible to merge the class of r with another class.
 *
 *   The table is a partial map. The domain is defined by the set of 
 *   terms r such that type[r] != NULL_TYPE. If type[r] is NULL_TYPE
 *   then r is considered to be a root.
 *
 * - a non-root i must be an uninterpreted term index and map[i] is the
 *   parent of i in the union-find tree.
 *
 * To distinguish between roots and non-roots, we use the sign bit:
 *   map[i] < 0  if i is a root, and the object mapped to i is obtained
 *               by clearing the sign bit.
 *   map[i] >= 0 if i is not a root, then map[i] is a term (term index + polarity bit)
 *
 * For boolean classes, the polarity bit is significant: the substitution
 * may map a boolean index 'i' to a negative term '(not t)'. Then the root
 * of 'i' is '(not t)'.
 */

#include "context/internalization_table.h"
#include "utils/memalloc.h"
#include "context/internalization_codes.h"

/*
 * Initialization:
 * - n = initial size for the arrays map, rank, type
 * - terms = attached term table
 */
void init_intern_tbl(intern_tbl_t *tbl, uint32_t n, term_table_t *terms) {
  init_int32_array(&tbl->map, NULL_MAP, n);
  init_int32_array(&tbl->type, NULL_TYPE, n);
  init_uint8_array(&tbl->rank, 0, n);

  tbl->terms = terms;
  tbl->types = terms->types;

  tbl->cache = NULL;
  tbl->queue = NULL;

  init_int_hmap(&tbl->reverse_map, 0);
}


/*
 * Delete: free all memory
 */
void delete_intern_tbl(intern_tbl_t *tbl) {
  delete_int32_array(&tbl->map);
  delete_int32_array(&tbl->type);
  delete_uint8_array(&tbl->rank);

  if (tbl->cache != NULL) {
    delete_int_hset(tbl->cache);
    safe_free(tbl->cache);
    tbl->cache = NULL;
  }

  if (tbl->queue != NULL) {
    delete_int_queue(tbl->queue);
    safe_free(tbl->queue);
    tbl->queue = NULL;
  }

  delete_int_hmap(&tbl->reverse_map);
}


/*
 * Reset to the empty table
 */
void reset_intern_tbl(intern_tbl_t *tbl) {
  reset_int32_array(&tbl->map);
  reset_int32_array(&tbl->type);
  reset_uint8_array(&tbl->rank);

  if (tbl->cache != NULL) {
    int_hset_reset(tbl->cache);
  }

  if (tbl->queue != NULL) {
    int_queue_reset(tbl->queue);
  }

  int_hmap_reset(&tbl->reverse_map);
}




/*
 * Push and pop
 */
void intern_tbl_push(intern_tbl_t *tbl) {
  int32_array_push(&tbl->map);
  int32_array_push(&tbl->type);
  uint8_array_push(&tbl->rank);
}

void intern_tbl_pop(intern_tbl_t *tbl) {
  int32_array_pop(&tbl->map);
  int32_array_pop(&tbl->type);
  uint8_array_pop(&tbl->rank);
}


#if 0
// NOT USED
/*
 * Get the internal cache.
 * Allocate and initialize it if needed.
 */
static int_hset_t *intern_tbl_get_cache(intern_tbl_t *tbl) {
  int_hset_t *tmp;

  tmp = tbl->cache;
  if (tmp == NULL) {
    tmp = (int_hset_t *) safe_malloc(sizeof(int_hset_t));
    init_int_hset(tmp, 128);
    tbl->cache = tmp;
  }
  return tmp;
}

/*
 * Same thing for the internal queue
 */
static int_queue_t *intern_tbl_get_queue(intern_tbl_t *tbl) {
  int_queue_t *tmp;

  tmp = tbl->queue;
  if (tmp == NULL) {
    tmp = (int_queue_t *) safe_malloc(sizeof(int_queue_t));
    init_int_queue(tmp, 100);
    tbl->queue = tmp;
  }
  return tmp;
}

#endif




/*
 * UNION-FIND OPERATIONS
 */

/*
 * Parent of term t in tbl
 * - return a negative number if t is a root
 */
static inline term_t intern_tbl_read_parent(intern_tbl_t *tbl, term_t t) {
  return ai32_read(&tbl->map, index_of(t)) ^ polarity_of(t);
}

static inline term_t intern_tbl_get_parent(intern_tbl_t *tbl, term_t t) {
  return ai32_get(&tbl->map, index_of(t)) ^ polarity_of(t);
}

// write p as parent of t in tbl
static inline void intern_tbl_write_parent(intern_tbl_t *tbl, term_t t, term_t p) {
  ai32_write(&tbl->map, index_of(t), p ^ polarity_of(t));
}


/*
 * Root of t's class
 * - apply path compression
 */
term_t intern_tbl_get_root(intern_tbl_t *tbl, term_t t) {
  term_t y, z;

  assert(good_term(tbl->terms, t));
  y = intern_tbl_read_parent(tbl, t);
  if (y < 0) { // t is not in the table or t is a root
    return t;
  }

  z = intern_tbl_read_parent(tbl, y);
  if (z < 0) { // y is a root: skip path compression
    return y;
  }

  // find the root: we have t --> y --> z
  do {
    y = z;
    z = intern_tbl_read_parent(tbl, y);
  } while (z >= 0);

  // path compression: we have t --> .... --> y
  // and y is the root of all terms on that path
  do {
    z = intern_tbl_get_parent(tbl, t);
    intern_tbl_write_parent(tbl, t, y);
    t = z;
  } while (t != y);

  return y;
}



/*
 * Variant: don't apply path compression
 */
term_t intern_tbl_find_root(intern_tbl_t *tbl, term_t t) {
  term_t y;

  assert(good_term(tbl->terms, t));
  y = intern_tbl_read_parent(tbl, t);
  while (y >= 0) {
    t = y;
    y = intern_tbl_read_parent(tbl, t);
  }

  return t;
}



/*
 * Add t to the union-find structure:
 * - t must be uninterpreted
 * - this creates a new singleton class with t as root
 *   and rank[t] is 0.
 */
static void partition_add(intern_tbl_t *tbl, term_t t) {
  type_t tau;

  assert(term_kind(tbl->terms, t) == UNINTERPRETED_TERM &&
         ai32_read(&tbl->map, index_of(t)) == NULL_MAP);

  tau = term_type(tbl->terms, t);
  ai32_write(&tbl->type, index_of(t), tau);
}


/*
 * Same thing but mark t as frozen
 */
static void partition_add_frozen(intern_tbl_t *tbl, term_t t) {
  type_t tau;

  assert(ai32_read(&tbl->map, index_of(t)) == NULL_MAP);

  tau = term_type(tbl->terms, t);
  ai32_write(&tbl->type, index_of(t), tau);
  au8_write(&tbl->rank, index_of(t), 255);
}


/*
 * Check whether r is a free root:
 * - r must be a root
 * - it's free if rank[r] < 255 (not frozen) or if r
 *   is not in the table and is uninterpreted.
 */
bool intern_tbl_root_is_free(intern_tbl_t *tbl, term_t r) {
  assert(intern_tbl_is_root(tbl, r));

  if (intern_tbl_term_present(tbl, r)) {
    return au8_read(&tbl->rank, index_of(r)) < 255;
  } else {
    return term_kind(tbl->terms, r) == UNINTERPRETED_TERM;
  }
}



/*
 * Merge the classes of x and y
 * - both terms must be roots, present in the table
 * - x and y must be distinct and at least one of them
 *   must be a free root
 */
static void partition_merge(intern_tbl_t *tbl, term_t x, term_t y) {
  uint8_t r_x, r_y;
  type_t tau_x, tau_y, tau;

  assert(intern_tbl_is_root(tbl, x) && intern_tbl_is_root(tbl, y) && x != y);

  tau_x = ai32_get(&tbl->type, index_of(x));
  tau_y = ai32_get(&tbl->type, index_of(y));
  assert(tau_x != NULL_TYPE && tau_y != NULL_TYPE);
  // intersection type
  tau = inf_type(tbl->types, tau_x, tau_y);
  assert(tau != NULL_TYPE);

  r_x = au8_read(&tbl->rank, index_of(x));
  r_y = au8_read(&tbl->rank, index_of(y));
  assert(r_x < 255 || r_y < 255);

  if (r_x < r_y) {
    // y stays root and is made parent of x in the union-find tree
    assert(term_kind(tbl->terms, x) == UNINTERPRETED_TERM);
    ai32_write(&tbl->map, index_of(x), (y ^ polarity_of(x)));
    // update type[y] if needed
    if (tau != tau_y) {
      ai32_write(&tbl->type, index_of(y), tau);
    }
  } else {
    // x stays root and is made parent of y in the tree
    assert(term_kind(tbl->terms, y) == UNINTERPRETED_TERM);
    ai32_write(&tbl->map, index_of(y), (x ^ polarity_of(y)));
    // update type[x] if needed
    if (tau != tau_x) {
      ai32_write(&tbl->type, index_of(x), tau);
    }
    // increase rank[x] if needed
    if (r_x == r_y) {
      assert(r_x < 254);
      au8_write(&tbl->rank, index_of(x), r_x + 1);
    }
  }
}





/*
 * INTERNALIZATION MAPPING
 */

/*
 * Type of r's class (return the type of r if r is not in tbl)
 * - r must be a root (it may have negative polarity)
 */
type_t intern_tbl_type_of_root(intern_tbl_t *tbl, term_t r) {
  type_t tau;

  assert(intern_tbl_is_root(tbl, r));

  tau = ai32_read(&tbl->type, index_of(r));
  if (tau == NULL_TYPE) {
    tau = term_type(tbl->terms, r);
  }

  return tau;
}


/*
 * Add the mapping r --> x then freeze r
 * - x must be non-negative and strictly smaller than INT32_MAX
 * - r must be a root, not mapped to anything yet, and must have positive
 *   polarity.
 */
void intern_tbl_map_root(intern_tbl_t *tbl, term_t r, int32_t x) {
  assert(0 <= x && x < INT32_MAX &&
         is_pos_term(r) && ai32_read(&tbl->map, index_of(r)) == NULL_MAP);

  // Freeze r and record its type if needed
  if (! intern_tbl_term_present(tbl, r)) {
    partition_add_frozen(tbl, r);
  } else if (au8_read(&tbl->rank, index_of(r)) < 255) {
    au8_write(&tbl->rank, index_of(r), 255);
  }

  // add the mapping
  ai32_write(&tbl->map, index_of(r), (INT32_MIN|x));

  // add reverse mapping
  int_hmap_pair_t *ip;
  ip = int_hmap_get(&tbl->reverse_map, x);
  if (ip->val < 0) {
    ip->val = r;
#if 0
    printf("  inverse-map:  mapping: ");
    print_intern_reverse(stdout, tbl, x);
#endif
  }

  assert(intern_tbl_map_of_root(tbl, r) == x &&
         intern_tbl_is_root(tbl, r) && !intern_tbl_root_is_free(tbl, r));
}


/*
 * Change the mapping of r:
 * - replace the current mapping by x
 * - r must be a root, already mapped, and with positive polarity
 */
void intern_tbl_remap_root(intern_tbl_t *tbl, term_t r, int32_t x) {
  assert(0 <= x && x < INT32_MAX && is_pos_term(r) &&
         intern_tbl_is_root(tbl, r) && intern_tbl_root_is_mapped(tbl, r));

  ai32_write(&tbl->map, index_of(r), (INT32_MIN|x));

  // add reverse mapping
  int_hmap_pair_t *ip;
  ip = int_hmap_get(&tbl->reverse_map, x);
  ip->val = r;

  assert(intern_tbl_map_of_root(tbl, r) == x);
}


/*
 * Return the term mapped to occurrence x (if any)
 */
term_t intern_tbl_reverse_map(intern_tbl_t *tbl, occ_t x) {
  int_hmap_pair_t *ip;

  ip = int_hmap_find(&tbl->reverse_map, occ2code(x));
  if (ip != NULL) return ip->val;

  ip = int_hmap_find(&tbl->reverse_map, occ2code(opposite_occ(x)));
  if (ip != NULL) return opposite_term(ip->val);

  return NULL_TERM;
}


/*
 * Return the term mapped to literal l if any
 */
term_t intern_tbl_reverse_lit_map(intern_tbl_t *tbl, literal_t l) {
  int_hmap_pair_t *ip;

  ip = int_hmap_find(&tbl->reverse_map, literal2code(l));
  if (ip != NULL) return ip->val;

  ip = int_hmap_find(&tbl->reverse_map, literal2code(not(l)));
  if (ip != NULL) return opposite_term(ip->val);

  return NULL_TERM;
}



#if 0

// NOT USED

/*
 * CYCLE DETECTION
 */

/*
 * We visit terms breadth-first to check for cycles.
 * The index of all visited terms are stored in subst->cache.
 * The terms to process are stored in subst->queue.
 */
static void bfs_visit_index(intern_tbl_t *tbl, int32_t i) {
  if (kind_for_idx(tbl->terms, i) == UNINTERPRETED_TERM) {
    // replace i by its root
    i = index_of(intern_tbl_get_root(tbl, pos_term(i)));
  }

  if (int_hset_add(tbl->cache, i)) {
    // i has not been seen before
    int_queue_push(tbl->queue, i);
  }
}

static inline void bfs_visit_term(intern_tbl_t *tbl, term_t t) {
  bfs_visit_index(tbl, index_of(t));
}

/*
 * Visit all children of composite term c
 */
static void bfs_visit_composite(intern_tbl_t *tbl, composite_term_t *c) {
  uint32_t i, n;

  n = c->arity;
  for (i=0; i<n; i++) {
    bfs_visit_term(tbl, c->arg[i]);
  }
}


/*
 * Children of polynomials and power products
 */
static void bfs_visit_pprod(intern_tbl_t *tbl, pprod_t *p) {
  uint32_t i, n;

  n = p->len;
  for (i=0; i<n; i++) {
    bfs_visit_term(tbl, p->prod[i].var);
  }
}

static void bfs_visit_poly(intern_tbl_t *tbl, polynomial_t *p) {
  monomial_t *m;
  uint32_t i, n;

  n = p->nterms;
  m = p->mono;

  // skip the constant if any
  assert(n > 0);
  if (m[0].var == const_idx) {
    m ++;
    n --;
  }

  for (i=0; i<n; i++) {
    bfs_visit_term(tbl, m[i].var);
  }
}

static void bfs_visit_bvpoly(intern_tbl_t *tbl, bvpoly_t *p) {
  bvmono_t *m;
  uint32_t i, n;

  n = p->nterms;
  m = p->mono;

  assert(n > 0);
  if (m[0].var == const_idx) {
    m ++;
    n --;
  }

  for (i=0; i<n; i++) {
    bfs_visit_term(tbl, m[i].var);
  }
}

static void bfs_visit_bvpoly64(intern_tbl_t *tbl, bvpoly64_t *p) {
  bvmono64_t *m;
  uint32_t i, n;

  m = p->mono;
  n = p->nterms;

  assert(n > 0);
  if (m[0].var == const_idx) {
    m ++;
    n --;
  }

  for (i=0; i<n; i++) {
    bfs_visit_term(tbl, m[i].var);
  }
}




/*
 * Check whether t occurs in v
 * - t must be a free root
 * - v must be a valid term
 */
static bool bfs_occurs_check(intern_tbl_t *tbl, term_t t, term_t v) {
  term_table_t *terms;
  int_queue_t *queue;
  int_hset_t *cache;
  int32_t x;
  bool found;

  assert(intern_tbl_root_is_free(tbl, t));
  assert(is_pos_term(t) && term_kind(tbl->terms, t) == UNINTERPRETED_TERM);

  terms = tbl->terms;
  queue = intern_tbl_get_queue(tbl);
  cache = intern_tbl_get_cache(tbl);

  assert(int_queue_is_empty(queue) && int_hset_is_empty(cache));

  bfs_visit_term(tbl, v);
  found = false;

  do {
    x = int_queue_pop(queue);

    switch (kind_for_idx(terms, x)) {
    case CONSTANT_TERM:
    case ARITH_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
    case VARIABLE:
      break;

    case UNINTERPRETED_TERM:
      if (x == index_of(t)) {
        // found a cycle
        found = true;
        goto done;
      }
      break;

    case ARITH_EQ_ATOM:
    case ARITH_GE_ATOM:
    case ARITH_IS_INT_ATOM:
    case ARITH_FLOOR:
    case ARITH_CEIL:
    case ARITH_ABS:
      bfs_visit_term(tbl, integer_value_for_idx(terms, x));
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
    case APP_TERM:
    case UPDATE_TERM:
    case TUPLE_TERM:
    case EQ_TERM:
    case DISTINCT_TERM:
    case FORALL_TERM:
    case LAMBDA_TERM:
    case OR_TERM:
    case XOR_TERM:
    case ARITH_BINEQ_ATOM:
    case ARITH_RDIV:
    case ARITH_IDIV:
    case ARITH_MOD:
    case ARITH_DIVIDES_ATOM:
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
      bfs_visit_composite(tbl, composite_for_idx(terms, x));
      break;

    case BIT_TERM:
    case SELECT_TERM:
      bfs_visit_term(tbl, select_for_idx(terms, x)->arg);
      break;

    case POWER_PRODUCT:
      bfs_visit_pprod(tbl, pprod_for_idx(terms, x));
      break;

    case ARITH_POLY:
      bfs_visit_poly(tbl, polynomial_for_idx(terms, x));
      break;

    case BV64_POLY:
      bfs_visit_bvpoly64(tbl, bvpoly64_for_idx(terms, x));
      break;

    case BV_POLY:
      bfs_visit_bvpoly(tbl, bvpoly_for_idx(terms, x));
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
 * Check whether the substitution [r1 := r2] is valid
 * - both r1 and r2 must be roots and they must have compatible types.
 * - r1 must have positive polarity.
 * - r2 must not be a constant term.
 * - returns true if r1 is a free root, and the substitution does not
 *   create a cycle.
 *
 * NOTE: if r2 is a constant, the next function should be used instead.
 */
bool intern_tbl_valid_subst(intern_tbl_t *tbl, term_t r1, term_t r2) {
  assert(is_pos_term(r1) &&
         intern_tbl_is_root(tbl, r1) &&
         intern_tbl_is_root(tbl, r2) &&
         !is_constant_term(tbl->terms, r2));


  return intern_tbl_root_is_free(tbl, r1) && ! bfs_occurs_check(tbl, r1, r2);
}

#endif

/*
 * Check whether the substitution [r1 := r2] is valid.
 * - r1 must be a root and r2 must be a constant
 * - r1 must have positive polarity
 * - returns true if r1 is a free root and
 *   if r2's type is a subtype of r1's class type.
 *
 * (e.g., x := 1/2 is not a valid substitution if x is an integer variable).
 */
bool intern_tbl_valid_const_subst(intern_tbl_t *tbl, term_t r1, term_t r2) {
  type_t tau1, tau2;
  bool ok;

  assert(is_pos_term(r1) &&
         intern_tbl_is_root(tbl, r1) &&
         intern_tbl_is_root(tbl, r2) &&
         is_constant_term(tbl->terms, r2));

  ok = false;

  if (intern_tbl_root_is_free(tbl, r1)) {
    tau1 = intern_tbl_type_of_root(tbl, r1);
    tau2 = intern_tbl_type_of_root(tbl, r2);
    ok = is_subtype(tbl->types, tau2, tau1);
  }

  return ok;
}


/*
 * Check whether the substitution [r1 := r2] is sound
 * - r1 must be a root
 * - r2 must be frozen
 * - returns true if r1 is a free root and r2's type is a subtype of r1's class type
 *
 * E.g., if r1 has integer type and r2 has real type then the substitution is not
 * sound.
 */
bool intern_tbl_sound_subst(intern_tbl_t *tbl, term_t r1, term_t r2) {
  type_t tau1, tau2;
  bool ok;

  assert(is_pos_term(r1) && intern_tbl_is_root(tbl, r1) && intern_tbl_is_root(tbl, r2));

  ok = false;

  if (intern_tbl_root_is_free(tbl, r1)) {
    tau1 = intern_tbl_type_of_root(tbl, r1);
    tau2 = intern_tbl_type_of_root(tbl, r2);
    ok = is_subtype(tbl->types, tau2, tau1);
  }

  return ok;
}


/*
 * Add the substitution [r1 := r2] to the table.
 * The substitution must be valid.
 */
void intern_tbl_add_subst(intern_tbl_t *tbl, term_t r1, term_t r2) {
  assert(intern_tbl_root_is_free(tbl, r1));

  if (! intern_tbl_term_present(tbl, r1)) {
    partition_add(tbl, r1);
  }

  if (! intern_tbl_term_present(tbl, r2)) {
    partition_add_frozen(tbl, r2);
  }

  partition_merge(tbl, r1, r2);
}


/*
 * Merge the classes of r1 and r2
 * - both r1 and r2 must be free roots and have compatible types
 * - if both r1 and r2 are boolean, they may have arbitrary polarity
 * This adds either the substitution [r1 := r2] or [r2 := r1]
 */
void intern_tbl_merge_classes(intern_tbl_t *tbl, term_t r1, term_t r2) {
  assert(intern_tbl_root_is_free(tbl, r1) &&
         intern_tbl_root_is_free(tbl, r2));

  if (! intern_tbl_term_present(tbl, r1)) {
    partition_add(tbl, r1);
  }

  if (! intern_tbl_term_present(tbl, r2)) {
    partition_add(tbl, r2);
  }

  partition_merge(tbl, r1, r2);
}



/*
 * SUPPORT FOR GARBAGE COLLECTION
 */

/*
 * Mark all terms and types in the domain of tbl to preserve them from
 * deletion in the next call to term_table_gc.
 *
 * Term index i is present if tbl->type[i] is not NULL_TYPE
 */
void intern_tbl_gc_mark(intern_tbl_t *tbl) {
  uint32_t i, n;
  type_t tau;

  n = tbl->type.top;
  for (i=0; i<n; i++) {
    tau = tbl->type.map[i];
    if (tau != NULL_TYPE) {
      term_table_set_gc_mark(tbl->terms, i);
      type_table_set_gc_mark(tbl->types, tau);
    }
  }
}


