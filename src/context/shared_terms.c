/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <assert.h>

#include "context/shared_terms.h"

/*
 * Initialization:
 * - intern must be the context's internalization table
 * - the term table is extracted from intern
 */
void init_sharing_map(sharing_map_t *map, intern_tbl_t *intern) { 
  init_int_hmap(&map->hmap, 128);
  map->intern = intern;
  map->terms = intern->terms;
}

/*
 * Delete the whole thing
 */
void delete_sharing_map(sharing_map_t *map) {
  delete_int_hmap(&map->hmap);
}

/*
 * Add i to the hmap and check whether this is the first occurrence of i
 * - p = a parent of i
 * - the function returns true if this is the first occurrence of i and adds
 *   p as its parent
 * - it returns false and sets i's parent to bool_const otherwise
 */
static bool sharing_map_record_occurrence(sharing_map_t *map, int32_t i, int32_t p) {
  int_hmap_pair_t *r;

  assert(good_term_idx(map->terms, i) && good_term_idx(map->terms, p));

  r = int_hmap_get(&map->hmap, i);
  assert(r->key == i);
  if (r->val < 0) {
    // new record so this is the first occurrence of i
    r->val = p;
    return true;
  } else {
    r->val = bool_const;
    return false;
  }
}



/*
 * Recursively visit a term
 * - i = term index in map->terms
 * - p = a parent of i
 */
static void sharing_map_visit(sharing_map_t *map, int32_t i, int32_t p);


static void sharing_map_visit_composite(sharing_map_t *map, composite_term_t *c, int32_t p) {
  uint32_t i, n;

  assert(c == composite_for_idx(map->terms, p));

  n = c->arity;
  for (i=0; i<n; i++) {
    sharing_map_visit(map, index_of(c->arg[i]), p);
  }
}

static void sharing_map_visit_select(sharing_map_t *map, select_term_t *c, int32_t p) {
  assert(c == select_for_idx(map->terms, p));
  sharing_map_visit(map, index_of(c->arg), p);
}

static void sharing_map_visit_pprod(sharing_map_t *map, pprod_t *c, int32_t p) {
  uint32_t i, n;

  assert(c == pprod_for_idx(map->terms, p));

  n = c->len;
  for (i=0; i<n; i++) {
    sharing_map_visit(map, index_of(c->prod[i].var), p);
  }
}

static void sharing_map_visit_poly(sharing_map_t *map, polynomial_t *c, int32_t p) {
  uint32_t i, n;

  assert(c == polynomial_for_idx(map->terms, p));

  n = c->nterms;
  assert(n > 0);

  i = 0;
  if (c->mono[0].var == const_idx) {
    i ++; // skip the constant
  }
  while (i<n) {
    sharing_map_visit(map, index_of(c->mono[i].var), p);
    i ++;
  }  
}

static void sharing_map_visit_bvpoly64(sharing_map_t *map, bvpoly64_t *c, int32_t p) {
  uint32_t i, n;

  assert(c == bvpoly64_for_idx(map->terms, p));

  n = c->nterms;
  assert(n > 0);

  i = 0;
  if (c->mono[0].var == const_idx) {
    i ++; // skip the constant
  }
  while (i<n) {
    sharing_map_visit(map, index_of(c->mono[i].var), p);
    i ++;
  }  
}

static void sharing_map_visit_bvpoly(sharing_map_t *map, bvpoly_t *c, int32_t p) {
  uint32_t i, n;

  assert(c == bvpoly_for_idx(map->terms, p));

  n = c->nterms;
  assert(n > 0);

  i = 0;
  if (c->mono[0].var == const_idx) {
    i ++; // skip the constant
  }
  while (i<n) {
    sharing_map_visit(map, index_of(c->mono[i].var), p);
    i ++;
  }  
}

// visit all subterms of i
static void sharing_map_visit_subterms(sharing_map_t *map, int32_t i) {
  switch (kind_for_idx(map->terms, i)) {
  case CONSTANT_TERM:
  case ARITH_CONSTANT:
  case BV64_CONSTANT:
  case BV_CONSTANT:
  case VARIABLE:
  case UNINTERPRETED_TERM:
    // atomic term
    break;

  case ARITH_EQ_ATOM:
  case ARITH_GE_ATOM:
    sharing_map_visit(map, index_of(integer_value_for_idx(map->terms, i)), i);
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
    sharing_map_visit_composite(map, composite_for_idx(map->terms, i), i);
    break;

  case SELECT_TERM:
  case BIT_TERM:
    sharing_map_visit_select(map, select_for_idx(map->terms, i), i);
    break;

  case POWER_PRODUCT:
    sharing_map_visit_pprod(map, pprod_for_idx(map->terms, i), i);
    break;

  case ARITH_POLY:
    sharing_map_visit_poly(map, polynomial_for_idx(map->terms, i), i);
    break;

  case BV64_POLY:
    sharing_map_visit_bvpoly64(map, bvpoly64_for_idx(map->terms, i), i);
    break;

  case BV_POLY:
    sharing_map_visit_bvpoly(map, bvpoly_for_idx(map->terms, i), i);
    break;

  case UNUSED_TERM:
  case RESERVED_TERM:
    assert(false);
    break;
  }
}


static void sharing_map_visit(sharing_map_t *map, int32_t i, int32_t p) {
  term_t r;

  // apply term substitution
  r = intern_tbl_get_root(map->intern, pos_term(i));
  if (intern_tbl_root_is_mapped(map->intern, r)) {
    /*
     * r is already mapped so we ignore it.  The sharing data is
     * not relevant for terms that are already internaliazed.
     */
    return;
  }

  i = index_of(r);
  if (sharing_map_record_occurrence(map, i, p)) {
    // first time we visit term i
    sharing_map_visit_subterms(map, i);
  }
}


/*
 * Process term t:
 * - all subterms of t are visited recursively and added the map
 */
void sharing_map_add_term(sharing_map_t *map, term_t t) {
  sharing_map_visit_subterms(map, index_of(t));
}


/*
 * Process all terms in array a
 * - n = size of the array
 */
void sharing_map_add_terms(sharing_map_t *map, term_t *a, uint32_t n) {
  uint32_t i;
  
  for (i=0; i<n; i++) {
    sharing_map_visit_subterms(map, index_of(a[i]));
  }
}


/*
 * Check whether t occurs more that once among all the terms visited so far 
 * - this returns false if t is not in the map or if t has been seen only once
 */
bool term_is_shared(sharing_map_t *map, term_t t) {
  int_hmap_pair_t *r;
  int32_t i;

  i = index_of(t);
  assert(good_term_idx(map->terms, i));

  r = int_hmap_find(&map->hmap, i);
  return r != NULL && r->val == bool_const;
}


/*
 * Check whether t occurs once
 * - this returns false if t is not in the map or if t has been visited more than once
 */
bool term_is_unshared(sharing_map_t *map, term_t t) {
  int_hmap_pair_t *r;
  int32_t i;

  i = index_of(t);
  assert(good_term_idx(map->terms, i));

  r = int_hmap_find(&map->hmap, i);
  return r != NULL && r->val != bool_const;
}


/*
 * Get the unique parent of t
 * - if t has been seen only once, this returns t's parent as stored in map->hamp
 * - if t has not been seen at all, this returns NULL_TERM
 * - if t has more than once occurrences, this returns true_term (as a marker).
 */
term_t unique_parent(sharing_map_t *map, term_t t) {
  int_hmap_pair_t *r;
  int32_t i;
  term_t parent;

  i = index_of(t);
  assert(good_term_idx(map->terms, i));

  parent = NULL_TERM;
  r = int_hmap_find(&map->hmap, i);
  if (r != NULL) {
    assert(r->key == i);
    parent = pos_term(r->val);
  }

  return parent;
}

