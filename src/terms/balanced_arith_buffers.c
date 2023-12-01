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
 * BUFFER FOR ARITHMETIC OPERATIONS USING RED-BLACK TREES
 */

#include "terms/balanced_arith_buffers.h"
#include "utils/bit_tricks.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"


/*
 * TREE MANIPULATIONS
 */

/*
 * When performing some operation f on the monomials stored in b, we
 * can either do a linear scan
 *
 *    for (i=1; i<b->num_nodes; i++) {
 *      f(b->mono + i)
 *    }
 *
 * or we can traverse the tree using a recursive function.
 *
 * Linear scan has a cost linear in num_nodes.
 *
 * Tree traversal has cost K * nterms * log(nterms) (approximately)
 * for some constant K>1.
 *
 * In most cases, the linear scan should be faster. We use a recursive
 * scan if num_terms is really small compared to num_nodes. The
 * following function is a heuristic that attempts to determine when
 * tree traversal is cheaper than linear scan.
 */
static bool rba_tree_is_small(const rba_buffer_t *b) {
  uint32_t n, p;

  n = b->nterms;
  p = b->num_nodes;
  return n * binlog(n) < (p >> 3);
}


/*
 * Left-most and right-most leaves of the subtree rooted at i
 * - special case: return null if i is null
 */
static uint32_t leftmost_leaf(const rba_buffer_t *b, uint32_t i) {
  uint32_t j;

  for (;;) {
    assert(0 <= i && i < b->num_nodes);
    j = b->child[i][0];
    if (j == rba_null) break;
    i = j;
  }
  return i;
}

static uint32_t rightmost_leaf(const rba_buffer_t *b, uint32_t i) {
  uint32_t j;

  for (;;) {
    assert(0 <= i && i < b->num_nodes);
    j = b->child[i][1];
    if (j == rba_null) break;
    i = j;
  }
  return i;
}


/*
 * Index of the main monomial (or null if the tree is empty)
 */
static inline uint32_t rba_main_idx(const rba_buffer_t *b) {
  return rightmost_leaf(b, b->root);
}


/*
 * Index of the smallest monomial (or null if the tree is empty)
 */
static inline uint32_t rba_smallest_idx(const rba_buffer_t *b) {
  return leftmost_leaf(b, b->root);
}


/*
 * Search for a node whose prod is equal to r
 * - return its index or rba_null if there's no such node
 */
uint32_t rba_find_node(rba_buffer_t *b, pprod_t *r) {
  uint32_t i, k;

  // to force termination: store r in the null node
  b->mono[0].prod = r;

  i = b->root;
  while (b->mono[i].prod != r) {
    k = pprod_precedes(b->mono[i].prod, r);
    assert(k <= 1);
    i = b->child[i][k];
  }

  return i;
}


/*
 * Check whether p is parent of q
 * - both must be valid node indices
 */
#ifndef NDEBUG
static inline bool is_parent_node(rba_buffer_t *b, uint32_t p, uint32_t q) {
  assert(p < b->num_nodes && q < b->num_nodes);
  return b->child[p][0] == q || b->child[p][1] == q;
}
#endif

/*
 * Child-index(p, q):
 * - q must be a child of node p
 * - returns 0 if q is the left child
 *   returns 1 if q is the right child
 * So i = child_index(b, p, q) implies b->child[p][i] = q
 */
static inline uint32_t child_index(rba_buffer_t *b, uint32_t p, uint32_t q) {
  assert(is_parent_node(b, p, q));
  return b->child[p][1] == q;
}


/*
 * Get sibling of q in p
 * - both p and q must be valid node indices
 * - q must be a child of p
 */
static inline uint32_t sibling(rba_buffer_t *b, uint32_t p, uint32_t q) {
  assert(is_parent_node(b, p, q));
  return (b->child[p][0] ^ b->child[p][1]) ^ q;
}


/*
 * Check color of node p
 */
static inline bool is_red(rba_buffer_t *b, uint32_t p) {
  assert(p < b->num_nodes);
  return tst_bit(b->isred, p);
}

static inline bool is_black(rba_buffer_t *b, uint32_t p) {
  return ! is_red(b, p);
}


/*
 * Set the color of node p
 */
static inline void mark_red(rba_buffer_t *b, uint32_t p) {
  assert(0 < p && p < b->num_nodes); // the null_node must always be black
  set_bit(b->isred, p);
}

static inline void mark_black(rba_buffer_t *b, uint32_t p) {
  assert(p < b->num_nodes);
  clr_bit(b->isred, p);
}

// make p the same color as q
static inline void copy_color(rba_buffer_t *b, uint32_t p, uint32_t q) {
  assert(p < b->num_nodes && q < b->num_nodes);
  assign_bit(b->isred, p, is_red(b, q));
}



/*
 * Fix child links in p's parent after a rotation
 * - p is now a child of q so p's parent must be updated to point to q
 * - p's parent must be the last element of b->stack
 */
static void fix_parent(rba_buffer_t *b, uint32_t p, uint32_t q) {
  uint32_t r;
  uint32_t i;

  r = ivector_last(&b->stack);
  if (r == rba_null) {
    assert(b->root == p);
    b->root = q;
  } else {
    i = child_index(b, r, p);
    b->child[r][i] = q;
  }
}


/*
 * Balance the tree after adding a node
 * - p = new node just added (must be red)
 * - q = parent of p
 * - b->stack must contains [rba_null, root, ..., r],
 *   which describes a path form the root to r where r = parent of q.
 * - the root must be black
 */
static void rba_balance_after_add(rba_buffer_t *b, uint32_t p, uint32_t q) {
  uint32_t r, s;
  uint32_t i, j;

  assert(is_parent_node(b, q, p) && is_red(b, p) && is_black(b, b->root));

  while (is_red(b, q)) {
    r = ivector_pop2(&b->stack); // r = parent of q
    assert(is_black(b, r));

    s = sibling(b, r, q);       // s = sibling of q = uncle of p
    if (is_red(b, s)) {
      // flip colors of q and s
      mark_black(b, s);
      mark_black(b, q);
      // if r is the root, we're done
      if (r == b->root) break;
      // otherwise, we color r red
      // and move up to p := r, q := parent of r
      mark_red(b, r);
      p = r;
      q = ivector_pop2(&b->stack); // q = parent of r
      assert(is_parent_node(b, q, p));

    } else {
      // Balance the tree with one or two rotations
      i = child_index(b, r, q);
      j = child_index(b, q, p);
      if (i != j) {
        /*
         * Rotate p and q
         * q becomes a child of p
         * p becomes a child of r
         */
        assert(q != 0 && p != 0 && r != 0 &&
               b->child[r][i] == q && b->child[q][j] == p);
        b->child[r][i] = p;
        b->child[q][j] = b->child[p][i];
        b->child[p][i] = q;

        // prepare for second rotation:
        q = p;
      }

      /*
       * rotate r and q
       * and fix the colors: r becomes red, q becomes black
       */
      assert(b->child[r][i] == q);
      fix_parent(b, r, q);
      b->child[r][i] = b->child[q][1-i];
      b->child[q][1-i] = r;
      mark_red(b, r);
      mark_black(b, q);

      break;
    }
  }
}


/*
 * Balance the tree after deleting a black node
 * - p = node that replaces the deleted node
 * - q = parent of p
 * - b->stack contains the path [null, root, ... r] where r is q's parent
 */
static void rba_balance_after_delete(rba_buffer_t *b, uint32_t p, uint32_t q) {
  uint32_t r, s, t;
  uint32_t i;

  assert(is_parent_node(b, q, p) && is_black(b, b->root));

 loop:
  if (is_red(b, p)) {
    mark_black(b, p);   // done
  } else {
    i = child_index(b, q, p);
    r = sibling(b, q, p);

    assert(is_black(b, p) && p == b->child[q][i] && r == b->child[q][1 - i]);

    if (is_red(b, r)) {
      // rotate and switch the colors of q and r
      fix_parent(b, q, r);
      b->child[q][1 - i] = b->child[r][i];
      b->child[r][i] = q;
      mark_black(b, r);
      mark_red(b, q);

      ivector_push(&b->stack, r); // r is now parent of q

      // r := new sibling of p after the rotation
      r = b->child[q][1 - i];
    }

    assert(is_black(b, r) && is_black(b, p) &&
	   p == b->child[q][i] && r == b->child[q][1 - i]);

    // three subcases depending on r's children
    s = b->child[r][i];
    t = b->child[r][1 - i];
    if (is_black(b, s) && is_black(b, t)) {
      // two black children: change r's color to red and move up
      mark_red(b, r);
      p = q;
      q = ivector_pop2(&b->stack);
      // q is either null if p is the root (then we're done)
      // or q is p's parent and we loop
      if (q != rba_null) {
        assert(is_parent_node(b, q, p));
        goto loop;
      }

    } else {
      // at least one red child
      if (is_black(b, t)) {
        // rotate s and r
        // change r's color to red
        // change s's color to black
        b->child[r][i] = b->child[s][1 - i];
        b->child[s][1 - i] = r;
        b->child[q][1 - i] = s;
        mark_red(b, r);
        mark_black(b, s);

        t = r;
        r = s;
        s = b->child[r][i];
      }

      assert(is_black(b, p) && is_black(b, r) && is_red(b, t) &&
	      p == b->child[q][i] && r == b->child[q][1 - i] &&
	      s == b->child[r][i] && t == b->child[r][1 - i]);

      // rotate r and q and change colors
      // r takes the same color as q
      // t becomes black
      // q becomes black
      fix_parent(b, q, r);
      b->child[r][i] = q;
      b->child[q][1 - i] = s;
      copy_color(b, r, q);
      mark_black(b, q);
      mark_black(b, t);
    }
  }

  assert(is_black(b, b->root));
}


/*
 * BUFFER OPERATIONS
 */

/*
 * Initialize and finalize a monomial
 */
static inline void init_rba_mono(mono_t *m) {
  q_init(&m->coeff);
}

static inline void clear_rba_mono(mono_t *m) {
  q_clear(&m->coeff);
}


/*
 * Initialize buffer
 */
void init_rba_buffer(rba_buffer_t *b, pprod_table_t *ptbl) {
  uint32_t n;

  n = DEF_RBA_BUFFER_SIZE;
  assert(n <= MAX_RBA_BUFFER_SIZE);

  b->mono = (mono_t *) safe_malloc(n * sizeof(mono_t));
  b->child = (rb_node_t *) safe_malloc(n * sizeof(rb_node_t));
  b->isred = allocate_bitvector(n);

  b->ptbl = ptbl;
  init_ivector(&b->stack, 20);

  assert(n > 0 && rba_null == 0);

  // initialize the null node
  b->mono[0].prod = NULL;
  q_init(&b->mono[0].coeff);
  b->child[0][0] = 0;
  b->child[0][1] = 1;
  clr_bit(b->isred, 0); // null node must be black

  b->size = n;
  b->num_nodes = 1;
  b->nterms = 0;
  b->root = 0;      // rba_null
  b->free_list = 0; // also rba_null (empty list)
}


/*
 * Extend: double size
 */
static void extend_rba_buffer(rba_buffer_t *b) {
  uint32_t n;

  n = b->size << 1;
  if (n > MAX_RBA_BUFFER_SIZE) {
    out_of_memory();
  }

  b->mono = (mono_t *) safe_realloc(b->mono, n * sizeof(mono_t));
  b->child = (rb_node_t *) safe_realloc(b->child, n * sizeof(rb_node_t));
  b->isred = extend_bitvector(b->isred, n);
  b->size = n;
}


/*
 * Allocate a node: return its id
 */
static uint32_t rba_alloc_node(rba_buffer_t *b) {
  uint32_t i;

  i = b->free_list;
  if (i != rba_null) {
    b->free_list = b->child[i][0];
  } else {
    i = b->num_nodes;
    if (i == b->size) {
      extend_rba_buffer(b);
    }
    assert(i < b->size);
    init_rba_mono(b->mono + i);
    b->num_nodes = i+1;
  }

  assert(0 < i && i < b->num_nodes);

  return i;
}


/*
 * Free node i: add it to the free list
 */
static void rba_free_node(rba_buffer_t *b, uint32_t i) {
  assert(0 < i && i < b->num_nodes);
  b->child[i][0] = b->free_list;
  b->free_list = i;
}



/*
 * Scan tree and finalize all monomials
 * - if the tree is small, we traverse the tree
 * - otherwise, we use a linear scan of b->mono
 */
// recursive version: cleanup all monomials reachable from node i
static void cleanup_tree(rba_buffer_t *b, uint32_t i) {
  assert(0 <= i && i < b->num_nodes);
  if (i != rba_null) {
    clear_rba_mono(b->mono + i);
    cleanup_tree(b, b->child[i][0]);
    cleanup_tree(b, b->child[i][1]);
  }
}

static void rba_cleanup(rba_buffer_t *b) {
  uint32_t i, n;

  if (rba_tree_is_small(b)) {
    cleanup_tree(b, b->root);
  } else {
    n = b->num_nodes;
    for (i=1; i<n; i++) {
      clear_rba_mono(b->mono + i);
    }
  }
}


/*
 * Free memory
 */
void delete_rba_buffer(rba_buffer_t *b) {
  rba_cleanup(b);
  safe_free(b->mono);
  safe_free(b->child);
  delete_bitvector(b->isred);
  delete_ivector(&b->stack);
  b->mono = NULL;
  b->child = NULL;
  b->isred = NULL;
}



/*
 * Reset b to the empty tree
 */
void reset_rba_buffer(rba_buffer_t *b) {
  rba_cleanup(b);
  b->num_nodes = 1;
  b->nterms = 0;
  b->root = 0;
  b->free_list = 0;
}



/*
 * NODE ADDITION AND DELETION
 */

/*
 * Search for a monomial whose prod is equal to r
 * - if there's one return its id and set new_node to false
 * - if there isn't one, create a new node (with coeff = 0 and prod = r)
 *   and set new_node to true.
 *
 * Side effects:
 * - if a new node is created, num_terms is incremented
 * - if new_node is false, the path from the root to the returned
 *   node p is stored in b->stack in the form
 *     [rba_null, root, ...., q] where q is p's parent
 */
//static
uint32_t rba_get_node(rba_buffer_t *b, pprod_t *r, bool *new_node) {
  uint32_t k, i, p;

  ivector_reset(&b->stack);

  // to force termination, store r in the null_node2
  b->mono[0].prod = r;

  k = 0; // otherwise GCC gives a warning

  // invariant: p = parent of i (and we use rba_null as parent of the root)
  p = rba_null;
  i = b->root;
  while (b->mono[i].prod != r) {
    k = pprod_precedes(b->mono[i].prod, r);
    // save p in the stack
    ivector_push(&b->stack, p);
    p = i;
    i = b->child[i][k];
  }

  if (i == 0) {
    // add a new node
    *new_node = true;
    i = rba_alloc_node(b);

    b->nterms ++;

    b->mono[i].prod = r;
    assert(q_is_zero(&b->mono[i].coeff));
    b->child[i][0] = rba_null;
    b->child[i][1] = rba_null;

    if (p == rba_null) {
      // i becomes the root. make sure it is black
      b->root = i;
      mark_black(b, i);
    } else {
      // add i as child of p and balance the tree
      assert(p < b->num_nodes && b->child[p][k] == rba_null);
      b->child[p][k] = i;
      mark_red(b, i);
      rba_balance_after_add(b, i, p);
    }
  } else {
    // node exists; save p on the stack
    *new_node = false;
    ivector_push(&b->stack, p);
  }

  assert(i > 0 && b->mono[i].prod == r);

  return i;
}



/*
 * Delete node i
 * - mono[i].coeff must be zero
 * - b->stack must contain the path from the root to i's parent
 *   (as set by get_node: [null, root, ...., parent of i]
 *
 * Side effect:
 * - decrement b->num_terms
 */
//static
void rba_delete_node(rba_buffer_t *b, uint32_t i) {
  uint32_t p, j, k;

  assert(0 < i && i < b->num_nodes && q_is_zero(&b->mono[i].coeff));

  b->nterms --;

  if (b->child[i][0] != rba_null &&  b->child[i][1] != rba_null) {
    /*
     * i has two children: find the successor node of i = the node
     * that will be deleted. Store the path to that leaf in b->stack
     */
    p = i;
    j = b->child[p][1];
    do {
      ivector_push(&b->stack, p);
      p = j;
      j = b->child[j][0];
    } while (j != rba_null);

    assert(0 < p && p < b->num_nodes);

    /*
     * copy p's content into node i
     * we can do a direct copy of b->node[p].coeff into b->node[i].coeff
     * because b->mono[i].coeff is 1/0
     */
    b->mono[i].prod = b->mono[p].prod;
    q_copy_and_clear(&b->mono[i].coeff, &b->mono[p].coeff);

    i = p;
  }

  j = b->child[i][0] + b->child[i][1]; // child of i or rba_null if i has no children
  assert(j == b->child[i][0] || j == b->child[i][1]);

  p = ivector_pop2(&b->stack); // parent of i or null if i is the root

  if (p == rba_null) {
    assert(b->root == i);
    b->root = j;
    mark_black(b, j);
  } else {
    k = child_index(b, p, i);
    b->child[p][k] = j;

    if (is_black(b, i)) {
      rba_balance_after_delete(b, j, p);
    }
  }

  rba_free_node(b, i);
}





/*
 * QUERIES
 */

/*
 * Root monomial
 */
static inline mono_t *root_mono(const rba_buffer_t *b) {
  return b->mono + b->root;
}

/*
 * Check whether b is a constant
 */
bool rba_buffer_is_constant(const rba_buffer_t *b) {
  return b->nterms == 0 || (b->nterms == 1 && root_mono(b)->prod == empty_pp);
}

/*
 * Check whether b is constant and nonzero
 * - b must be normalized
 */
bool rba_buffer_is_nonzero(const rba_buffer_t *b) {
  return b->nterms == 1 && root_mono(b)->prod == empty_pp;
}


/*
 * Check whether b is constant and positive, negative, etc.
 * - b must be normalized
 */
bool rba_buffer_is_pos(const rba_buffer_t *b) {
  mono_t *r;
  r = root_mono(b);
  return b->nterms == 1 && r->prod == empty_pp && q_is_pos(&r->coeff);
}

bool rba_buffer_is_neg(const rba_buffer_t *b) {
  mono_t *r;
  r = root_mono(b);
  return b->nterms == 1 && r->prod == empty_pp && q_is_neg(&r->coeff);
}

bool rba_buffer_is_nonneg(const rba_buffer_t *b) {
  mono_t *r;
  r = root_mono(b);
  return b->nterms == 1 && r->prod == empty_pp && q_is_nonneg(&r->coeff);
}

bool rba_buffer_is_nonpos(const rba_buffer_t *b) {
  mono_t *r;
  r = root_mono(b);
  return b->nterms == 1 && r->prod == empty_pp && q_is_nonpos(&r->coeff);
}


/*
 * Check whether b is of the form 1 * X for a non-null power-product X
 * If so return X in *r
 */
bool rba_buffer_is_product(const rba_buffer_t *b, pprod_t **r) {
  mono_t *root;

  if (b->nterms == 1) {
    root = root_mono(b);
    if (root->prod != empty_pp && q_is_one(&root->coeff)) {
      *r = root->prod;
      return true;
    }
  }

  return false;
}


/*
 * Check whether b is of the form a * X - a * Y
 * for a non-zero rational a and two products X and Y.
 * If so return X in *r1 and Y in *r2
 */
bool rba_buffer_is_equality(const rba_buffer_t *b, pprod_t **r1, pprod_t **r2) {
  uint32_t i, j;
  mono_t *p, *q;
  pprod_t *x, *y;
  rational_t a;
  bool is_eq;

  is_eq = false;
  if (b->nterms == 2) {
    i = b->root;
    j = b->child[i][0] + b->child[i][1];
    assert(j == b->child[i][0] || j == b->child[i][1]);
    p = b->mono + i;
    q = b->mono + j;
    assert(q_is_nonzero(&p->coeff) && q_is_nonzero(&q->coeff));
    x = p->prod;
    y = p->prod;
    if (x != empty_pp && y != empty_pp) {
      *r1 = x;
      *r2 = y;
      q_init(&a);
      q_set(&a, &p->coeff);
      q_add(&a, &q->coeff);
      is_eq = q_is_zero(&a);
      q_clear(&a);
    }
  }

  return is_eq;
}


/*
 * Main monomial of b
 */
mono_t *rba_buffer_main_mono(const rba_buffer_t *b) {
  assert(b->nterms > 0);
  return b->mono +  rba_main_idx(b);
}


/*
 * Main term
 */
pprod_t *rba_buffer_main_term(const rba_buffer_t *b) {
  return rba_buffer_main_mono(b)->prod;
}


/*
 * Get degree of polynomial in buffer b.
 * - returns 0 if b is zero
 */
uint32_t rba_buffer_degree(const rba_buffer_t *b) {
  return (b->nterms == 0) ? 0 : pprod_degree(rba_buffer_main_term(b));
}


/*
 * Degree of x in b
 * - return 0 if x does not occur in b
 */

// return max(d, degree of x in subtree of root i)
static uint32_t tree_var_degree(const rba_buffer_t *b, int32_t x, uint32_t i, uint32_t d) {
  uint32_t e;

  if (i != rba_null) {
    assert(q_is_nonzero(&b->mono[i].coeff));
    e = pprod_var_degree(b->mono[i].prod, x);
    if (e > d) {
      d = e;
    }
    d = tree_var_degree(b, x, b->child[i][0], d);
    d = tree_var_degree(b, x, b->child[i][1], d);
  }
  return d;
}

uint32_t rba_buffer_var_degree(const rba_buffer_t *b, int32_t x) {
  uint32_t i, n, d, e;

  if (rba_tree_is_small(b)) {
    d = tree_var_degree(b, x, b->root, 0);
  } else {
    n = b->num_nodes;
    d = 0;
    for (i=1; i<n; i++) {
      if (q_is_nonzero(&b->mono[i].coeff)) {
	e = pprod_var_degree(b->mono[i].prod, x);
	if (e > d) {
	  d = e;
	}
      }
    }
  }
  return d;
}


/*
 * Collect the two monomials of b into *m[0] and *m[1]
 * - b must have exactly two monomials
 */
void rba_buffer_monomial_pair(const rba_buffer_t *b, mono_t *m[2]) {
  uint32_t x, i, j;

  assert(b->nterms == 2);

  x = b->root;
  i = b->child[x][0];
  j = b->child[x][1];

  if (i == rba_null) {
    m[0] = b->mono + x;
    m[1] = b->mono + j;
  } else {
    assert(j == rba_null);
    m[0] = b->mono + i;
    m[1] = b->mono + x;
  }
}


/*
 * Monomial whose pp is equal to r (or NULL)
 */
mono_t *rba_buffer_get_mono(rba_buffer_t *b, pprod_t *r) {
  mono_t *p;
  uint32_t i;

  p = NULL;
  i = rba_find_node(b, r);
  if (i != rba_null) {
    p = b->mono + i;
    assert(p->prod == r && q_is_nonzero(&p->coeff));
  }
  return p;
}


/*
 * Get the constant monomial of b
 * - return NULL if b does not have a constant monomial
 */
mono_t *rba_buffer_get_constant_mono(const rba_buffer_t *b) {
  mono_t *p;
  uint32_t i;

  i = rba_smallest_idx(b);
  p = b->mono + i;
  if (i == 0 || p->prod != empty_pp) {
    p = NULL;
  }
  return p;
}



/*
 * Check whether monomial p occurs in b
 * - i.e., b contains a monomial with same product and coefficient as m
 * - m must have a non-zero coefficient
 */
static bool rba_buffer_has_monomial(rba_buffer_t *b, mono_t *p) {
  uint32_t i;

  assert(q_is_nonzero(&p->coeff));
  i = rba_find_node(b, p->prod);
  return i != rba_null && q_eq(&p->coeff, &b->mono[i].coeff);
}


/*
 * Check whether all monomials in b1's subtree rooted at x occur in b2
 */
static bool tree_eq(rba_buffer_t *b1, rba_buffer_t *b2, uint32_t x) {
  uint32_t i, j;

  assert(x < b1->num_nodes);

  if (x == rba_null) return true;

  i = b1->child[x][0];
  j = b1->child[x][1];
  return rba_buffer_has_monomial(b2, b1->mono + x) && tree_eq(b1, b2, i) && tree_eq(b1, b2, j);
}


/*
 * Check equality:
 * - b1 and b2 are two buffers with same number of terms
 * - n = number of terms
 */
static bool rba_buffer_eq(rba_buffer_t *b1, rba_buffer_t *b2) {
  rba_buffer_t *aux;
  mono_t *p;
  uint32_t n;

  assert(b1->nterms == b2->nterms);

  // swap if b1 has more nodes than b2
  if (b1->num_nodes > b2->num_nodes) {
    aux = b1; b1 = b2; b2 = aux;
  }

  if (rba_tree_is_small(b1)) {
    return tree_eq(b1, b2, b1->root);
  }

  p = b1->mono;
  n = b1->num_nodes - 1;
  while (n > 0) {
    n --;
    p ++;
    if (q_is_nonzero(&p->coeff) && !rba_buffer_has_monomial(b2, p)) {
      return false;
    }
  }

  return true;
}

/*
 * Check equality between b1 and b2
 * - both must use the same product table
 */
bool rba_buffer_equal(rba_buffer_t *b1, rba_buffer_t *b2) {
  assert(b1->ptbl == b2->ptbl);
  return b1->nterms  == b2->nterms && rba_buffer_eq(b1, b2);
}




/*****************************
 *  POLYNOMIAL CONSTRUCTION  *
 ****************************/

/*
 * Set b to the constant 1
 */
void rba_buffer_set_one(rba_buffer_t *b) {
  uint32_t i;

  reset_rba_buffer(b);
  assert(b->root == rba_null && b->nterms == 0);

  i = rba_alloc_node(b);

  b->mono[i].prod = empty_pp;
  assert(q_is_zero(&b->mono[i].coeff));
  q_set_one(&b->mono[i].coeff);
  b->child[i][0] = rba_null;
  b->child[i][1] = rba_null;

  b->root = i;
  mark_black(b, i);

  b->nterms = 1;
}


/*
 * Negate: multiply all coefficients by -1
 */
static void negate_tree(rba_buffer_t *b, uint32_t x) {
  assert(x < b->num_nodes);
  if (x != rba_null) {
    q_neg(&b->mono[x].coeff);
    negate_tree(b, b->child[x][0]);
    negate_tree(b, b->child[x][1]);
  }
}

void rba_buffer_negate(rba_buffer_t *b) {
  uint32_t i, n;

  if (rba_tree_is_small(b)) {
    negate_tree(b, b->root);
  } else {
    n = b->num_nodes;
    for (i=1; i<n; i++) {
      // Not clear whether skipping zero coeff is faster
      q_neg(&b->mono[i].coeff);
    }
  }
}


/*
 * Multiply all coefficients by constant a
 */
// a must be non-zero here
static void mul_const_tree(rba_buffer_t *b, const rational_t *a, uint32_t x) {
  assert(x < b->num_nodes);
  if (x != rba_null) {
    q_mul(&b->mono[x].coeff, a);
    mul_const_tree(b, a, b->child[x][0]);
    mul_const_tree(b, a, b->child[x][1]);
  }
}

void rba_buffer_mul_const(rba_buffer_t *b, const rational_t *a) {
  uint32_t i, n;

  if (q_is_zero(a)) {
    reset_rba_buffer(b);
  } else if (rba_tree_is_small(b)) {
    mul_const_tree(b, a, b->root);
  } else {
    n = b->num_nodes;
    for (i=1; i<n; i++) {
      // Skip zero coeff?
      q_mul(&b->mono[i].coeff, a);
    }
  }
}


/*
 * Divide all coefficients by a non-zero constant
 */
void rba_buffer_div_const(rba_buffer_t *b, const rational_t *a) {
  rational_t inv_a;
  uint32_t i, n;

  assert(q_is_nonzero(a));

  if (rba_tree_is_small(b)) {
    q_init(&inv_a);
    q_set(&inv_a, a);
    q_inv(&inv_a);
    mul_const_tree(b, &inv_a, b->root);
    q_clear(&inv_a);
  } else {
    n = b->num_nodes;
    for (i=1; i<n; i++) {
      // Skip zero coeff?
      q_div(&b->mono[i].coeff, a);
    }
  }
}


/*
 * Multiply by a power product r
 * - the monomial ordering is compatible with product:
 *   p1 < p2 => r * p1 < r * p2
 */
static void mul_pp_tree(rba_buffer_t *b, pprod_t *r, uint32_t x) {
  assert(x < b->num_nodes);

  if (x != rba_null) {
    b->mono[x].prod = pprod_mul(b->ptbl, b->mono[x].prod, r);
    mul_pp_tree(b, r, b->child[x][0]);
    mul_pp_tree(b, r, b->child[x][1]);
  }
}

void rba_buffer_mul_pp(rba_buffer_t *b, pprod_t *r) {
  pprod_table_t *tbl;
  mono_t *p;
  uint32_t n;

  if (rba_tree_is_small(b)) {
    mul_pp_tree(b, r, b->root);
  } else {
    tbl = b->ptbl;
    p = b->mono;
    n = b->num_nodes - 1;
    while (n > 0) {
      n --;
      p ++;
      if (q_is_nonzero(&p->coeff)) {
        p->prod = pprod_mul(tbl, p->prod, r);
      }
    }
  }
}


/*
 * Multiply by (-1) * r
 */
static void mul_negpp_tree(rba_buffer_t *b, pprod_t *r, uint32_t x) {
  assert(x < b->num_nodes);

  if (x != rba_null) {
    b->mono[x].prod = pprod_mul(b->ptbl, b->mono[x].prod, r);
    q_neg(&b->mono[x].coeff);
    mul_pp_tree(b, r, b->child[x][0]);
    mul_pp_tree(b, r, b->child[x][1]);
  }
}

void rba_buffer_mul_negpp(rba_buffer_t *b, pprod_t *r) {
  pprod_table_t *tbl;
  mono_t *p;
  uint32_t n;

  if (rba_tree_is_small(b)) {
    mul_negpp_tree(b, r, b->root);
  } else {
    tbl = b->ptbl;
    p = b->mono;
    n = b->num_nodes - 1;
    while (n > 0) {
      n --;
      p ++;
      if (q_is_nonzero(&p->coeff)) {
        p->prod = pprod_mul(tbl, p->prod, r);
        q_neg(&p->coeff);
      }
    }
  }
}



/*
 * Multiply by a * r
 */
// a must be non-zero here
static void mul_mono_tree(rba_buffer_t *b, const rational_t *a, pprod_t *r, uint32_t x) {
  assert(x < b->num_nodes);

  if (x != rba_null) {
    b->mono[x].prod = pprod_mul(b->ptbl, b->mono[x].prod, r);
    q_mul(&b->mono[x].coeff, a);
    mul_mono_tree(b, a, r, b->child[x][0]);
    mul_mono_tree(b, a, r, b->child[x][1]);
  }
}

void rba_buffer_mul_mono(rba_buffer_t *b, const rational_t *a, pprod_t *r) {
  pprod_table_t *tbl;
  mono_t *p;
  uint32_t n;

  if (q_is_zero(a)) {
    reset_rba_buffer(b);
  } else if (rba_tree_is_small(b)) {
    mul_mono_tree(b, a, r, b->root);
  } else {
    tbl = b->ptbl;
    p = b->mono;
    n = b->num_nodes - 1;
    while (n > 0) {
      n --;
      p ++;
      if (q_is_nonzero(&p->coeff)) {
        p->prod = pprod_mul(tbl, p->prod, r);
        q_mul(&p->coeff, a);
      }
    }
  }
}


/*
 * Add or subtract a * r when a is non-zero
 */
static void rba_add_mono(rba_buffer_t *b, const rational_t *a, pprod_t *r) {
  uint32_t i;
  bool new_node;

  assert(q_is_nonzero(a));

  i = rba_get_node(b, r, &new_node);
  assert(0 < i && i < b->num_nodes && b->mono[i].prod == r);
  q_add(&b->mono[i].coeff, a);
  if (!new_node && q_is_zero(&b->mono[i].coeff)) {
    rba_delete_node(b, i);
  }
}

static void rba_sub_mono(rba_buffer_t *b, const rational_t *a, pprod_t *r) {
  uint32_t i;
  bool new_node;

  assert(q_is_nonzero(a));

  i = rba_get_node(b, r, &new_node);
  assert(0 < i && i < b->num_nodes && b->mono[i].prod == r);
  q_sub(&b->mono[i].coeff, a);
  if (!new_node && q_is_zero(&b->mono[i].coeff)) {
    rba_delete_node(b, i);
  }
}


/*
 * Add or subtract a * c * r
 * - a and c must be non-zero
 */
static void rba_addmul_mono(rba_buffer_t *b, const rational_t *a, const rational_t *c, pprod_t *r) {
  uint32_t i;
  bool new_node;

  assert(q_is_nonzero(a) && q_is_nonzero(c));

  i = rba_get_node(b, r, &new_node);
  assert(0 < i && i < b->num_nodes && b->mono[i].prod == r);
  q_addmul(&b->mono[i].coeff, a, c);
  if (!new_node && q_is_zero(&b->mono[i].coeff)) {
    rba_delete_node(b, i);
  }
}

static void rba_submul_mono(rba_buffer_t *b, const rational_t *a, const rational_t *c, pprod_t *r) {
  uint32_t i;
  bool new_node;

  assert(q_is_nonzero(a) && q_is_nonzero(c));

  i = rba_get_node(b, r, &new_node);
  assert(0 < i && i < b->num_nodes && b->mono[i].prod == r);
  q_submul(&b->mono[i].coeff, a, c);
  if (!new_node && q_is_zero(&b->mono[i].coeff)) {
    rba_delete_node(b, i);
  }
}




/*
 * Add or subtract monomial a * r
 */
void rba_buffer_add_mono(rba_buffer_t *b, const rational_t *a, pprod_t *r) {
  if (q_is_nonzero(a)) {
    rba_add_mono(b, a, r);
  }
}

void rba_buffer_sub_mono(rba_buffer_t *b, const rational_t *a, pprod_t *r) {
  if (q_is_nonzero(a)) {
    rba_sub_mono(b, a, r);
  }
}

void rba_buffer_add_const(rba_buffer_t *b, const rational_t *a) {
  rba_buffer_add_mono(b, a, empty_pp);
}

void rba_buffer_sub_const(rba_buffer_t *b, const rational_t *a) {
  rba_buffer_sub_mono(b, a, empty_pp);
}





/*
 * Add or subtract r
 */
void rba_buffer_add_pp(rba_buffer_t *b, pprod_t *r) {
  uint32_t i;
  bool new_node;

  i = rba_get_node(b, r, &new_node);
  assert(0 < i && i < b->num_nodes && b->mono[i].prod == r);
  q_add_one(&b->mono[i].coeff);
  if (!new_node && q_is_zero(&b->mono[i].coeff)) {
    rba_delete_node(b, i);
  }
}

void rba_buffer_sub_pp(rba_buffer_t *b, pprod_t *r) {
  uint32_t i;
  bool new_node;

  i = rba_get_node(b, r, &new_node);
  assert(0 < i && i < b->num_nodes && b->mono[i].prod == r);
  q_sub_one(&b->mono[i].coeff);
  if (!new_node && q_is_zero(&b->mono[i].coeff)) {
    rba_delete_node(b, i);
  }
}


/*
 * Add b1 to b
 * - the two buffers must have the same ptbl and must be distinct
 * - b1 must be distinct from b
 */
static void add_buffer_tree(rba_buffer_t *b, rba_buffer_t *b1, uint32_t x) {
  assert(x < b1->num_nodes);
  if (x != rba_null) {
    rba_add_mono(b, &b1->mono[x].coeff, b1->mono[x].prod);
    add_buffer_tree(b, b1, b1->child[x][0]);
    add_buffer_tree(b, b1, b1->child[x][1]);
  }
}

void rba_buffer_add_buffer(rba_buffer_t *b, rba_buffer_t *b1) {
  mono_t *p;
  uint32_t n;

  assert(b->ptbl == b1->ptbl && b != b1);
  if (rba_tree_is_small(b1)) {
    add_buffer_tree(b, b1, b1->root);
  } else {
    p = b1->mono;
    n = b1->num_nodes - 1;
    while (n > 0) {
      n --;
      p ++;
      if (q_is_nonzero(&p->coeff)) {
        rba_add_mono(b, &p->coeff, p->prod);
      }
    }
  }
}


/*
 * Subtract b1 from  b
 * - the two buffers must have the same ptbl
 * - b1 must be distinct from b
 */
static void sub_buffer_tree(rba_buffer_t *b, rba_buffer_t *b1, uint32_t x) {
  assert(x < b1->num_nodes);
  if (x != rba_null) {
    rba_sub_mono(b, &b1->mono[x].coeff, b1->mono[x].prod);
    sub_buffer_tree(b, b1, b1->child[x][0]);
    sub_buffer_tree(b, b1, b1->child[x][1]);
  }
}

void rba_buffer_sub_buffer(rba_buffer_t *b, rba_buffer_t *b1) {
  mono_t *p;
  uint32_t n;

  assert(b->ptbl == b1->ptbl && b != b1);

  if (rba_tree_is_small(b1)) {
    sub_buffer_tree(b, b1, b1->root);
  } else {
    p = b1->mono;
    n = b1->num_nodes - 1;
    while (n > 0) {
      n --;
      p ++;
      if (q_is_nonzero(&p->coeff)) {
        rba_sub_mono(b, &p->coeff, p->prod);
      }
    }
  }
}


/*
 * Add a * b1 to b
 * - the two buffers must have the same ptbl
 * - b1 must be distinct from b
 */
static void addmul_const_tree(rba_buffer_t *b, rba_buffer_t *b1, const rational_t *a, uint32_t x) {
  assert(x < b1->num_nodes);
  if (x != rba_null) {
    rba_addmul_mono(b, a, &b1->mono[x].coeff, b1->mono[x].prod);
    addmul_const_tree(b, b1, a, b1->child[x][0]);
    addmul_const_tree(b, b1, a, b1->child[x][1]);
  }
}

void rba_add_const_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, const rational_t *a) {
  mono_t *p;
  uint32_t n;

  assert(b->ptbl == b1->ptbl && b != b1);

  if (rba_tree_is_small(b1)) {
    addmul_const_tree(b, b1, a, b1->root);
  } else {
    p = b1->mono;
    n = b1->num_nodes - 1;
    while (n > 0) {
      n --;
      p ++;
      if (q_is_nonzero(&p->coeff)) {
        rba_addmul_mono(b, a, &p->coeff, p->prod);
      }
    }
  }
}


/*
 * Subtract a * b1 from b
 * - the two buffers must have the same ptbl
 * - b1 must be distinct from b
 */
static void submul_const_tree(rba_buffer_t *b, rba_buffer_t *b1, const rational_t *a, uint32_t x) {
  assert(x < b1->num_nodes);
  if (x != rba_null) {
    rba_submul_mono(b, a, &b1->mono[x].coeff, b1->mono[x].prod);
    submul_const_tree(b, b1, a, b1->child[x][0]);
    submul_const_tree(b, b1, a, b1->child[x][1]);
  }
}

void rba_sub_const_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, const rational_t *a) {
  mono_t *p;
  uint32_t n;

  assert(b->ptbl == b1->ptbl && b != b1);

  if (rba_tree_is_small(b1)) {
    submul_const_tree(b, b1, a, b1->root);
  } else {
    p = b1->mono;
    n = b1->num_nodes - 1;
    while (n > 0) {
      n --;
      p ++;
      if (q_is_nonzero(&p->coeff)) {
        rba_submul_mono(b, a, &p->coeff, p->prod);
      }
    }
  }
}



/*
 * Add r * b1 to b
 * - b1 must be different from b
 */
static void addmul_pp_tree(rba_buffer_t *b, rba_buffer_t *b1, pprod_t *r, uint32_t x) {
  pprod_t *q;

  assert(x < b1->num_nodes);

  if (x != rba_null) {
    q = pprod_mul(b1->ptbl, r, b1->mono[x].prod);
    rba_add_mono(b, &b1->mono[x].coeff, q);
    addmul_pp_tree(b, b1, r, b1->child[x][0]);
    addmul_pp_tree(b, b1, r, b1->child[x][1]);
  }
}

void rba_buffer_add_pp_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, pprod_t *r) {
  pprod_table_t *tbl;
  mono_t *p;
  pprod_t *q;
  uint32_t n;

  assert(b->ptbl == b1->ptbl && b != b1);

  if (rba_tree_is_small(b1)) {
    addmul_pp_tree(b, b1, r, b1->root);
  } else {
    tbl = b1->ptbl;
    p = b1->mono;
    n = b1->num_nodes - 1;
    while (n > 0) {
      n --;
      p ++;
      if (q_is_nonzero(&p->coeff)) {
        q = pprod_mul(tbl, r, p->prod);
        rba_add_mono(b, &p->coeff, q);
      }
    }
  }
}


/*
 * Add - r * b1 to b
 * - b1 must be different from b
 */
static void submul_pp_tree(rba_buffer_t *b, rba_buffer_t *b1, pprod_t *r, uint32_t x) {
  pprod_t *q;

  assert(x < b1->num_nodes);

  if (x != rba_null) {
    q = pprod_mul(b1->ptbl, r, b1->mono[x].prod);
    rba_sub_mono(b, &b1->mono[x].coeff, q);
    submul_pp_tree(b, b1, r, b1->child[x][0]);
    submul_pp_tree(b, b1, r, b1->child[x][1]);
  }
}

void rba_buffer_sub_pp_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, pprod_t *r) {
  pprod_table_t *tbl;
  mono_t *p;
  pprod_t *q;
  uint32_t n;

  assert(b->ptbl == b1->ptbl && b != b1);

  if (rba_tree_is_small(b1)) {
    submul_pp_tree(b, b1, r, b1->root);
  } else {
    tbl = b1->ptbl;
    p = b1->mono;
    n = b1->num_nodes - 1;
    while (n > 0) {
      n --;
      p ++;
      if (q_is_nonzero(&p->coeff)) {
        q = pprod_mul(tbl, r, p->prod);
        rba_sub_mono(b, &p->coeff, q);
      }
    }
  }
}


/*
 * Add a * r * b1 to b
 * - b1 must be different from b
 */
static void addmul_mono_tree(rba_buffer_t *b, rba_buffer_t *b1, const rational_t *a, pprod_t *r, uint32_t x) {
  pprod_t *q;

  assert(x < b1->num_nodes);

  if (x != rba_null) {
    q = pprod_mul(b1->ptbl, r, b1->mono[x].prod);
    rba_addmul_mono(b, a, &b1->mono[x].coeff, q);
    addmul_mono_tree(b, b1, a, r, b1->child[x][0]);
    addmul_mono_tree(b, b1, a, r, b1->child[x][1]);
  }
}

void rba_buffer_add_mono_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, const rational_t *a, pprod_t *r) {
  pprod_table_t *tbl;
  mono_t *p;
  pprod_t *q;
  uint32_t n;

  assert(b->ptbl == b1->ptbl && b != b1);

  if (q_is_nonzero(a)) {
    if (rba_tree_is_small(b1)) {
      addmul_mono_tree(b, b1, a, r, b1->root);
    } else {
      tbl = b1->ptbl;
      p = b1->mono;
      n = b1->num_nodes - 1;
      while (n > 0) {
        n--;
        p++;
        if (q_is_nonzero(&p->coeff)) {
          q = pprod_mul(tbl, r, p->prod);
          rba_addmul_mono(b, a, &p->coeff, q);
        }
      }
    }
  }
}


/*
 * Add -a * r * b1 to b
 * - b1 must be different from b
 */
static void submul_mono_tree(rba_buffer_t *b, rba_buffer_t *b1, const rational_t *a, pprod_t *r, uint32_t x) {
  pprod_t *q;

  assert(x < b1->num_nodes);

  if (x != rba_null) {
    q = pprod_mul(b1->ptbl, r, b1->mono[x].prod);
    rba_submul_mono(b, a, &b1->mono[x].coeff, q);
    submul_mono_tree(b, b1, a, r, b1->child[x][0]);
    submul_mono_tree(b, b1, a, r, b1->child[x][1]);
  }
}

void rba_buffer_sub_mono_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, const rational_t *a, pprod_t *r) {
  pprod_table_t *tbl;
  mono_t *p;
  pprod_t *q;
  uint32_t n;

  assert(b->ptbl == b1->ptbl && b != b1);

  if (q_is_nonzero(a)) {
    if (rba_tree_is_small(b1)) {
      submul_mono_tree(b, b1, a, r, b1->root);
    } else {
      tbl = b1->ptbl;
      p = b1->mono;
      n = b1->num_nodes - 1;
      while (n > 0) {
        n--;
        p++;
        if (q_is_nonzero(&p->coeff)) {
          q = pprod_mul(tbl, r, p->prod);
          rba_submul_mono(b, a, &p->coeff, q);
        }
      }
    }
  }
}


/*
 * Add b1 * b2 to b
 * - b1 and b2 must be distinct from b (but b1 may be equal to b2)
 */
static void rba_addmul_buffer_tree(rba_buffer_t *b, rba_buffer_t *b1, rba_buffer_t *b2, uint32_t x) {
  assert(x < b2->num_nodes);

  if (x != rba_null) {
    // could use more efficient versions if coeff = +/-1 or prod = empty_pp?
    rba_buffer_add_mono_times_buffer(b, b1, &b2->mono[x].coeff, b2->mono[x].prod);
    rba_addmul_buffer_tree(b, b1, b2, b2->child[x][0]);
    rba_addmul_buffer_tree(b, b1, b2, b2->child[x][1]);
  }
}

void rba_buffer_add_buffer_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, rba_buffer_t *b2) {
  mono_t *p;
  uint32_t n;

  assert(b1->ptbl == b->ptbl && b2->ptbl == b->ptbl && b != b1 && b != b2);

  if (rba_tree_is_small(b2)) {
    rba_addmul_buffer_tree(b, b1, b2, b2->root);
  } else {
    p = b2->mono;
    n = b2->num_nodes - 1;
    while (n > 0) {
      n --;
      p ++;
      if (q_is_nonzero(&p->coeff)) {
        rba_buffer_add_mono_times_buffer(b, b1, &p->coeff, p->prod);
      }
    }
  }
}


/*
 * Add - b1 * b2 to b
 * - b1 and b2 must be distinct from b (but b1 may be equal to b2)
 */
static void rba_submul_buffer_tree(rba_buffer_t *b, rba_buffer_t *b1, rba_buffer_t *b2, uint32_t x) {
  assert(x < b2->num_nodes);

  if (x != rba_null) {
    // could use more efficient versions if coeff = +/-1 or prod = empty_pp?
    rba_buffer_sub_mono_times_buffer(b, b1, &b2->mono[x].coeff, b2->mono[x].prod);
    rba_submul_buffer_tree(b, b1, b2, b2->child[x][0]);
    rba_submul_buffer_tree(b, b1, b2, b2->child[x][1]);
  }
}

void rba_buffer_sub_buffer_times_buffer(rba_buffer_t *b, rba_buffer_t *b1, rba_buffer_t *b2) {
  mono_t *p;
  uint32_t n;

  assert(b1->ptbl == b->ptbl && b2->ptbl == b->ptbl && b != b1 && b != b2);

  if (rba_tree_is_small(b2)) {
    rba_submul_buffer_tree(b, b1, b2, b2->root);
  } else {
    p = b2->mono;
    n = b2->num_nodes - 1;
    while (n > 0) {
      n --;
      p ++;
      if (q_is_nonzero(&p->coeff)) {
        rba_buffer_sub_mono_times_buffer(b, b1, &p->coeff, p->prod);
      }
    }
  }
}



/*
 * Multiply b by b1
 */
void rba_buffer_mul_buffer(rba_buffer_t *b, rba_buffer_t *b1) {
  rba_buffer_t aux;

  assert(b->ptbl == b1->ptbl);

  aux = *b;  // clone of b
  init_rba_buffer(b, aux.ptbl);
  rba_buffer_add_buffer_times_buffer(b, &aux, b1);
  delete_rba_buffer(&aux);
}


/*
 * Compute the square of b
 */
void rba_buffer_square(rba_buffer_t *b) {
  rba_buffer_t aux;

  aux = *b;
  init_rba_buffer(b, aux.ptbl);
  rba_buffer_add_buffer_times_buffer(b, &aux, &aux);
  delete_rba_buffer(&aux);
}






/*************************************
 *  OPERATIONS WITH MONOMIAL ARRAYS  *
 ************************************/

/*
 * Add poly to buffer b
 */
void rba_buffer_add_monarray(rba_buffer_t *b, monomial_t *poly, pprod_t **pp) {
  while (poly->var < max_idx) {
    rba_add_mono(b, &poly->coeff, *pp);
    poly ++;
    pp ++;
  }
}


/*
 * Subtract poly from buffer b
 */
void rba_buffer_sub_monarray(rba_buffer_t *b, monomial_t *poly, pprod_t **pp) {
  while (poly->var < max_idx) {
    rba_sub_mono(b, &poly->coeff, *pp);
    poly ++;
    pp ++;
  }
}


/*
 * Add a * poly to buffer b
 */
void rba_buffer_add_const_times_monarray(rba_buffer_t *b, monomial_t *poly, pprod_t **pp, const rational_t *a) {
  if (q_is_nonzero(a)) {
    while (poly->var < max_idx) {
      rba_addmul_mono(b, a, &poly->coeff, *pp);
      poly ++;
      pp ++;
    }
  }
}


/*
 * Subtract a * poly from b
 */
void rba_buffer_sub_const_times_monarray(rba_buffer_t *b, monomial_t *poly, pprod_t **pp, const rational_t *a) {
  if (q_is_nonzero(a)) {
    while (poly->var < max_idx) {
      rba_submul_mono(b, a, &poly->coeff, *pp);
      poly ++;
      pp ++;
    }
  }
}


/*
 * Add a * r * poly to b
 */
void rba_buffer_add_mono_times_monarray(rba_buffer_t *b, monomial_t *poly, pprod_t **pp, const rational_t *a, pprod_t *r) {
  pprod_table_t *tbl;
  pprod_t *q;

  if (q_is_nonzero(a)) {
    tbl = b->ptbl;
    while (poly->var < max_idx) {
      q = pprod_mul(tbl, r, *pp);
      rba_addmul_mono(b, a, &poly->coeff, q);
      poly ++;
      pp ++;
    }
  }
}


/*
 * Add -a * r * poly to b
 */
void rba_buffer_sub_mono_times_monarray(rba_buffer_t *b, monomial_t *poly, pprod_t **pp, const rational_t *a, pprod_t *r) {
  pprod_table_t *tbl;
  pprod_t *q;

  if (q_is_nonzero(a)) {
    tbl = b->ptbl;
    while (poly->var < max_idx) {
      q = pprod_mul(tbl, r, *pp);
      rba_submul_mono(b, a, &poly->coeff, q);
      poly ++;
      pp ++;
    }
  }
}


/*
 * Multiply b by poly
 */
void rba_buffer_mul_monarray(rba_buffer_t *b, monomial_t *poly, pprod_t **pp) {
  rba_buffer_t aux;

  aux = *b;
  init_rba_buffer(b, aux.ptbl);
  while (poly->var < max_idx) {
    rba_buffer_add_mono_times_buffer(b, &aux, &poly->coeff, *pp);
    poly ++;
    pp ++;
  }
  delete_rba_buffer(&aux);
}


/*
 * Multiply b by  poly ^ d
 * - pp = power products for the variables of poly
 * - use aux as an auxiliary buffer (aux must be distinct from b)
 * - store the result in b (normalized)
 */
void rba_buffer_mul_monarray_power(rba_buffer_t *b, monomial_t *poly, pprod_t **pp, uint32_t d, rba_buffer_t *aux) {
  uint32_t i;

  assert(b != aux && b->ptbl == aux->ptbl);

  if (d <= 4) {
    // small exponent: aux is not used
    for (i=0; i<d; i++) {
      rba_buffer_mul_monarray(b, poly, pp);
    }
  } else {
    // larger exponent
    reset_rba_buffer(aux);
    rba_buffer_add_monarray(aux, poly, pp); // aux := poly
    for (;;) {
      /*
       * loop invariant: b0 * p^d0 == b * aux^ d
       * with b0 = b on entry to the function
       *      d0 = d on entry to the function
       */
      assert(d > 0);
      if ((d & 1) != 0) {
        rba_buffer_mul_buffer(b, aux); // b := b * aux
      }
      d >>= 1;                         // d := d/2
      if (d == 0) break;
      rba_buffer_square(aux);          // aux := aux^2
    }
  }
}



/*******************************************************************
 *  SUPPORT FOR HASH CONSING AND CONVERSION TO POLYNOMIAL OBJECTS  *
 ******************************************************************/

/*
 * The conversion of a buffer b to a polynomial object requires two steps:
 * 1) convert all the power-products in b to integer indices.
 *    This must map empty_pp to const_idx and end_pp to max_idx.
 * 2) build a polynomial from the coefficients of b and the integer indices
 *
 * The operations below use a buffer b and an integer array v.
 * The array v stores the conversion from power-products to integer indices:
 * If b contains a_0 r_0 + ... + a_n r_n then v must have (n+2) elements
 * and the integer index for power product r_i is v[i], and the last element
 * of v must be max_idx.
 *
 * The pair (b, v) defines then a polynomial P(b, v) = a_1 v[1] + ... + a_n v[n],
 */

/*
 * Store the subterm of P(b, v) rooted at x into polynomial p
 * - i = number of terms to the left of subtree rooted at x
 * - return i + number of terms in the subtree rooted at x
 */
static uint32_t rba_copy_tree(polynomial_t *p, rba_buffer_t *b, int32_t *v, uint32_t i, uint32_t x) {
  assert(x < b->num_nodes);

  if (x != rba_null) {
    i = rba_copy_tree(p, b, v, i, b->child[x][0]);
    assert(i < p->nterms);
    p->mono[i].var = v[i];
    q_copy_and_clear(&p->mono[i].coeff, &b->mono[x].coeff);
    i = rba_copy_tree(p, b, v, i+1, b->child[x][1]);
  }

  return i;
}


/*
 * Build P(b, v) (i.e., convert b to a polynomial then reset b).
 * SIDE EFFECT: b is reset to the zero polynomial.
 */
#ifdef NDEBUG
polynomial_t *rba_buffer_get_poly(rba_buffer_t *b, int32_t *v) {
  polynomial_t *tmp;

  tmp = alloc_raw_polynomial(b->nterms);
  (void) rba_copy_tree(tmp, b, v, 0, b->root);

  // reset b but don't call cleanup
  b->num_nodes = 1;
  b->nterms = 0;
  b->root = 0;
  b->free_list = 0;

  return tmp;
}

#else

/*
 * Debugging enabled
 */

// check that all monomials are cleared
static bool rba_buffer_is_clean(rba_buffer_t *b) {
  uint32_t i, n;

  n = b->num_nodes;
  for (i=1; i<n; i++) {
    if (q_is_nonzero(&b->mono[i].coeff)) {
      return false;
    }
  }
  return true;
}

// same function with debugging
polynomial_t *rba_buffer_get_poly(rba_buffer_t *b, int32_t *v) {
  polynomial_t *tmp;
  uint32_t n;

  tmp = alloc_raw_polynomial(b->nterms);
  n = rba_copy_tree(tmp, b, v, 0, b->root);
  assert(n == b->nterms);

  // reset b but don't call cleanup
  assert(rba_buffer_is_clean(b));

  b->num_nodes = 1;
  b->nterms = 0;
  b->root = 0;
  b->free_list = 0;

  return tmp;
}


#endif


/*
 * Hash code support: iterate the hash code computation
 * through all nodes reachable from x (in monomial order)
 * - *i = number of terms to the left of the subtree rooted at x
 * - h = hash code for this subtree
 * - update i: add the number of terms in the subtree rooted at x
 */
static uint32_t rba_hash_tree(rba_buffer_t *b, int32_t *v, uint32_t *i, uint32_t h, uint32_t x) {
  uint32_t num, den, j;

  assert(x < b->num_nodes);

  if (x != rba_null) {
    h = rba_hash_tree(b, v, i, h, b->child[x][0]); // left subtree

    // apply hash for node x
    q_hash_decompose(&b->mono[x].coeff, &num, &den);
    j = *i;
    assert(j < b->nterms);
    h = jenkins_hash_triple(v[j], num, den, h);
    *i = j+1;

    h = rba_hash_tree(b, v, i, h, b->child[x][1]); // right subtree
  }

  return h;
}


/*
 * Hash code for P(b, v).
 * This function is consistent with hash_polynomial defined in polynomials.c:
 * If P(b, v) = p0 then hash_rba_buffer(b, v) = hash_polynomial(p0).
 */
uint32_t hash_rba_buffer(rba_buffer_t *b, int32_t *v) {
  uint32_t h, n;

  n = 0;
  h = rba_hash_tree(b, v, &n, HASH_POLY_SEED + b->nterms, b->root);
  assert(n == b->nterms);
  return h;
}



/*
 * Check that the subtree rooted at x is equal to a segment of p
 * that start at *i:
 * - if the subtree rooted at x has n nodes then this returns true
 *   if the subtree is equal to p[j ... j+n-1] where j = *i
 * - side effect: if the function returns true then *i is updated to j+n-1
 */
// aux function: check where p->mono[*i] is equal to the node x
// if so increment *i
static bool rba_equal_node(polynomial_t *p, rba_buffer_t *b, int32_t *v, uint32_t *i, uint32_t x) {
  uint32_t j;

  assert(0 < x && x < b->num_nodes && q_is_nonzero(&b->mono[x].coeff));

  j = *i;
  assert(j < p->nterms);

  if (v[j] == p->mono[j].var && q_eq(&b->mono[x].coeff, &p->mono[j].coeff)) {
    *i = j+1;
    return true;
  }

  return false;
}

static bool rba_equal_tree(polynomial_t *p, rba_buffer_t *b, int32_t *v, uint32_t *i, uint32_t x) {
  assert(x < b->num_nodes);
  return (x == rba_null) ||
    (rba_equal_tree(p, b, v, i, b->child[x][0]) &&
     rba_equal_node(p, b, v, i, x) &&
     rba_equal_tree(p, b, v, i, b->child[x][1]));
}


/*
 * Check where P(b, v) is equal to p
 */
bool rba_buffer_equal_poly(rba_buffer_t *b, int32_t *v, polynomial_t *p) {
  uint32_t n;
  bool result;

  result = false;
  if (p->nterms == b->nterms) {
    n = 0;
    result = rba_equal_tree(p, b, v, &n, b->root);
    assert(!result || n == b->nterms);
  }

  return result;
}



/*
 * TYPE CHECKING
 */

/*
 * All functions use an external function to check the type of variables
 * - for every variable x, var_is_int(aux, x) must return true if x is
 *   integer, false if x is real.
 */


/*
 * Check whether monomial m is integral:
 */
static bool monomial_is_int(mono_t *m, void *aux, var_type_fun_t var_is_int) {
  pprod_t *p;
  uint32_t i, n;

  if (q_is_zero(&m->coeff)) {
    return true;
  }

  if (!q_is_integer(&m->coeff)) {
    return false;
  }

  p = m->prod;
  if (pp_is_empty(p)) {
    return true;
  }

  if (pp_is_var(p)) {
    return var_is_int(aux, var_of_pp(p));
  }

  n = p->len;
  for (i=0; i<n; i++) {
    if (! var_is_int(aux, p->prod[i].var)) {
      return false;
    }
  }

  return true;
}


/*
 * Check whether all monomials in x's subtree are integral
 */
static bool tree_is_int(rba_buffer_t *b, uint32_t x, void *aux, var_type_fun_t var_is_int) {
  return x == rba_null ||
    (monomial_is_int(b->mono + x, aux, var_is_int) &&
     tree_is_int(b, b->child[x][0], aux, var_is_int) &&
     tree_is_int(b, b->child[x][1], aux, var_is_int));
}

/*
 * Check whether b is an integral polynomial
 */
bool rba_buffer_is_int(rba_buffer_t *b, void *aux, var_type_fun_t var_is_int) {
  uint32_t i, n;

  if (rba_tree_is_small(b)) {
    return tree_is_int(b, b->root, aux, var_is_int);
  } else {
    n = b->num_nodes;
    for (i=1; i<n; i++) {
      if (!monomial_is_int(&b->mono[i], aux, var_is_int)) {
        return false;
      }
    }
    return true;
  }
}
