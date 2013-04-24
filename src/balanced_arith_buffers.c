/*
 * BUFFER FOR ARITHMETIC OPERATIONS USING RED-BLACK TREES
 */

#include "bit_tricks.h"
#include "memalloc.h"
#include "balanced_arith_buffers.h"


/*
 * TREE MANIPULATIONS
 */

/*
 * When performing some operation f on the monomials stored in b, we
 * can either do a linear scan
 *
 *    for (i=0; i<b->num_nodes; i++) {
 *      f(b->mono + i)
 *    }
 * 
 * or we can traverse the tree using a recursive function.
 *
 * Linear scan has a cost of linear in num_nodes.
 *
 * Tree traversal has cost K * nterms * log(nterms) (approximately)
 * for some constant K>1.
 *
 * In most cases, the linear scan should be faster. But the recursive
 * scan will be faster if num_terms is really small compared to 
 * num_nodes. The following function is a heuristic that attempts to
 * determine when tree traversal is cheaper than linear scan.
 */
static bool rba_tree_is_small(rba_buffer_t *b) {
  uint32_t n, p;

  n = b->nterms;
  p = b->num_nodes;
  return n * binlog(n) < (p >> 3);
}


/*
 * Left-most and right-most leaves of the subtree rooted at i
 * - special case: return null if i is null
 */
static uint32_t leftmost_leaf(rba_buffer_t *b, uint32_t i) {
  uint32_t j;

  for (;;) {
    assert(0 <= i && i < b->num_nodes);
    j = b->child[i][0];
    if (j == rba_null) break;
    i = j;
  }
  return i;
}

static uint32_t rightmost_leaf(rba_buffer_t *b, uint32_t i) {
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
static inline uint32_t rba_main_idx(rba_buffer_t *b) {
  return rightmost_leaf(b, b->root);
}


/*
 * Index of the smallest monomial (or null if the tree is empty)
 */
static inline uint32_t rba_smallest_idx(rba_buffer_t *b) {
  return leftmost_leaf(b, b->root);
}


/*
 * Search for a node whose prod is equal to r
 * - return its index or rba_null if there's no such node
 */
static uint32_t rba_find_node(rba_buffer_t *b, pprod_t *r) {
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
static inline bool is_parent_node(rba_buffer_t *b, uint32_t p, uint32_t q) {
  assert(p < b->num_nodes && q < b->num_nodes);
  return b->child[p][0] == q || b->child[p][1] == q;
}

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
 * Inialize buffer
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
 * Extend: increase size by 50%
 */
static void extend_rba_buffer(rba_buffer_t *b) {
  uint32_t n;

  n = b->size + 1;
  n += (n >> 1);
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
    b->child[1][1] = rba_null;

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

  // we can free node i now
  rba_free_node(b, i);

  if (p == rba_null) {
    assert(b->root = i);
    b->root = j;
    mark_black(b, j);
  } else {
    k = child_index(b, p, i);
    b->child[p][k] = j;

    // we've deleted i but the color flag is still good
    if (is_black(b, i)) {
      rba_balance_after_delete(b, j, p);
    }
  }
}





/*
 * QUERIES
 */

/*
 * Root monomial
 */
static inline mono_t *root_mono(rba_buffer_t *b) {
  return b->mono + b->root;
}

/*
 * Check whether b is a constant
 */
bool rba_buffer_is_constant(rba_buffer_t *b) {
  return b->nterms == 0 || (b->nterms == 1 && root_mono(b)->prod == empty_pp);
}

/*
 * Check whether b is constant and nonzero
 * - b must be normalized
 */
bool rba_buffer_is_nonzero(rba_buffer_t *b) {
  return b->nterms == 1 && root_mono(b)->prod == empty_pp;
}


/*
 * Check whether b is constant and positive, negative, etc.
 * - b must be normalized
 */
bool rba_buffer_is_pos(rba_buffer_t *b) {
  mono_t *r;
  r = root_mono(b);
  return b->nterms == 1 && r->prod == empty_pp && q_is_pos(&r->coeff);
}

bool rba_buffer_is_neg(rba_buffer_t *b) {
  mono_t *r;
  r = root_mono(b);
  return b->nterms == 1 && r->prod == empty_pp && q_is_neg(&r->coeff);
}

bool rba_buffer_is_nonneg(rba_buffer_t *b) {
  mono_t *r;
  r = root_mono(b);
  return b->nterms == 1 && r->prod == empty_pp && q_is_nonneg(&r->coeff);
}

bool rba_buffer_is_nonpos(rba_buffer_t *b) {
  mono_t *r;
  r = root_mono(b);
  return b->nterms == 1 && r->prod == empty_pp && q_is_nonpos(&r->coeff);
}


/*
 * Check whether b is of the form 1 * X for a non-null power-product X
 * If so return X in *r
 */
bool rba_buffer_is_product(rba_buffer_t *b, pprod_t **r) {
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
bool rba_buffer_is_equality(rba_buffer_t *b, pprod_t **r1, pprod_t **r2) {
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
mono_t *rba_buffer_main_mono(rba_buffer_t *b) {
  assert(b->nterms > 0);
  return b->mono +  rba_main_idx(b);
}


/*
 * Main term
 */
pprod_t *rba_buffer_main_term(rba_buffer_t *b) {
  return rba_buffer_main_mono(b)->prod;
}


/*
 * Get degree of polynomial in buffer b.
 * - returns 0 if b is zero
 */
uint32_t rba_buffer_degree(rba_buffer_t *b) {
  return (b->nterms == 0) ? 0 : pprod_degree(rba_buffer_main_term(b));
}


/*
 * Degree of x in b
 * - return 0 if x does not occur in b
 */

// return max(d, degree of x in subtree of root i)
static uint32_t tree_var_degree(rba_buffer_t *b, int32_t x, uint32_t i, uint32_t d) {
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

uint32_t rba_buffer_var_degree(rba_buffer_t *b, int32_t x) {
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
mono_t *rba_buffer_get_constant_mono(rba_buffer_t *b) {
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
 * Convert b to a polynomial then reset b
 * - v = array of variables
 */
