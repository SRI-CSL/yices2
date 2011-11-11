/*
 * BIT-VECTOR SOLVER (BASELINE)
 */

#include <assert.h>

#include "memalloc.h"
#include "hash_functions.h"
#include "bv64_constants.h"
#include "small_bvsets.h"
#include "rb_bvsets.h"
#include "int_powers.h"

#include "bvsolver.h"


/*****************
 *  BOUND QUEUE  *
 ****************/

/*
 * Initialize the queue: initial size = 0
 */
static void init_bv_bound_queue(bv_bound_queue_t *queue) {
  queue->data = NULL;
  queue->top = 0;
  queue->size = 0;  
  queue->bound = NULL;
  queue->bsize = 0;
}


/*
 * Allocate the data array of make it 50% larger
 */
static void bv_bound_queue_extend(bv_bound_queue_t *queue) {
  uint32_t n;

  n = queue->size;
  if (n == 0) {
    n = DEF_BV_BOUND_QUEUE_SIZE;
    assert(n <= MAX_BV_BOUND_QUEUE_SIZE);
    queue->data = (bv_bound_t *) safe_malloc(n * sizeof(bv_bound_t));
    queue->size = n;

  } else {
    n += (n >> 1); // 50% larger
    assert(n > queue->size);
    if (n > MAX_BV_BOUND_QUEUE_SIZE) {
      out_of_memory();
    }
    queue->data = (bv_bound_t *) safe_realloc(queue->data, n * sizeof(bv_bound_t));
    queue->size = n;
  }
}


/*
 * Make the bound array large enough to store bound[x]
 * - x must be a variable index (between 0 and MAX_BV_BOUND_NUM_LISTS)
 * - this should be called when x >= queue->bsize
 */
static void bv_bound_queue_resize(bv_bound_queue_t *queue, thvar_t x) {
  uint32_t i, n;
  int32_t *tmp;

  assert(x >= queue->bsize);

  n = queue->bsize;
  if (n == 0) {
    n = DEF_BV_BOUND_NUM_LISTS;
  } else {
    n += (n >> 1);
    assert(n > queue->bsize);
  }

  if (n <= (uint32_t) x) {
    n = x + 1;
  }

  if (n > MAX_BV_BOUND_NUM_LISTS) {
    out_of_memory();
  }

  tmp = (int32_t *) safe_realloc(queue->bound, n * sizeof(int32_t));
  for (i=queue->size; i<n; i++) {
    tmp[i] = -1;
  }

  queue->bound = tmp;
  queue->bsize = n;
}


/*
 * Add a bound for variable x:
 * - id = the atom index
 */
static void bv_bound_queue_push(bv_bound_queue_t *queue, thvar_t x, int32_t id) {
  int32_t k, i;

  if (x >= queue->bsize) {
    bv_bound_queue_resize(queue, x);
    assert(x < queue->bsize);
  }

  k = queue->bound[x];
  assert(-1 <= k && k < (int32_t) queue->top);

  i = queue->top;
  if (i == queue->size) {
    bv_bound_queue_extend(queue);
  }
  assert(i < queue->size);

  queue->data[i].atom_id = id;
  queue->data[i].pre = k;
  queue->bound[x] = i;

  queue->top = i+1;
}



/*
 * Delete the queue
 */
static void delete_bv_bound_queue(bv_bound_queue_t *queue) {
  safe_free(queue->data);
  safe_free(queue->bound);
  queue->data = NULL;
  queue->bound = NULL;
}


/*
 * Empty the queue
 */
static void reset_bv_bound_queue(bv_bound_queue_t *queue) {
  uint32_t i, n;

  n = queue->bsize;
  for (i=0; i<n; i++) {
    queue->bound[i] = -1;
  }
  queue->top = 0;
}




/********************
 *  PUSH/POP STACK  *
 *******************/

/*
 * Initialize the stack: initial size = 0
 */
static void init_bv_trail(bv_trail_stack_t *stack) {
  stack->size = 0;
  stack->top = 0;
  stack->data = NULL;
}



/*
 * Save a base level
 * - nv = number of variables
 * - na = number of atoms
 * - nb = number of bounds
 */
static void bv_trail_save(bv_trail_stack_t *stack, uint32_t nv, uint32_t na, uint32_t nb) {
  uint32_t i, n;

  i = stack->top;
  n = stack->size;
  if (i == n) {
    if (n == 0) {
      n = DEF_BV_TRAIL_SIZE;
      assert(0<n &&  n<MAX_BV_TRAIL_SIZE);
    } else {
      n += n;
      if (n >= MAX_BV_TRAIL_SIZE) {
	out_of_memory();
      }
    }
    stack->data = (bv_trail_t *) safe_realloc(stack->data, n * sizeof(bv_trail_t));
    stack->size = n;
  }
  assert(i < stack->size);

  stack->data[i].nvars = nv;
  stack->data[i].natoms = na;
  stack->data[i].nbounds = nb;

  stack->top = i+1;
}


/*
 * Get the top trail record
 */
static bv_trail_t *bv_trail_top(bv_trail_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data + (stack->top - 1);
}


/*
 * Remove the top record
 */
static inline void bv_trail_pop(bv_trail_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}


/*
 * Delete the stack
 */
static inline void delete_bv_trail(bv_trail_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Empty the stack
 */
static inline void reset_bv_trail(bv_trail_stack_t *stack) {
  stack->top = 0;
}





/*****************
 *  USED VALUES  *
 ****************/

/*
 * Initialize a used_vals array:
 * - initial size = 0
 */
static void init_used_vals(used_bvval_t *used_vals) {
  used_vals->data = NULL;
  used_vals->nsets = 0;
  used_vals->size = 0;
}


/*
 * Empty the array: delete all sets
 */
static void reset_used_vals(used_bvval_t *used_vals) {
  uint32_t i, n;

  n = used_vals->nsets;
  for (i=0; i<n; i++) {
    if (used_vals->data[i].bitsize <= SMALL_BVSET_LIMIT) {
      delete_small_bvset(used_vals->data[i].ptr);
    } else {
      delete_rb_bvset(used_vals->data[i].ptr);
    }
    safe_free(used_vals->data[i].ptr);
    used_vals->data[i].ptr = NULL;
  }

  used_vals->nsets = 0;
}


/*
 * Delete a used_vals array: free memory
 */
static void delete_used_vals(used_bvval_t *used_vals) {
  reset_used_vals(used_vals);
  safe_free(used_vals->data);
  used_vals->data = NULL;
}



#if 0

// NOT USED YET

/*
 * Allocate a set descriptor
 * - return its id
 */
static uint32_t used_vals_new_set(used_bvval_t *used_vals) {
  uint32_t i, n;

  i = used_vals->nsets;
  n = used_vals->size;
  if (i == n) {
    if (n == 0) {
      // first allocation: use the default size
      n = USED_BVVAL_DEF_SIZE;
      assert(n < USED_BVVAL_MAX_SIZE);
      used_vals->data = (bvset_t *) safe_malloc(n * sizeof(bvset_t));
      used_vals->size = n;
    } else {
      // make the array 50% larger
      n ++;
      n += n>>1;
      if (n >= USED_BVVAL_MAX_SIZE) {
	out_of_memory();
      }
      used_vals->data = (bvset_t *) safe_realloc(used_vals->data, n * sizeof(bvset_t));
      used_vals->size = n;
    }
  }

  assert(i < used_vals->size);
  used_vals->nsets = i+1;

  return i;
}


/*
 * Return the set descriptor for bit-vectors of size k
 * - allocate and initialize a new desciptor if necessary
 * - for a new descriptor, the internal small_set or red-black tree is NULL
 */ 
static bvset_t *used_vals_get_set(used_bvval_t *used_vals, uint32_t k) {
  uint32_t i, n;

  assert(k > 0);
  n = used_vals->nsets;
  for (i=0; i<n; i++) {
    if (used_vals->data[i].bitsize == k) {
      return used_vals->data + i;
    }
  }

  // allocate a new descriptor
  i = used_vals_new_set(used_vals);
  used_vals->data[i].bitsize = k;
  used_vals->data[i].ptr = NULL;

  return used_vals->data + i;
}


/*
 * Allocate a new small_bvset for size k and initialize it
 */
static small_bvset_t *new_small_bvset(uint32_t k) {
  small_bvset_t *tmp;

  assert(0 < k && k <= SMALL_BVSET_LIMIT);
  tmp = (small_bvset_t *) safe_malloc(sizeof(small_bvset_t));
  init_small_bvset(tmp, k);

  return tmp;
}


/*
 * Allocate a red-black tree for bitvectors of size k
 * and initialize it.
 */
static rb_bvset_t *new_rb_bvset(uint32_t k) {
  rb_bvset_t *tmp;

  assert(k > SMALL_BVSET_LIMIT);
  tmp = (rb_bvset_t *) safe_malloc(sizeof(rb_bvset_t));
  init_rb_bvset(tmp, k);

  return tmp;
}

#endif


/********************************
 *  MAPPING TO PSEUDO LITERALS  *
 *******************************/

/*
 * Return the remap table (allocate and initialize it if necessary)
 */
static remap_table_t *bv_solver_get_remap(bv_solver_t *solver) {
  remap_table_t *tmp;

  tmp = solver->remap;
  if (tmp == NULL) {
    tmp = (remap_table_t *) safe_malloc(sizeof(remap_table_t));
    init_remap_table(tmp);
    solver->remap = tmp;
  }

  return tmp;
}


/*
 * Return the pseudo literal array mapped to x
 * - allocate a new array of n literals if x is not mapped yet
 */
static literal_t *bv_solver_get_pseudo_map(bv_solver_t *solver, thvar_t x) {
  remap_table_t *rmap;
  literal_t *tmp;
  uint32_t n;

  tmp = bvvar_get_map(&solver->vtbl, x);
  if (tmp == NULL) {
    n = bvvar_bitsize(&solver->vtbl, x);
    rmap = bv_solver_get_remap(solver);
    tmp = remap_table_fresh_array(rmap, n);
    bvvar_set_map(&solver->vtbl, x, tmp);
  }

  return tmp;
}



/******************
 *  BOUND ATOMS   *
 *****************/

/*
 * Check whether x is a constant
 */
static inline bool is_constant(bv_vartable_t *table, thvar_t x) {
  bvvar_tag_t tag;

  tag = bvvar_tag(table, x);
  return (tag == BVTAG_CONST64) | (tag == BVTAG_CONST);
}


/*
 * Check wether x or y is a constant
 */
static inline bool is_bv_bound_pair(bv_vartable_t *table, thvar_t x, thvar_t y) {
  bvvar_tag_t tag_x, tag_y;

  tag_x = bvvar_tag(table, x);
  tag_y = bvvar_tag(table, y);

  return (tag_x == BVTAG_CONST64) | (tag_x == BVTAG_CONST)
    | (tag_y == BVTAG_CONST64) | (tag_y == BVTAG_CONST);
}



/*
 * Check whether atom i is a 'bound atom' (i.e., inequality between
 * a constant and a non-constant).
 * - all atoms are of the form (op x y), we just check whether x
 *   or y is a bitvector constant.
 * - this is fine since no atom should involve two constants
 *   (constraints between constants are always simplified to true or false)
 */
static inline bool is_bound_atom(bv_solver_t *solver, int32_t i) {
  bvatm_t *a;
  
  a = bvatom_desc(&solver->atbl, i);
  return is_constant(&solver->vtbl, a->left) || is_constant(&solver->vtbl, a->right);
}


/*
 * Get the constant and variable in a bound atom
 */
#if 0
// NOT USED
static thvar_t bound_atom_const(bv_solver_t *solver, int32_t i) {
  bvatm_t *a;
  thvar_t c;
  
  a = bvatom_desc(&solver->atbl, i);
  c = a->left;
  if (! is_constant(&solver->vtbl, c)) {
    c = a->right;
  }

  assert(is_constant(&solver->vtbl, c));

  return c;
}
#endif

static thvar_t bound_atom_var(bv_solver_t *solver, int32_t i) {
  bvatm_t *a;
  thvar_t x;
  
  a = bvatom_desc(&solver->atbl, i);
  x = a->left;
  if (is_constant(&solver->vtbl, x)) {
    x = a->right;
  }

  assert(! is_constant(&solver->vtbl, x));

  return x;
}



/*
 * Add (bvge x y) to the bound queue
 * - either x or y must be a constant
 *   and the atom (bvge x y) must exist in the atom table
 */
static void push_bvuge_bound(bv_solver_t *solver, thvar_t x, thvar_t y) {
  int32_t i;

  assert(is_bv_bound_pair(&solver->vtbl, x, y));

  i = find_bvuge_atom(&solver->atbl, x, y);
  assert(i >= 0 && is_bound_atom(solver, i));
  if (is_constant(&solver->vtbl, x)) {
    x = y;
  }

  assert(! is_constant(&solver->vtbl, x));
  bv_bound_queue_push(&solver->bqueue, x, i);
}


/*
 * Same thing for (bvsge x y)
 */
static void push_bvsge_bound(bv_solver_t *solver, thvar_t x, thvar_t y) {
  int32_t i;

  assert(is_bv_bound_pair(&solver->vtbl, x, y));

  i = find_bvsge_atom(&solver->atbl, x, y);
  assert(i >= 0 && is_bound_atom(solver, i));
  if (is_constant(&solver->vtbl, x)) {
    x = y;
  }

  assert(! is_constant(&solver->vtbl, x));
  bv_bound_queue_push(&solver->bqueue, x, i);
}


/*
 * Same thing for (eq x y) (this is used for (x != 0) or (y != 0))
 */
static void push_bvdiseq_bound(bv_solver_t *solver, thvar_t x, thvar_t y) {
  int32_t i;

  assert(is_bv_bound_pair(&solver->vtbl, x, y));

  i = find_bveq_atom(&solver->atbl, x, y);
  assert(i >= 0 && is_bound_atom(solver, i));
  if (is_constant(&solver->vtbl, x)) {
    x = y;
  }

  assert(! is_constant(&solver->vtbl, x));
  bv_bound_queue_push(&solver->bqueue, x, i);
}


/*
 * Remove all bounds of index >= n
 */
static void bv_solver_remove_bounds(bv_solver_t *solver, uint32_t n) {
  bv_bound_queue_t *queue;
  bv_bound_t *d;
  uint32_t i;
  thvar_t x;

  queue = &solver->bqueue;
  assert(0 <= n && n <= queue->top);

  i = queue->top;
  d = queue->data + i;
  while (i > n) {
    i --;
    d --;
    x = bound_atom_var(solver, d->atom_id);
    assert(0 <= x && x < queue->bsize);
    queue->bound[x] = d->pre;
  }

  queue->top = n;
}




/**********************
 *  VARIABLE MERGING  *
 *********************/

/*
 * We attempt to keep the simplest element of the class as
 * root of its class, using the following ranking:
 * - constants are simplest:       rank 0
 * - bvarray are next              rank 1
 * - polynomials                   rank 2
 * - power products                rank 3
 * - other non-variable terms:     rank 4
 * - variables are last            rank 5
 *
 * The following functions checks whether a is striclty simpler than b
 * based on this ranking.
 */
static const uint8_t bvtag2rank[NUM_BVTAGS] = {
  5,      // BVTAG_VAR
  0,      // BVTAG_CONST64
  0,      // BVTAG_CONST
  2,      // BVTAG_POLY64
  2,      // BVTAG_POLY
  3,      // BVTAG_PPROD
  1,      // BVTAG_BIT_ARRAY
  4,      // BVTAG_ITE
  4,      // BVTAG_UDIV
  4,      // BVTAG_UREM
  4,      // BVTAG_SDIV
  4,      // BVTAG_SREM
  4,      // BVTAG_SMOD
  4,      // BVTAG_SHL
  4,      // BVTAG_LSHR
  4,      // BVTAG_ASHR
};

static inline bool simpler_bvtag(bvvar_tag_t a, bvvar_tag_t b) {
  return bvtag2rank[a] < bvtag2rank[b];
}


/*
 * Check whether tag is for a constant
 */
static inline bool constant_bvtag(bvvar_tag_t a) {
  return a == BVTAG_CONST64 || a == BVTAG_CONST;
}



/*
 * Merge the equivalence classes of x and y
 * - both x and y must be root of their class
 * - x and y must be distinct variables
 */
static void bv_solver_merge_vars(bv_solver_t *solver, thvar_t x, thvar_t y) {
  mtbl_t *mtbl;
  bvvar_tag_t tag_x, tag_y;
  thvar_t aux;

  mtbl = &solver->mtbl;

  assert(x != y && mtbl_is_root(mtbl, x) && mtbl_is_root(mtbl, y));

  tag_x = bvvar_tag(&solver->vtbl, x);
  tag_y = bvvar_tag(&solver->vtbl, y);

  if (simpler_bvtag(tag_y, tag_x)) {
    aux = x; x = y; y = aux;
  }

  // x is simpler than y, we set map[y] := x
  mtbl_map(mtbl, y, x);
}



/*
 * Check whether the root of x's class is a 64bit constant
 * - if so return the root, otherwise return x
 */
static thvar_t bvvar_root_if_const64(bv_solver_t *solver, thvar_t x) {
  thvar_t y;

  y = mtbl_get_root(&solver->mtbl, x);
  if (bvvar_is_const64(&solver->vtbl, y)) {
    x = y;
  }

  return x;
}


/*
 * Check whether the root of x's class is a generic constant
 * - if so return the root, otherwise return x
 */
static thvar_t bvvar_root_if_const(bv_solver_t *solver, thvar_t x) {
  thvar_t y;

  y = mtbl_get_root(&solver->mtbl, x);
  if (bvvar_is_const(&solver->vtbl, y)) {
    x = y;
  }

  return x;
}




/*
 * Check whether x is equal to 0b0000...
 */
static bool bvvar_is_zero(bv_vartable_t *vtbl, thvar_t x) {  
  uint32_t n, k;

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST64:
    return bvvar_val64(vtbl, x) == 0;

  case BVTAG_CONST:
    n = bvvar_bitsize(vtbl, x);
    k = (n + 31) >> 5;
    return bvconst_is_zero(bvvar_val(vtbl, x), k);

  default:
    return false;
  }
}


/*
 * Check whether x is equal to 0b1111...
 */
static bool bvvar_is_minus_one(bv_vartable_t *vtbl, thvar_t x) {  
  uint32_t n;

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST64:
    n = bvvar_bitsize(vtbl, x);
    return bvconst64_is_minus_one(bvvar_val64(vtbl, x), n);

  case BVTAG_CONST:
    n = bvvar_bitsize(vtbl, x);
    return bvconst_is_minus_one(bvvar_val(vtbl, x), n);

  default:
    return false;
  }
}


/*
 * Check whether x is equal to 0b1000...
 */
static bool bvvar_is_min_signed(bv_vartable_t *vtbl, thvar_t x) {
  uint32_t n;

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST64:
    n = bvvar_bitsize(vtbl, x);
    return bvvar_val64(vtbl, x) == min_signed64(n);

  case BVTAG_CONST:
    n = bvvar_bitsize(vtbl, x);
    return bvconst_is_min_signed(bvvar_val(vtbl, x), n);

  default:
    return false;
  }
}


/*
 * Check whether x is equal to 0b0111...
 */
static bool bvvar_is_max_signed(bv_vartable_t *vtbl, thvar_t x) {
  uint32_t n;

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST64:
    n = bvvar_bitsize(vtbl, x);
    return bvvar_val64(vtbl, x) == max_signed64(n);

  case BVTAG_CONST:
    n = bvvar_bitsize(vtbl, x);
    return bvconst_is_max_signed(bvvar_val(vtbl, x), n);

  default:
    return false;
  }
}



/*********************
 *  EQUALITY CHECKS  *
 ********************/

/*
 * Check whether two variables x and y are equal
 * - x and y must be the roots of their equivalence class in the merge table
 */
static inline bool equal_bvvar(bv_solver_t *solver, thvar_t x, thvar_t y) {
  assert(bvvar_bitsize(&solver->vtbl, x) == bvvar_bitsize(&solver->vtbl, y));
  assert(mtbl_is_root(&solver->mtbl, x) && mtbl_is_root(&solver->mtbl, y));

  /*
   * TODO: check for equality between arithmetic expressions
   * (using associativity, distributivity)
   */

  return x == y;
}


/************************
 *  DISEQUALITY CHECKS  *
 ***********************/

/*
 * Check whether two bitarrays a and b are distinct
 * - n = size of both arrays
 * - for now, this returns true if there's an 
 *   index i such that a[i] = not b[i]
 */
static bool diseq_bitarrays(literal_t *a, literal_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (opposite(a[i], b[i])) {
      return true;
    }
  }

  return false;
}


/*
 * Check whether bit array a and small constant c must differ.
 * - n = number of bits in a (and c)
 */
static bool diseq_bitarray_const64(literal_t *a, uint64_t c, uint32_t n) {
  uint32_t i;

  assert(n <= 64);

  /*
   * We use the fact that true_literal = 0 and false_literal = 1
   * So (bit i of c) == a[i] implies a != c
   */
  assert(true_literal == 0 && false_literal == 1);
  
  for (i=0; i<n; i++) {
    if (((int32_t) (c & 1)) == a[i]) {
      return true;
    }
    c >>= 1;
  }

  return false;  
}


/*
 * Same thing for a constant c with more than 64bits
 */
static bool diseq_bitarray_const(literal_t *a, uint32_t *c, uint32_t n) {
  uint32_t i;

  assert(n >= 64);

  /*
   * Same trick as above:
   * - bvconst_tst_bit(c, i) = bit i of c = either 0 or 1
   */
  assert(true_literal == 0 && false_literal == 1);

  for (i=0; i<n; i++) {
    if (bvconst_tst_bit(c, i) == a[i]) {
      return true;
    }
  }

  return false;
}


/*
 * Top-level disequality check
 * - x and y must be roots of their equivalence class in the merge table
 */
static bool diseq_bvvar(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvvar_tag_t tag_x, tag_y;
  uint32_t n;

  assert(bvvar_bitsize(&solver->vtbl, x) == bvvar_bitsize(&solver->vtbl, y));
  assert(mtbl_is_root(&solver->mtbl, x) && mtbl_is_root(&solver->mtbl, y));

  if (x == y) return false;

  vtbl = &solver->vtbl;
  tag_x = bvvar_tag(vtbl, x);
  tag_y = bvvar_tag(vtbl, y);

  if (tag_x == tag_y) {
    switch (tag_x) {
    case BVTAG_CONST64:
    case BVTAG_CONST:
      return true;

    case BVTAG_POLY64:
      return disequal_bvpoly64(bvvar_poly64_def(vtbl, x), bvvar_poly64_def(vtbl, y));

    case BVTAG_POLY:
      return disequal_bvpoly(bvvar_poly_def(vtbl, x), bvvar_poly_def(vtbl, y));

    case BVTAG_BIT_ARRAY:
      n = bvvar_bitsize(vtbl, x);
      return diseq_bitarrays(bvvar_bvarray_def(vtbl, x), bvvar_bvarray_def(vtbl, y), n);

    default:
      break;
    }

  } else {

    n = bvvar_bitsize(vtbl, x);
    if (n <= 64) {
      if (tag_x == BVTAG_CONST64 && tag_y == BVTAG_BIT_ARRAY) {
	return diseq_bitarray_const64(bvvar_bvarray_def(vtbl, y), bvvar_val64(vtbl, x), n);
      }

      if (tag_y == BVTAG_CONST64 && tag_x == BVTAG_BIT_ARRAY) {
	return diseq_bitarray_const64(bvvar_bvarray_def(vtbl, x), bvvar_val64(vtbl, y), n);
      }
      
      if (tag_x == BVTAG_POLY64 && tag_y != BVTAG_CONST64) {
	return bvpoly64_is_const_plus_var(bvvar_poly64_def(vtbl, x), y);
      }

      if (tag_y == BVTAG_POLY64 && tag_x != BVTAG_CONST64) {
	return bvpoly64_is_const_plus_var(bvvar_poly64_def(vtbl, y), x);
      }

    } else {
      if (tag_x == BVTAG_CONST && tag_y == BVTAG_BIT_ARRAY) {
	return diseq_bitarray_const(bvvar_bvarray_def(vtbl, y), bvvar_val(vtbl, x), n);
      }

      if (tag_y == BVTAG_CONST && tag_x == BVTAG_BIT_ARRAY) {
	return diseq_bitarray_const(bvvar_bvarray_def(vtbl, x), bvvar_val(vtbl, y), n);
      }
      
      if (tag_x == BVTAG_POLY && tag_y != BVTAG_CONST) {
	return bvpoly_is_const_plus_var(bvvar_poly_def(vtbl, x), y);
      }

      if (tag_y == BVTAG_POLY && tag_x != BVTAG_CONST) {
	return bvpoly_is_const_plus_var(bvvar_poly_def(vtbl, y), x);
      }
      
    }
  }
  
  return false;
}



/*******************
 *  INEQUALITIES   *
 ******************/

/*
 * LOWER AND UPPER BOUNDS (for bitvectors of no more than 64bits)
 */

/*
 * Compute a lower or upper bound on a bitarray a
 * - n = number of bits in a. n must be no more than 64
 * - the result is returned as a 64bit unsigned integer, normalized modulo 2^n
 *   (if n < 64, then the high-order bits are set to 0)
 */
static uint64_t bitarray_upper_bound_unsigned64(literal_t *a, uint32_t n) {
  uint64_t c;
  uint32_t i;

  assert(0 < n && n <= 64);
  c = mask64(n);    // all bits equal to 1
  for (i=0; i<n; i++) {
    if (a[i] == false_literal) {
      c = clr_bit64(c, i);
    }
  }
  return c;
}


static uint64_t bitarray_lower_bound_unsigned64(literal_t *a, uint32_t n) {
  uint64_t c;
  uint32_t i;

  assert(0 < n && n <= 64);
  c = 0;    // all bits equal to 0
  for (i=0; i<n; i++) {
    if (a[i] == true_literal) { 
      c = set_bit64(c, i);
    }
  }
  return c;
}


static uint64_t bitarray_upper_bound_signed64(literal_t *a, uint32_t n) {
  uint64_t c;
  uint32_t i;

  assert(0 < n && n <= 64);
  c = mask64(n);   // all bits equal to 1
  for (i=0; i<n-1; i++) {
    if (a[i] == false_literal) {
      c = clr_bit64(c, i);
    }
  }

  // test the sign bit
  if (a[i] != true_literal) { // i.e. sign bit may be 0
    c = clr_bit64(c, i);
  }

  return c;
}


static uint64_t bitarray_lower_bound_signed64(literal_t *a, uint32_t n) {
  uint64_t c;
  uint32_t i;

  assert(0 < n && n <= 64);
  c = 0;

  for (i=0; i<n-1; i++) {
    if (a[i] == true_literal) {
      c = set_bit64(c, i);
    }
  }

  // sign bit
  if (a[i] != false_literal) { // sign bit may be 1
    c = set_bit64(c, i);
  }

  return c;
}


/*
 * Lower/upper bound for a bitvector variable x
 * - n = bitsize of x: must be between 1 and 64
 */
static uint64_t bvvar_upper_bound_unsigned64(bv_solver_t *solver, thvar_t x, uint32_t n) {
  bv_vartable_t *vtbl;
  uint64_t c;

  vtbl = &solver->vtbl;

  assert(valid_bvvar(vtbl, x) && n == bvvar_bitsize(vtbl, x) && 1 <= n && n <= 64);

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST64:
    c = bvvar_val64(vtbl, x);
    break;

  case BVTAG_BIT_ARRAY:
    c = bitarray_upper_bound_unsigned64(bvvar_bvarray_def(vtbl, x), n);
    break;

  default:
    c = mask64(n); // all bits equal to 1
    break;
  }

  assert(c == norm64(c, n));

  return c;
}


static uint64_t bvvar_lower_bound_unsigned64(bv_solver_t *solver, thvar_t x, uint32_t n) {
  bv_vartable_t *vtbl;
  uint64_t c;

  vtbl = &solver->vtbl;

  assert(valid_bvvar(vtbl, x) && n == bvvar_bitsize(vtbl, x) && 1 <= n && n <= 64);

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST64:
    c = bvvar_val64(vtbl, x);
    break;

  case BVTAG_BIT_ARRAY:
    c = bitarray_lower_bound_unsigned64(bvvar_bvarray_def(vtbl, x), n);
    break;

  default:
    c = 0;
    break;
  }

  assert(c == norm64(c, n));

  return c;
}


static uint64_t bvvar_upper_bound_signed64(bv_solver_t *solver, thvar_t x, uint32_t n) {
  bv_vartable_t *vtbl;
  uint64_t c;

  vtbl = &solver->vtbl;

  assert(valid_bvvar(vtbl, x) && n == bvvar_bitsize(vtbl, x) && 1 <= n && n <= 64);

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST64:
    c = bvvar_val64(vtbl, x);
    break;

  case BVTAG_BIT_ARRAY:
    c = bitarray_upper_bound_signed64(bvvar_bvarray_def(vtbl, x), n);
    break;

  default:
    c = max_signed64(n); // 0b011111..1
    break;
  }

  assert(c == norm64(c, n));

  return c;
}


static uint64_t bvvar_lower_bound_signed64(bv_solver_t *solver, thvar_t x, uint32_t n) {
  bv_vartable_t *vtbl;
  uint64_t c;

  vtbl = &solver->vtbl;

  assert(valid_bvvar(vtbl, x) && n == bvvar_bitsize(vtbl, x) && 1 <= n && n <= 64);

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST64:
    c = bvvar_val64(vtbl, x);
    break;

  case BVTAG_BIT_ARRAY:
    c = bitarray_lower_bound_signed64(bvvar_bvarray_def(vtbl, x), n);
    break;

  default:
    c = min_signed64(n); // 0b100000..00
    break;
  }

  assert(c == norm64(c, n));

  return c;
}




/*
 * LOWER AND UPPER BOUNDS (bitvectors with more than 64bits)
 */

/*
 * Lower/upper bounds for a bit array:
 * - the result is stored in bvconstant_t buffer v
 * - n = number of bits (should be more than 64)
 */
static void bitarray_upper_bound_unsigned(literal_t *a, uint32_t n, bvconstant_t *v) {
  uint32_t i;

  bvconstant_set_all_one(v, n); // v := 0b11....11
  for (i=0; i<n; i++) {
    if (a[i] == false_literal) {
      bvconst_clr_bit(v->data, i);
    }
  }
}


static void bitarray_lower_bound_unsigned(literal_t *a, uint32_t n, bvconstant_t *v) {
  uint32_t i;

  bvconstant_set_all_zero(v, n); // v := 0b00000...0
  for (i=0; i<n; i++) {
    if (a[i] == true_literal) {
      bvconst_set_bit(v->data, i);
    }
  }
}


static void bitarray_upper_bound_signed(literal_t *a, uint32_t n, bvconstant_t *v) {
  uint32_t i;

  assert(n > 0);

  bvconstant_set_all_one(v, n); // v := 0b11....11
  for (i=0; i<n-1; i++) {
    if (a[i] == false_literal) {
      bvconst_clr_bit(v->data, i);
    }
  }

  // sign bit
  if (a[i] != true_literal) {
    bvconst_clr_bit(v->data, i);
  }
}

static void bitarray_lower_bound_signed(literal_t *a, uint32_t n, bvconstant_t *v) {
  uint32_t i;

  assert(n > 0);

  bvconstant_set_all_zero(v, n); // v := 0b0000000

  for (i=0; i<n-1; i++) {
    if (a[i] == true_literal) {
      bvconst_set_bit(v->data, i);
    }
  }

  // sign bit
  if (a[i] != false_literal) {
    bvconst_clr_bit(v->data, i);
  }
}



/*
 * Lower/upper bound for a bitvector variable x
 * - n = bitsize of x: must be between 1 and 64
 * - the result is stored in v
 */
static void bvvar_upper_bound_unsigned(bv_solver_t *solver, thvar_t x, uint32_t n, bvconstant_t *v) {
  bv_vartable_t *vtbl;

  vtbl = &solver->vtbl;

  assert(valid_bvvar(vtbl, x) && n == bvvar_bitsize(vtbl, x) && 64 < n);

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST:
    bvconstant_copy(v, n, bvvar_val(vtbl, x));
    break;

  case BVTAG_BIT_ARRAY:
    bitarray_upper_bound_unsigned(bvvar_bvarray_def(vtbl, x), n, v);
    break;

  default:
    bvconstant_set_all_one(v, n);
    break;
  }
}


static void bvvar_lower_bound_unsigned(bv_solver_t *solver, thvar_t x, uint32_t n, bvconstant_t *v) {
  bv_vartable_t *vtbl;

  vtbl = &solver->vtbl;

  assert(valid_bvvar(vtbl, x) && n == bvvar_bitsize(vtbl, x) && 64 < n);

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST:
    bvconstant_copy(v, n, bvvar_val(vtbl, x));
    break;

  case BVTAG_BIT_ARRAY:
    bitarray_lower_bound_unsigned(bvvar_bvarray_def(vtbl, x), n, v);
    break;

  default:
    bvconstant_set_all_zero(v, n);
    break;
  }
}


static void bvvar_upper_bound_signed(bv_solver_t *solver, thvar_t x, uint32_t n, bvconstant_t *v) {
  bv_vartable_t *vtbl;

  vtbl = &solver->vtbl;

  assert(valid_bvvar(vtbl, x) && n == bvvar_bitsize(vtbl, x) && 64 < n);

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST:
    bvconstant_copy(v, n, bvvar_val(vtbl, x));
    break;

  case BVTAG_BIT_ARRAY:
    bitarray_upper_bound_signed(bvvar_bvarray_def(vtbl, x), n, v);
    break;

  default:
    bvconstant_set_all_one(v, n);
    bvconst_clr_bit(v->data, n-1); // clear the sign bit
    break;
  }
}


static void bvvar_lower_bound_signed(bv_solver_t *solver, thvar_t x, uint32_t n, bvconstant_t *v) {
  bv_vartable_t *vtbl;

  vtbl = &solver->vtbl;

  assert(valid_bvvar(vtbl, x) && n == bvvar_bitsize(vtbl, x) && 64 < n);

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST:
    bvconstant_copy(v, n, bvvar_val(vtbl, x));
    break;

  case BVTAG_BIT_ARRAY:
    bitarray_lower_bound_signed(bvvar_bvarray_def(vtbl, x), n, v);
    break;

  default:
    bvconstant_set_all_zero(v, n);
    bvconst_set_bit(v->data, n-1); // set the sign bit
    break;
  }
}


/*
 * SIMPLIFY INEQUALITIES
 */

/*
 * Three possible codes returned by the 'check_bvuge' and 'check_bvsge' functions
 * - the order matters: we want BVTEST_FALSE = 0 = false and BVTEST_TRUE = 1= true
 */
typedef enum {
  BVTEST_FALSE = 0,
  BVTEST_TRUE,
  BVTEST_UNKNOWN,
} bvtest_code_t;



/*
 * Check whether (x >= y) simplifies (unsigned)
 * - x and y must be roots in the merge table
 * - Return BVTEST_FALSE if (x > y) is known to hold
 * - return BVTEST_TRUE  if (x >= y) is known to hold
 * - return BVTEST_UNKNOWN otherwise
 */
static bvtest_code_t check_bvuge(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bvconstant_t *va, *vb;
  uint64_t a, b;
  uint32_t n;

  assert(bvvar_bitsize(&solver->vtbl, x) == bvvar_bitsize(&solver->vtbl, y));
  assert(mtbl_is_root(&solver->mtbl, x) && mtbl_is_root(&solver->mtbl, y));

  if (x == y) return BVTEST_TRUE;

  n = bvvar_bitsize(&solver->vtbl, x);

  if (n <= 64) {

    a = bvvar_lower_bound_unsigned64(solver, x, n); // (x >= a)
    b = bvvar_upper_bound_unsigned64(solver, y, n); // (b >= y)
    if (a >= b) {
      // a >= b ==> x >= y
      return BVTEST_TRUE;
    }

    a = bvvar_upper_bound_unsigned64(solver, x, n); // (x <= a)
    b = bvvar_lower_bound_unsigned64(solver, y, n); // (b <= y) 
    if (a < b) {
      return BVTEST_FALSE;
    }

  } else {

    va = &solver->aux1;
    vb = &solver->aux2;

    bvvar_lower_bound_unsigned(solver, x, n, va); // (x >= va)
    bvvar_upper_bound_unsigned(solver, y, n, vb); // (vb >= y);
    if (bvconst_ge(va->data, vb->data, n)) {
      // va >= vb
      return BVTEST_TRUE;
    }

    bvvar_upper_bound_unsigned(solver, x, n, va); // (x <= va);
    bvvar_lower_bound_unsigned(solver, y, n, vb); // (vb <= y);
    if (bvconst_lt(va->data, vb->data, n)) {
      // va < vb
      return BVTEST_FALSE;
    }

  }

  return BVTEST_UNKNOWN;
}


/*
 * Check whether (x <= y) simplifies (signed)
 * - x and y must be roots in the merge table
 * - return BVTEST_FALSE if (x > y) is known to hold
 * - return BVTEST_TRUE  if (x >= y) is known to hold
 * - return BVTEST_UNKNOWN otherwise
 */
static bvtest_code_t check_bvsge(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bvconstant_t *va, *vb;
  uint64_t a, b;
  uint32_t n;

  assert(bvvar_bitsize(&solver->vtbl, x) == bvvar_bitsize(&solver->vtbl, y));
  assert(mtbl_is_root(&solver->mtbl, x) && mtbl_is_root(&solver->mtbl, y));

  if (x == y) return BVTEST_TRUE;
  
  n = bvvar_bitsize(&solver->vtbl, x);

  if (n <= 64) {
    a = bvvar_lower_bound_signed64(solver, x, n); // (x >= a)
    b = bvvar_upper_bound_signed64(solver, y, n); // (b >= y)
    if (signed64_ge(a, b, n)) {
      // a >= b ==> x >= y
      return BVTEST_TRUE;
    }

    a = bvvar_upper_bound_signed64(solver, x, n); // (x <= a)
    b = bvvar_lower_bound_signed64(solver, y, n); // (b <= y) 
    if (signed64_gt(b, a, n)) {
      // b > a ==> x < y
      return BVTEST_FALSE;
    }

  } else {
    va = &solver->aux1;
    vb = &solver->aux2;

    bvvar_lower_bound_signed(solver, x, n, va); // (x >= va)
    bvvar_upper_bound_signed(solver, y, n, vb); // (vb >= y);
    if (bvconst_sge(va->data, vb->data, n)) {
      // va >= vb
      return BVTEST_TRUE;
    }

    bvvar_upper_bound_signed(solver, x, n, va); // (x <= va);
    bvvar_lower_bound_signed(solver, y, n, vb); // (vb <= y);
    if (bvconst_slt(va->data, vb->data, n)) {
      // va < vb
      return BVTEST_FALSE;
    }

  }

  return BVTEST_UNKNOWN;
}




/*****************************************
 *  SIMPLIFICATION + TERM CONSTRUCTION   *
 ****************************************/

/*
 * Add a * x to buffer b
 * - replace x by its value if it's a constant
 * - also replace x by its root value if the root is a constant
 * - b, a, and x must all have the same bitsize
 */
static void bvbuffer_add_mono64(bv_solver_t *solver, bvpoly_buffer_t *b, thvar_t x, uint64_t a) {
  bv_vartable_t *vtbl;
  thvar_t y;

  vtbl = &solver->vtbl;
  y = bvvar_root_if_const64(solver, x);
  if (bvvar_is_const64(vtbl, y)) {
    bvpoly_buffer_add_const64(b, a * bvvar_val64(vtbl, y));
  } else {
    bvpoly_buffer_add_mono64(b, x, a);
  }
}

// same thing for bitsize > 64
static void bvbuffer_add_mono(bv_solver_t *solver, bvpoly_buffer_t *b, thvar_t x, uint32_t *a) {
  bv_vartable_t *vtbl;
  thvar_t y;

  vtbl = &solver->vtbl;
  y = bvvar_root_if_const(solver, x);
  if (bvvar_is_const(vtbl, y)) {
    // add const_idx * a * value of y
    bvpoly_buffer_addmul_monomial(b, const_idx, a, bvvar_val(vtbl, y));
  } else {
    bvpoly_buffer_add_monomial(b, x, a);
  }
}


/*
 * Build the variable for a polynomial stored in buffer:
 * - check whether buffer is reduced to a constant or a variable
 */
static thvar_t map_bvpoly(bv_solver_t *solver, bvpoly_buffer_t *b) {
  bv_vartable_t *vtbl;
  thvar_t x;
  uint32_t n, nbits;

  vtbl = &solver->vtbl;

  n = bvpoly_buffer_num_terms(b);
  nbits = bvpoly_buffer_bitsize(b);

  if (n == 0) {
    // return the constant 0b000...0 
    bvconstant_set_all_zero(&solver->aux1, nbits);
    x = get_bvconst(vtbl, nbits, solver->aux1.data);
    return x;
  }

  if (n == 1) {
    x = bvpoly_buffer_var(b, 0);
    if (x == const_idx) {
      // p is a constant 
      x = get_bvconst(vtbl, nbits, bvpoly_buffer_coeff(b, 0));
      return x;
    }

    if (bvconst_is_one(bvpoly_buffer_coeff(b, 0), (nbits + 31) >> 5)) {
      // p is equal to 1 . x
      return x;
    }
  }
   
  // no simplification
  x = get_bvpoly(vtbl, b);

  return x;
}


/*
 * Same thing for a polynomial with 64bit coefficients
 */
static thvar_t map_bvpoly64(bv_solver_t *solver, bvpoly_buffer_t *b) {
  bv_vartable_t *vtbl;
  thvar_t x;
  uint32_t n, nbits;

  vtbl = &solver->vtbl;

  n = bvpoly_buffer_num_terms(b);
  nbits = bvpoly_buffer_bitsize(b);
    
  if (n == 0) {
    // return the constant 0b000 ..0
    x = get_bvconst64(vtbl, nbits, 0);
    return x;
  }

  if (n == 1) {
    x = bvpoly_buffer_var(b, 0);
    if (x == const_idx) {
      // constant
      x = get_bvconst64(vtbl, nbits, bvpoly_buffer_coeff64(b, 0));
      return x;
    }

    if (bvpoly_buffer_coeff64(b, 0) == 1) {
      return x;
    }
  }

  // no simplification
  x = get_bvpoly64(vtbl, b);

  return x;
}



/*
 * Map a power product p to a variable
 * - nbits = number of bits in all variables of p
 * - return null_thvar if p is the empty product
 */
static thvar_t map_product(bv_vartable_t *table, uint32_t nbits, pp_buffer_t *p) {
  uint32_t n;
  thvar_t x;

  n = p->len;
  if (n == 0) {
    x = null_thvar;
  } else if (n == 1 && p->prod[0].exp == 1) {
    x = p->prod[0].var;
  } else {
    x = get_bvpprod(table, nbits, p);
  }

  return x;
}


/*
 * Build the term c * x (as a polynomial)
 * - nbits = number of bits in c and x
 */
static thvar_t make_mono64(bv_solver_t *solver, uint32_t nbits, uint64_t c, thvar_t x) {
  bvpoly_buffer_t *b;

  b = &solver->buffer;
  reset_bvpoly_buffer(b, nbits);
  bvpoly_buffer_add_mono64(b, x, c);

  return get_bvpoly64(&solver->vtbl, b);
}


/*
 * Build the term (c * p)
 * - c is a 64bit constants
 * - p is a power product
 * - nbits = number of bits in c (and in all variables of p)
 */
static thvar_t map_const64_times_product(bv_solver_t *solver, uint32_t nbits, pp_buffer_t *p, uint64_t c) {
  bv_vartable_t *vtbl;
  thvar_t x;

  assert(c == norm64(c, nbits));

  vtbl = &solver->vtbl;

  if (c == 0) {
    x = get_bvconst64(vtbl, nbits, 0);
  } else {
    x = map_product(vtbl, nbits, p);
    if (x == null_thvar) { 
      // empty product: p = 1
      x = get_bvconst64(vtbl, nbits, c);
    } else if (c != 1) {
      x = make_mono64(solver, nbits, c, x);
    }
  }

  return x;
}



/*
 * Build the term c * x (as a polynomial)
 * - nbits = number of bits in c and x (nbits > 64)
 * - c must be normalized
 */
static thvar_t make_mono(bv_solver_t *solver, uint32_t nbits, uint32_t *c, thvar_t x) {
  bvpoly_buffer_t *b;

  b = &solver->buffer;
  reset_bvpoly_buffer(b, nbits);
  bvpoly_buffer_add_monomial(b, x, c);

  return get_bvpoly(&solver->vtbl, b);
}


/*
 * Build the term (c * p)
 * - c is a constants with more than 64bits
 * - p is a power product
 * - nbits = number of bits in c (and in all variables of p)
 */
static thvar_t map_const_times_product(bv_solver_t *solver, uint32_t nbits, pp_buffer_t *p, uint32_t *c) {
  bv_vartable_t *vtbl;
  uint32_t w;
  thvar_t x;

  vtbl = &solver->vtbl;
  w = (nbits + 31) >> 5;

  if (bvconst_is_zero(c, w)) {
    x = get_bvconst(vtbl, nbits, c); // constant 0b0000...0
  } else {
    x = map_product(vtbl, nbits, p);
    if (x == null_thvar) { 
      // empty product: p = 1
      x = get_bvconst(vtbl, nbits, c);
    } else if (! bvconst_is_one(c, w)) {
      x = make_mono(solver, nbits, c, x);
    }
  }

  return x;
}



/*
 * Check whether all literals in a[0 ... n-1] are constant
 */
static bool bvarray_is_constant(literal_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (var_of(a[i]) != const_bvar) return false;
  }

  return true;
}


/*
 * Convert constant array a[0 ... n-1] to a 64bit unsigned integer
 * - a[0] = low order bit
 * - a[n-1] = high order bit
 */
static uint64_t bvarray_to_uint64(literal_t *a, uint32_t n) {
  uint64_t c;

  assert(1 <= n && n <= 64);
  c = 0;
  while (n > 0) {
    n --;
    assert(a[n] == true_literal || a[n] == false_literal);
    c = (c << 1) | is_pos(a[n]);
  }

  return c;
}


/*
 * Convert constant array a[0 ... n-1] to a bitvecotr constant
 * - copy the result in c
 */
static void bvarray_to_bvconstant(literal_t *a, uint32_t n, bvconstant_t *c) {
  uint32_t i;

  assert(n > 64);

  bvconstant_set_all_zero(c, n);
  for (i=0; i<n; i++) {
    assert(a[i] == true_literal || a[i] == false_literal);
    if (a[i] == true_literal) {
      bvconst_set_bit(c->data, i);
    }
  }
}



/*
 * Extract bit i of a 64bit constant x
 * - convert to true_literal or false_literal
 */
static literal_t bvconst64_get_bit(bv_vartable_t *vtbl, thvar_t x, uint32_t i) {
  literal_t l;
  
  l = false_literal;
  if (tst_bit64(bvvar_val64(vtbl, x), i)) {
    l= true_literal;
  } 

  return l;
}


/*
 * Extract bit i of a general constant x
 */
static literal_t bvconst_get_bit(bv_vartable_t *vtbl, thvar_t x, uint32_t i) {
  literal_t l;

  l = false_literal;
  if (bvconst_tst_bit(bvvar_val(vtbl, x), i)) {
    l = true_literal;
  }

  return l;
}


/*
 * Extract bit i of a bvarray variable x
 */
static literal_t bvarray_get_bit(bv_vartable_t *vtbl, thvar_t x, uint32_t i) {
  literal_t *a;

  assert(i < bvvar_bitsize(vtbl, x));

  a = bvvar_bvarray_def(vtbl, x);
  return a[i];
}


/*
 * Extract bit i of variable x: 
 * - get it from the pseudo literal array mapped to x
 */
static literal_t bvvar_get_bit(bv_solver_t *solver, thvar_t x, uint32_t i) {
  remap_table_t *rmap;
  literal_t *map;
  literal_t r, l;

  map = bv_solver_get_pseudo_map(solver, x);

  rmap = solver->remap;
  r = remap_table_find_root(rmap, map[i]); // r := root of map[i] 
  l = remap_table_find(rmap, r); // l := real literal for r
  if (l == null_literal) {
    // nothing attached to r: create a new literal and attach it to r
    l = pos_lit(create_boolean_variable(solver->core));
    remap_table_assign(rmap, r, l);
  }

  return l;
}



/**********************
 *  SOLVER INTERFACE  *
 *********************/

void bv_solver_start_internalization(bv_solver_t *solver) {
}

void bv_solver_start_search(bv_solver_t *solver) {
}

bool bv_solver_propagate(bv_solver_t *solver) {
  return true;
}

fcheck_code_t bv_solver_final_check(bv_solver_t *solver) {
  return FCHECK_SAT;
}

void bv_solver_increase_decision_level(bv_solver_t *solver) {
  solver->decision_level ++;
}

void bv_solver_backtrack(bv_solver_t *solver, uint32_t backlevel) {
  assert(solver->base_level <= backlevel && backlevel < solver->decision_level);
  reset_eassertion_queue(&solver->egraph_queue);
  solver->decision_level = backlevel;
}

bool bv_solver_assert_atom(bv_solver_t *solver, void *a, literal_t l) {
  return true;
}

void bv_solver_expand_explanation(bv_solver_t *solver, literal_t l, void *expl, ivector_t *v) {
  assert(false);
}

literal_t bv_solver_select_polarity(bv_solver_t *solver, void *a, literal_t l) {
  return l;
}



/**********************
 *  EGRAPH INTERFACE  *
 *********************/

void bv_solver_assert_var_eq(bv_solver_t *solver, thvar_t x, thvar_t y) {
}

void bv_solver_assert_var_diseq(bv_solver_t *solver, thvar_t x, thvar_t y, composite_t *hint) {
}

void bv_solver_assert_var_distinct(bv_solver_t *solver, uint32_t n, thvar_t *a, composite_t *hint) {
}


bool bv_solver_check_disequality(bv_solver_t *solver, thvar_t x, thvar_t y) {
  return false;
}


uint32_t bv_solver_reconcile_model(bv_solver_t *solver, uint32_t max_eq) {
  return 0;
}

literal_t bv_solver_select_eq_polarity(bv_solver_t *solver, thvar_t x, thvar_t y, literal_t l) {
  return l;
}

bool bv_solver_value_in_model(bv_solver_t *solver, thvar_t x, bvconstant_t *v) {
  return false;
}

bool bv_solver_fresh_value(bv_solver_t *solver, bvconstant_t *v, uint32_t n) {
  return false;
}


/**********************
 *  MAIN OPERATIONS   *
 *********************/

/*
 * Initialize a bit-vector solver
 * - core = the attached smt core
 * - egraph = the attached egraph (or NULL)
 */
void init_bv_solver(bv_solver_t *solver, smt_core_t *core, egraph_t *egraph) {
  solver->core = core;
  solver->egraph = egraph;
  solver->base_level = 0;
  solver->decision_level = 0;

  init_bv_vartable(&solver->vtbl);
  init_bv_atomtable(&solver->atbl);
  init_mtbl(&solver->mtbl);
  init_bv_bound_queue(&solver->bqueue);

  solver->blaster = NULL;
  solver->remap = NULL;

  init_eassertion_queue(&solver->egraph_queue);

  init_bv_trail(&solver->trail_stack);

  init_bvpoly_buffer(&solver->buffer);
  init_pp_buffer(&solver->prod_buffer, 10);
  init_ivector(&solver->aux_vector, 0);
  init_bvconstant(&solver->aux1);
  init_bvconstant(&solver->aux2);
  init_ivector(&solver->a_vector, 0);
  init_ivector(&solver->b_vector, 0);

  init_used_vals(&solver->used_vals);

  solver->env = NULL;
}


/*
 * Attach a jump buffer for exception handling
 */
void bv_solver_init_jmpbuf(bv_solver_t *solver, jmp_buf *buffer) {
  solver->env = buffer;
}


/*
 * Delete solver
 */
void delete_bv_solver(bv_solver_t *solver) {
  delete_bv_vartable(&solver->vtbl);
  delete_bv_atomtable(&solver->atbl);
  delete_mtbl(&solver->mtbl);
  delete_bv_bound_queue(&solver->bqueue);

  if (solver->blaster != NULL) {
    delete_bit_blaster(solver->blaster);
    safe_free(solver->blaster);
    solver->blaster = NULL;
  }

  if (solver->remap != NULL) {
    delete_remap_table(solver->remap);
    safe_free(solver->remap);
    solver->remap = NULL;
  }

  delete_eassertion_queue(&solver->egraph_queue);

  delete_bv_trail(&solver->trail_stack);

  delete_bvpoly_buffer(&solver->buffer);
  delete_pp_buffer(&solver->prod_buffer);
  delete_ivector(&solver->aux_vector);
  delete_bvconstant(&solver->aux1);
  delete_bvconstant(&solver->aux2);
  delete_ivector(&solver->a_vector);
  delete_ivector(&solver->b_vector);

  delete_used_vals(&solver->used_vals);
}


/********************
 *  PUSH/POP/RESET  *
 *******************/

/*
 * Start a new base level
 */
void bv_solver_push(bv_solver_t *solver) {
  uint32_t na, nv, nb;

  assert(solver->decision_level == solver->base_level);

  nv = solver->vtbl.nvars;
  na = solver->atbl.natoms;
  nb = solver->bqueue.top;
  bv_trail_save(&solver->trail_stack, nv, na, nb);

  mtbl_push(&solver->mtbl);

  solver->base_level ++;
  bv_solver_increase_decision_level(solver);
}



/*
 * Remove all eterms whose id >= number of terms in the egraph
 * - if a bitvector variable x is kept after pop but the
 *   eterm[x] is removed from the egraph then we must clear
 *   solver->vtbl.eterm[x]
 */
static void bv_solver_remove_dead_eterms(bv_solver_t *solver) {
  uint32_t nterms;

  if (solver->egraph != NULL) {
    nterms = egraph_num_terms(solver->egraph);
    bv_vartable_remove_eterms(&solver->vtbl, nterms);
  }
}


/*
 * Return to the previous base level
 */
void bv_solver_pop(bv_solver_t *solver) {
  bv_trail_t *top;

  assert(solver->base_level > 0 &&
	 solver->base_level == solver->decision_level);

  solver->base_level --;
  bv_solver_backtrack(solver, solver->base_level);

  top = bv_trail_top(&solver->trail_stack);

  bv_solver_remove_bounds(solver, top->natoms);
  bv_vartable_remove_vars(&solver->vtbl, top->nvars);
  bv_atomtable_remove_atoms(&solver->atbl, top->natoms);
  bv_solver_remove_dead_eterms(solver);

  mtbl_pop(&solver->mtbl);

  bv_trail_pop(&solver->trail_stack);
}


/*
 * Reset: remove all variables and atoms
 * and reset base_level to 0.
 */
void bv_solver_reset(bv_solver_t *solver) {
  reset_bv_vartable(&solver->vtbl);
  reset_bv_atomtable(&solver->atbl);
  reset_mtbl(&solver->mtbl);
  reset_bv_bound_queue(&solver->bqueue);

  if (solver->blaster != NULL) {
    delete_bit_blaster(solver->blaster);
    safe_free(solver->blaster);
    solver->blaster = NULL;
  }

  if (solver->remap != NULL) {
    delete_remap_table(solver->remap);
    safe_free(solver->remap);
    solver->remap = NULL;
  }

  reset_eassertion_queue(&solver->egraph_queue);

  reset_bv_trail(&solver->trail_stack);

  reset_bvpoly_buffer(&solver->buffer, 32);
  pp_buffer_reset(&solver->prod_buffer);
  ivector_reset(&solver->aux_vector);
  ivector_reset(&solver->a_vector);
  ivector_reset(&solver->b_vector);

  reset_used_vals(&solver->used_vals);

  solver->base_level = 0;
  solver->decision_level = 0;
}




/********************************
 *  INTERNALIZATION FUNCTIONS   *
 *******************************/


/*
 * TERM CONSTRUCTORS
 */

/*
 * Create a new variable of n bits
 */
thvar_t bv_solver_create_var(bv_solver_t *solver, uint32_t n) {
  assert(n > 0);
  return make_bvvar(&solver->vtbl, n);
}


/*
 * Create a variable equal to constant c
 */
thvar_t bv_solver_create_const(bv_solver_t *solver, bvconst_term_t *c) {
  return get_bvconst(&solver->vtbl, c->bitsize, c->data);
}


thvar_t bv_solver_create_const64(bv_solver_t *solver, bvconst64_term_t *c) {
  return get_bvconst64(&solver->vtbl, c->bitsize, c->value);
}


/*
 * Internalize a polynomial p:
 * - map = variable renaming
 *   if p is of the form a_0 t_0 + ... + a_n t_n
 *   then map containts n+1 variables, and map[i] is the internalization of t_i
 * - exception: if t_0 is const_idx then map[0] = null_thvar
 */
thvar_t bv_solver_create_bvpoly(bv_solver_t *solver, bvpoly_t *p, thvar_t *map) {
  bvpoly_buffer_t *buffer;
  uint32_t i, n, nbits;

  n = p->nterms;
  nbits = p->bitsize;
  i = 0;

  buffer = &solver->buffer;
  reset_bvpoly_buffer(buffer, nbits);

  // deal with constant term if any
  if (p->mono[0].var == const_idx) {
    assert(map[0] == null_thvar);
    bvpoly_buffer_add_constant(buffer, p->mono[i].coeff);
    i ++;
  }

  // rest of p
  while (i < n) {
    assert(valid_bvvar(&solver->vtbl, map[i]));
    bvbuffer_add_mono(solver, buffer, map[i], p->mono[i].coeff);
    i ++;
  }

  normalize_bvpoly_buffer(buffer);
  return map_bvpoly(solver, buffer);
}

// Same thing: coefficients stored as 64bit integers
thvar_t bv_solver_create_bvpoly64(bv_solver_t *solver, bvpoly64_t *p, thvar_t *map) {
  bvpoly_buffer_t *buffer;
  uint32_t i, n, nbits;

  n = p->nterms;
  nbits = p->bitsize;
  i = 0;

  buffer = &solver->buffer;
  reset_bvpoly_buffer(buffer, nbits);

  // deal with constant term if any
  if (p->mono[0].var == const_idx) {
    assert(map[0] == null_thvar);
    bvpoly_buffer_add_const64(buffer, p->mono[i].coeff);
    i ++;
  }

  // rest of p
  while (i < n) {
    assert(valid_bvvar(&solver->vtbl, map[i]));
    bvbuffer_add_mono64(solver, buffer, map[i], p->mono[i].coeff);
    i ++;
  }

  normalize_bvpoly_buffer(buffer);
  return map_bvpoly64(solver, buffer);
}



/*
 * Product p = t_0^d_0 x ... x t_n ^d_n
 * - map = variable renaming: t_i is replaced by map[i]
 */
thvar_t bv_solver_create_pprod(bv_solver_t *solver, pprod_t *p, thvar_t *map) {
  bv_vartable_t *vtbl;
  pp_buffer_t *buffer;
  uint32_t *a;
  uint64_t c;
  uint32_t i, n, nbits, w;
  thvar_t x;

  vtbl = &solver->vtbl;
  buffer = &solver->prod_buffer;
  pp_buffer_reset(buffer);

  assert(p->len > 0);
  nbits = bvvar_bitsize(vtbl, map[0]);

  /*
   * We build a term (* constant (x_1 ^ d_1 ... x_k^d_k))
   * by replacing any constant map[i] by its value
   */
  if (nbits <= 64) {
    c = 1;
    n = p->len;
    for (i=0; i<n; i++) {
      x = map[i];
      if (bvvar_is_const64(vtbl, x)) {
	c *= upower64(bvvar_val64(vtbl, x), p->prod[i].exp);
      } else {
	pp_buffer_mul_varexp(buffer, x, p->prod[i].exp);
      }
    }

    // normalize c then build the term (c * p)
    c = norm64(c, nbits);
    x = map_const64_times_product(solver, nbits, buffer, c);

  } else {
    // use aux1 to store the constant
    w = (nbits + 31) >> 5;
    bvconstant_set_bitsize(&solver->aux1, nbits);
    a = solver->aux1.data;
    bvconst_set_one(a, w);

    n = p->len;
    for (i=0; i<n; i++) {
      x = map[i];
      if (bvvar_is_const(vtbl, x)) {
	bvconst_mulpower(a, w, bvvar_val(vtbl, x), p->prod[i].exp);
      } else {
	pp_buffer_mul_varexp(buffer, x, p->prod[i].exp);
      }
    }

    // normalize a then build the term (a * p)
    bvconst_normalize(a, nbits);
    x = map_const_times_product(solver, nbits, buffer, a);
  }

  return x;
}


/*
 * Internalize the bit array a[0 ... n-1]
 * - each element a[i] is a literal in the core
 */
thvar_t bv_solver_create_bvarray(bv_solver_t *solver, literal_t *a, uint32_t n) {
  bvconstant_t *aux;
  uint64_t c;
  thvar_t x;

  if (bvarray_is_constant(a, n)) {
    if (n <= 64) {
      c = bvarray_to_uint64(a, n);
      assert(c == norm64(c, n));
      x = get_bvconst64(&solver->vtbl, n, c);
    } else {
      aux = &solver->aux1;
      bvarray_to_bvconstant(a, n, aux);
      x = get_bvconst(&solver->vtbl, n, aux->data);
    }
  } else {
    x = get_bvarray(&solver->vtbl, n, a);
  }

  return x;
}



/*
 * Internalization of (ite c x y)
 */
thvar_t bv_solver_create_ite(bv_solver_t *solver, literal_t c, thvar_t x, thvar_t y) {
  uint32_t n;
  thvar_t aux;

  n = bvvar_bitsize(&solver->vtbl, x);
  assert(bvvar_bitsize(&solver->vtbl, y) == n);

  /*
   * Normalize: rewrite ((ite (not b) x y) to (ite b y x)
   */
  if (is_neg(c)) {
    aux = x; x = y; y = aux;
    c = not(c);
  }

  assert(c != false_literal);
    
  if (c == true_literal) {
    return x; 
  } else {
    return get_bvite(&solver->vtbl, n, c, x, y);
  }
}


/*
 * Binary operators
 */

/*
 * Quotient x/y: unsigned, rounding toward 0
 * - simplify if x and y are both constants
 */
thvar_t bv_solver_create_bvdiv(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  uint64_t c;
  uint32_t n;

  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  n = bvvar_bitsize(vtbl, x);
  assert(n == bvvar_bitsize(vtbl, y));

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_CONST64) {
      // small constants
      assert(n <= 64);
      c = bvconst64_udiv2z(bvvar_val64(vtbl, x), bvvar_val64(vtbl, y), n);
      return get_bvconst64(vtbl, n, c);
    }

    if (xtag == BVTAG_CONST) {
      // large constants
      assert(n > 64);
      aux = &solver->aux1;
      bvconstant_set_bitsize(aux, n);
      bvconst_udiv2z(aux->data, n, bvvar_val(vtbl, x), bvvar_val(vtbl, y));
      bvconst_normalize(aux->data, n);
      return get_bvconst(vtbl, n, aux->data);
    }
  }

  // no simplification
  return get_bvdiv(vtbl, n, x, y);
}


/*
 * Remainder of x/y: unsigned division, rounding toward 0
 */
thvar_t bv_solver_create_bvrem(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  uint64_t c;
  uint32_t n;

  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  n = bvvar_bitsize(vtbl, x);
  assert(n == bvvar_bitsize(vtbl, y));

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_CONST64) {
      // small constants
      assert(n <= 64);
      c = bvconst64_urem2z(bvvar_val64(vtbl, x), bvvar_val64(vtbl, y), n);
      return get_bvconst64(vtbl, n, c);
    }

    if (xtag == BVTAG_CONST) {
      // large constants
      assert(n > 64);
      aux = &solver->aux1;
      bvconstant_set_bitsize(aux, n);
      bvconst_urem2z(aux->data, n, bvvar_val(vtbl, x), bvvar_val(vtbl, y));
      bvconst_normalize(aux->data, n);
      return get_bvconst(vtbl, n, aux->data);
    }
  }

  // no simplification
  return get_bvrem(&solver->vtbl, n, x, y);
}


/*
 * Quotient x/y: signed division, rounding toward 0
 */
thvar_t bv_solver_create_bvsdiv(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  uint64_t c;
  uint32_t n;

  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  n = bvvar_bitsize(vtbl, x);
  assert(n == bvvar_bitsize(vtbl, y));
  
  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_CONST64) {
      // small constants
      assert(n <= 64);
      c = bvconst64_sdiv2z(bvvar_val64(vtbl, x), bvvar_val64(vtbl, y), n);
      return get_bvconst64(vtbl, n, c);
    }

    if (xtag == BVTAG_CONST) {
      // large constants
      assert(n > 64);
      aux = &solver->aux1;
      bvconstant_set_bitsize(aux, n);
      bvconst_sdiv2z(aux->data, n, bvvar_val(vtbl, x), bvvar_val(vtbl, y));
      bvconst_normalize(aux->data, n);
      return get_bvconst(vtbl, n, aux->data);
    }
  }

  // no simplification
  return get_bvsdiv(&solver->vtbl, n, x, y);
}


/*
 * Remainder of x/y: signed division, rounding toward 0
 */
thvar_t bv_solver_create_bvsrem(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  uint64_t c;
  uint32_t n;

  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  n = bvvar_bitsize(vtbl, x);
  assert(n == bvvar_bitsize(vtbl, y));
  
  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_CONST64) {
      // small constants
      assert(n <= 64);
      c = bvconst64_srem2z(bvvar_val64(vtbl, x), bvvar_val64(vtbl, y), n);
      return get_bvconst64(vtbl, n, c);
    }

    if (xtag == BVTAG_CONST) {
      // large constants
      assert(n > 64);
      aux = &solver->aux1;
      bvconstant_set_bitsize(aux, n);
      bvconst_srem2z(aux->data, n, bvvar_val(vtbl, x), bvvar_val(vtbl, y));
      bvconst_normalize(aux->data, n);
      return get_bvconst(vtbl, n, aux->data);
    }
  }

  // no simplification
  return get_bvsrem(&solver->vtbl, n, x, y);
}


/*
 * Remainder in x/y: signed division, rounding toward -infinity
 */
thvar_t bv_solver_create_bvsmod(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  uint64_t c;
  uint32_t n;

  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  n = bvvar_bitsize(vtbl, x);
  assert(n == bvvar_bitsize(vtbl, y));

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_CONST64) {
      // small constants
      assert(n <= 64);
      c = bvconst64_smod2z(bvvar_val64(vtbl, x), bvvar_val64(vtbl, y), n);
      return get_bvconst64(vtbl, n, c);
    }

    if (xtag == BVTAG_CONST) {
      // large constants
      assert(n > 64);
      aux = &solver->aux1;
      bvconstant_set_bitsize(aux, n);
      bvconst_smod2z(aux->data, n, bvvar_val(vtbl, x), bvvar_val(vtbl, y));
      bvconst_normalize(aux->data, n);
      return get_bvconst(vtbl, n, aux->data);
    }
  }

  // no simplification
  return get_bvsmod(&solver->vtbl, n, x, y);
}


/*
 * Left shift, padding with zeros
 */
thvar_t bv_solver_create_bvshl(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag; 
  uint32_t n;
  uint64_t c;

  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  n = bvvar_bitsize(vtbl, x);
  assert(bvvar_bitsize(vtbl, y) == n);

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_CONST64) {
      // small constants
      assert(n <= 64);
      c = bvconst64_lshl(bvvar_val64(vtbl, x), bvvar_val64(vtbl, y), n);
      return get_bvconst64(vtbl, n, c);
    }
    
    if (xtag == BVTAG_CONST) {
      assert(n > 64);
      aux = &solver->aux1;
      bvconstant_set_bitsize(aux, n);
      bvconst_lshl(aux->data, bvvar_val(vtbl, x), bvvar_val(vtbl, y), n);
      return get_bvconst(vtbl, n, aux->data);
    }
  }

  if (bvvar_is_zero(vtbl, x)) {
    // 0b000..0 unchanged by logical shift
    return x;
  }
  
  return get_bvshl(vtbl, n, x, y);
}


/*
 * Right shift, padding with zeros
 */
thvar_t bv_solver_create_bvlshr(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag; 
  uint32_t n;
  uint64_t c;


  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  n = bvvar_bitsize(vtbl, x);
  assert(bvvar_bitsize(vtbl, y) == n);

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_CONST64) {
      // small constants
      assert(n <= 64);
      c = bvconst64_lshr(bvvar_val64(vtbl, x), bvvar_val64(vtbl, y), n);
      return get_bvconst64(vtbl, n, c);
    }
   
    if (xtag == BVTAG_CONST) {
      assert(n > 64);
      aux = &solver->aux1;
      bvconstant_set_bitsize(aux, n);
      bvconst_lshr(aux->data, bvvar_val(vtbl, x), bvvar_val(vtbl, y), n);
      return get_bvconst(vtbl, n, aux->data);
    }
  }

  if (bvvar_is_zero(vtbl, x)) {
    // 0b000..0 unchanged by logical shift
    return x;
  }
  
  return get_bvlshr(vtbl, n, x, y);
}


/*
 * Arithmetic right shift
 */
thvar_t bv_solver_create_bvashr(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag; 
  uint32_t n;
  uint64_t c;

  vtbl = &solver->vtbl;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  n = bvvar_bitsize(vtbl, x);
  assert(bvvar_bitsize(vtbl, y) == n);

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_CONST64) {
      // small constants
      assert(n <= 64);
      c = bvconst64_ashr(bvvar_val64(vtbl, x), bvvar_val64(vtbl, y), n);
      return get_bvconst64(vtbl, n, c);
    }

    if (xtag == BVTAG_CONST) {
      assert(n > 64);
      aux = &solver->aux1;
      bvconstant_set_bitsize(aux, n);
      bvconst_ashr(aux->data, bvvar_val(vtbl, x), bvvar_val(vtbl, y), n);
      return get_bvconst(vtbl, n, aux->data);
    }
  }

  if (bvvar_is_zero(vtbl, x) || bvvar_is_minus_one(vtbl, x)) {
    // 0b000..0 and 0b11...1 are unchanged by any arithmetic shift
    return x;
  }
  
  return get_bvashr(vtbl, n, x, y);
}


/*
 * Return the i-th bit of theory variable x as a literal
 */
literal_t bv_solver_select_bit(bv_solver_t *solver, thvar_t x, uint32_t i) {
  bv_vartable_t *vtbl;
  literal_t l;

  assert(valid_bvvar(&solver->vtbl, x) && i < bvvar_bitsize(&solver->vtbl, x));

  // apply substitutions
  x = mtbl_get_root(&solver->mtbl, x);

  vtbl = &solver->vtbl;
  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_CONST64:
    l = bvconst64_get_bit(vtbl, x, i);
    break;

  case BVTAG_CONST:
    l = bvconst_get_bit(vtbl, x, i);
    break;

  case BVTAG_BIT_ARRAY:
    l = bvarray_get_bit(vtbl, x, i);
    break;

  default:
    l = bvvar_get_bit(solver, x, i);
    break;
  }

  return l;
}




/*
 * ATOM CONSTRUCTORS
 *
 * TODO: check for simplifications
 */


/*
 * Atom (eq x y)
 */
literal_t bv_solver_create_eq_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_atomtable_t *atbl;
  int32_t i;
  literal_t l;
  bvar_t v;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  if (equal_bvvar(solver, x, y)) {
    return true_literal;
  }

  if (diseq_bvvar(solver, x, y)) {
    return false_literal;
  }

  atbl = &solver->atbl;
  i = get_bveq_atom(atbl, x, y);
  l = atbl->data[i].lit;

  if (l == null_literal) {
    /*
     * New atom: assign a fresh boolean variable for it
     */
    v = create_boolean_variable(solver->core);
    l = pos_lit(v);
    atbl->data[i].lit = l;
    attach_atom_to_bvar(solver->core, v, bvatom_idx2tagged_ptr(i));
  }

  return l;
}



/*
 * Create (bvge x y): no simplification
 */
static literal_t bv_solver_make_ge_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_atomtable_t *atbl;
  int32_t i;
  literal_t l;
  bvar_t v;

  atbl = &solver->atbl;
  i = get_bvuge_atom(atbl, x, y);
  l = atbl->data[i].lit;
  if (l == null_literal) {
    /*
     * New atom: assign a fresh boolean variable for it
     */
    v = create_boolean_variable(solver->core);
    l = pos_lit(v);
    atbl->data[i].lit = l;
    attach_atom_to_bvar(solver->core, v, bvatom_idx2tagged_ptr(i));
  }
 
  return l;
}


/*
 * Atom (bvge x y) (unsigned comparison)
 */
literal_t bv_solver_create_ge_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  literal_t l;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  /*
   * Rewrite rules:
   * (bvge 0b000...0 y)  <-->  (bveq 0b000...0 y)
   * (bvge x 0b111...1)  <-->  (bveq x 0b111...1)
   */
  if (bvvar_is_zero(&solver->vtbl, x) || 
      bvvar_is_minus_one(&solver->vtbl, y)) {
    return bv_solver_create_eq_atom(solver, x, y);
  }

  switch (check_bvuge(solver, x, y)) {
  case BVTEST_FALSE:
    l = false_literal;
    break;

  case BVTEST_TRUE:
    l = true_literal;
    break;

  default:
    l = bv_solver_make_ge_atom(solver, x, y);
    break;
  }

  return l;
}


/*
 * Create (bvsge x y): no simplification
 */
static literal_t bv_solver_make_sge_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_atomtable_t *atbl;
  int32_t i;
  literal_t l;
  bvar_t v;

  atbl = &solver->atbl;
  i = get_bvsge_atom(atbl, x, y);
  l = atbl->data[i].lit;
  if (l == null_literal) {
    /*
     * New atom: assign a fresh boolean variable for it
     */
    v = create_boolean_variable(solver->core);
    l = pos_lit(v);
    atbl->data[i].lit = l;
    attach_atom_to_bvar(solver->core, v, bvatom_idx2tagged_ptr(i));
  }
 
  return l;
}


/*
 * Atom (bvsge x y) (signed comparison)
 */
literal_t bv_solver_create_sge_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  literal_t l;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);
  
  /*
   * Rewrite rules:
   * (bvsge 0b100...0 y)  <-->  (bveq 0b100...0 y)
   * (bvsge x 0b011...1)  <-->  (bveq x 0b011...1)
   */
  if (bvvar_is_min_signed(&solver->vtbl, x) || 
      bvvar_is_max_signed(&solver->vtbl, y)) {
    return bv_solver_create_eq_atom(solver, x, y);
  }

  switch (check_bvsge(solver, x, y)) {
  case BVTEST_FALSE:
    l = false_literal;
    break;

  case BVTEST_TRUE:
    l = true_literal;
    break;

  default:
    l = bv_solver_make_sge_atom(solver, x, y);
    break;
  }

  return l;
}



/*
 * ATOM ASSERTIONS
 */

/*
 * Assert (x == y) if tt is true
 * assert (x != y) if tt is false
 */
void bv_solver_assert_eq_axiom(bv_solver_t *solver, thvar_t x, thvar_t y, bool tt) {
  literal_t l;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  if (equal_bvvar(solver, x, y)) {
    if (! tt) add_empty_clause(solver->core);     // Contradiction
  } else if (diseq_bvvar(solver, x, y)) {
    if (tt) add_empty_clause(solver->core);       // Contradiction
  } else if (tt) {
    // Merge the classes of x and y
    x = mtbl_get_root(&solver->mtbl, x);
    y = mtbl_get_root(&solver->mtbl, y);
    bv_solver_merge_vars(solver, x, y);

  } else {
    // Add the constraint (x != y)
    l = bv_solver_create_eq_atom(solver, x, y);
    add_unit_clause(solver->core, not(l));

    // push (x != 0) or (y != 0) in the bound queue
    if (bvvar_is_zero(&solver->vtbl, x) || 
	bvvar_is_zero(&solver->vtbl, y)) {
      push_bvdiseq_bound(solver, x, y);
    }
  }
}


/*
 * Assert (bvge x y) if tt is true
 * Assert (not (bvge x y)) if tt is false
 */
void bv_solver_assert_ge_axiom(bv_solver_t *solver, thvar_t x, thvar_t y, bool tt) {
  literal_t l;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  /*
   * Rewrite rules:
   * (bvge 0b000...0 y)  <-->  (bveq 0b000...0 y)
   * (bvge x 0b111...1)  <-->  (bveq x 0b111...1)
   */
  if (bvvar_is_zero(&solver->vtbl, x) || 
      bvvar_is_minus_one(&solver->vtbl, y)) {
    bv_solver_assert_eq_axiom(solver, x, y, tt);

  } else {
    switch (check_bvuge(solver, x, y)) {
    case BVTEST_FALSE:
      if (tt) add_empty_clause(solver->core); // x < y holds
      break;

    case BVTEST_TRUE:
      if (!tt) add_empty_clause(solver->core); // x >= y holds
      break;

    case BVTEST_UNKNOWN:
      l = bv_solver_make_ge_atom(solver, x, y);
      add_unit_clause(solver->core, signed_literal(l, tt));
      // push the bound into the queue
      if (is_bv_bound_pair(&solver->vtbl, x, y)) {
	push_bvuge_bound(solver, x, y);
      }
      break;
    }
  }
}


/*
 * Assert (bvsge x y) if tt is true
 * Assert (not (bvsge x y)) if tt is false
 */
void bv_solver_assert_sge_axiom(bv_solver_t *solver, thvar_t x, thvar_t y, bool tt) {
  literal_t l;

  x = mtbl_get_root(&solver->mtbl, x);
  y = mtbl_get_root(&solver->mtbl, y);

  /*
   * Rewrite rules:
   * (bvsge 0b100...0 y)  <-->  (bveq 0b100...0 y)
   * (bvsge x 0b011...1)  <-->  (bveq x 0b011...1)
   */
  if (bvvar_is_min_signed(&solver->vtbl, x) || 
      bvvar_is_max_signed(&solver->vtbl, y)) {
    bv_solver_assert_eq_axiom(solver, x, y, tt);

  } else {
    switch (check_bvsge(solver, x, y)) {
    case BVTEST_FALSE:
      if (tt) add_empty_clause(solver->core); // x < y holds
      break;

    case BVTEST_TRUE:
      if (!tt) add_empty_clause(solver->core); // x >= y holds
      break;

    case BVTEST_UNKNOWN:
      l = bv_solver_make_sge_atom(solver, x, y);
      add_unit_clause(solver->core, signed_literal(l, tt));
      // push the bound into the queue
      if (is_bv_bound_pair(&solver->vtbl, x, y)) {
	push_bvsge_bound(solver, x, y);
      }
      break;
    }
  }
}


/*
 * Assert that bit i of x is equal to tt
 */
void bv_solver_set_bit(bv_solver_t *solver, thvar_t x, uint32_t i, bool tt) {
  literal_t l;

  l = bv_solver_select_bit(solver, x, i);
  add_unit_clause(solver->core, signed_literal(l, tt));
}



/*
 * EGRAPH TERMS
 */

/*
 * Attach egraph term t to variable x
 */
void bv_solver_attach_eterm(bv_solver_t *solver, thvar_t x, eterm_t t) {
  attach_eterm_to_bvvar(&solver->vtbl, x, t);
}


/*
 * Get the egraph term attached to x
 * - return null_eterm if x has no eterm attached
 */
eterm_t bv_solver_eterm_of_var(bv_solver_t *solver, thvar_t x) {
  return bvvar_get_eterm(&solver->vtbl, x);
}



/******************************
 *  NUMBER OF ATOMS PER TYPE  *
 *****************************/

uint32_t bv_solver_num_eq_atoms(bv_solver_t *solver) {
  bv_atomtable_t *atbl;
  uint32_t i, n, c;

  c = 0;
  atbl = &solver->atbl;
  n = atbl->natoms;
  for (i=0; i<n; i++) {
    if (bvatm_is_eq(atbl->data + i)) {
      c ++;
    }
  }

  return c;
}

uint32_t bv_solver_num_ge_atoms(bv_solver_t *solver) {
  bv_atomtable_t *atbl;
  uint32_t i, n, c;

  c = 0;
  atbl = &solver->atbl;
  n = atbl->natoms;
  for (i=0; i<n; i++) {
    if (bvatm_is_ge(atbl->data + i)) {
      c ++;
    }
  }

  return c;
}


uint32_t bv_solver_num_sge_atoms(bv_solver_t *solver) {
  bv_atomtable_t *atbl;
  uint32_t i, n, c;

  c = 0;
  atbl = &solver->atbl;
  n = atbl->natoms;
  for (i=0; i<n; i++) {
    if (bvatm_is_sge(atbl->data + i)) {
      c ++;
    }
  }

  return c;
}





/*******************************
 *  INTERNALIZATION INTERFACE  *
 ******************************/

static bv_interface_t bv_solver_context = {
  (create_bv_var_fun_t) bv_solver_create_var,
  (create_bv_const_fun_t) bv_solver_create_const,
  (create_bv64_const_fun_t) bv_solver_create_const64,
  (create_bv_poly_fun_t) bv_solver_create_bvpoly,
  (create_bv64_poly_fun_t) bv_solver_create_bvpoly64,
  (create_bv_pprod_fun_t) bv_solver_create_pprod,
  (create_bv_array_fun_t) bv_solver_create_bvarray,
  (create_bv_ite_fun_t) bv_solver_create_ite,
  (create_bv_binop_fun_t) bv_solver_create_bvdiv,
  (create_bv_binop_fun_t) bv_solver_create_bvrem,
  (create_bv_binop_fun_t) bv_solver_create_bvsdiv,
  (create_bv_binop_fun_t) bv_solver_create_bvsrem,
  (create_bv_binop_fun_t) bv_solver_create_bvsmod,
  (create_bv_binop_fun_t) bv_solver_create_bvshl,
  (create_bv_binop_fun_t) bv_solver_create_bvlshr,
  (create_bv_binop_fun_t) bv_solver_create_bvashr,

  (select_bit_fun_t) bv_solver_select_bit,
  (create_bv_atom_fun_t) bv_solver_create_eq_atom, 
  (create_bv_atom_fun_t) bv_solver_create_ge_atom, 
  (create_bv_atom_fun_t) bv_solver_create_sge_atom, 

  (assert_bv_axiom_fun_t) bv_solver_assert_eq_axiom,
  (assert_bv_axiom_fun_t) bv_solver_assert_ge_axiom,
  (assert_bv_axiom_fun_t) bv_solver_assert_sge_axiom,
  (set_bit_fun_t) bv_solver_set_bit,

  (attach_eterm_fun_t) bv_solver_attach_eterm,
  (eterm_of_var_fun_t) bv_solver_eterm_of_var,

  NULL,
  NULL,
  NULL,  
};


/*
 * Return the interface descriptor
 */
bv_interface_t *bv_solver_bv_interface(bv_solver_t *solver) {
  return &bv_solver_context;
}



/********************************
 *  SMT AND CONTROL INTERFACES  *
 *******************************/

static th_ctrl_interface_t bv_solver_control = {
  (start_intern_fun_t) bv_solver_start_internalization,
  (start_fun_t) bv_solver_start_search,
  (propagate_fun_t) bv_solver_propagate,
  (final_check_fun_t) bv_solver_final_check,
  (increase_level_fun_t) bv_solver_increase_decision_level,
  (backtrack_fun_t) bv_solver_backtrack,
  (push_fun_t) bv_solver_push,
  (pop_fun_t) bv_solver_pop,
  (reset_fun_t) bv_solver_reset,
};

static th_smt_interface_t bv_solver_smt = {
  (assert_fun_t) bv_solver_assert_atom,
  (expand_expl_fun_t) bv_solver_expand_explanation,
  (select_pol_fun_t) bv_solver_select_polarity,
  NULL,
  NULL,
};


/*
 * Get the control and smt interfaces
 */
th_ctrl_interface_t *bv_solver_ctrl_interface(bv_solver_t *solver) {
  return &bv_solver_control;
}

th_smt_interface_t *bv_solver_smt_interface(bv_solver_t *solver) {
  return &bv_solver_smt;
}



/*********************************************
 *  SATELLITE SOLVER INTERFACE (FOR EGRAPH)  *
 ********************************************/

static th_egraph_interface_t bv_solver_egraph = {
  (assert_eq_fun_t) bv_solver_assert_var_eq,
  (assert_diseq_fun_t) bv_solver_assert_var_diseq,
  (assert_distinct_fun_t) bv_solver_assert_var_distinct,
  (check_diseq_fun_t) bv_solver_check_disequality,
  NULL, // no need for expand_th_explanation
  (reconcile_model_fun_t) bv_solver_reconcile_model,
  (attach_to_var_fun_t) bv_solver_attach_eterm,
  (get_eterm_fun_t) bv_solver_eterm_of_var,
  (select_eq_polarity_fun_t) bv_solver_select_eq_polarity,
};


static bv_egraph_interface_t bv_solver_bv_egraph = {
  (make_bv_var_fun_t) bv_solver_create_var,
  (bv_val_fun_t) bv_solver_value_in_model,
  (bv_fresh_val_fun_t) bv_solver_fresh_value,
};


/*
 * Get the egraph interfaces
 */
th_egraph_interface_t *bv_solver_egraph_interface(bv_solver_t *solver) {
  return &bv_solver_egraph;
}

bv_egraph_interface_t *bv_solver_bv_egraph_interface(bv_solver_t *solver) {
  return &bv_solver_bv_egraph;
}






