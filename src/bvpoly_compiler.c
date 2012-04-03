/*
 * SUPPORT FOR CONVERTING BIT-VECTOR POLYNOMIALS
 * TO ELEMENTATY EXPRESSSIONS.
 */

#include <assert.h>

#include "bit_tricks.h"
#include "bv_constants.h"
#include "bv64_constants.h"
#include "bvpoly_compiler.h"


/*
 * STACK OF ELEMENTARY EXPRESSIONS
 */

/*
 * Initialize to empty stack
 */
static inline void init_bvc_stack(bvc_stack_t *stack) {
  stack->data = NULL;
  stack->top = 0;
  stack->size = 0;
}


/*
 * Make the stack larger
 */
static void bvc_stack_extend(bvc_stack_t *stack) {
  uint32_t n;

  n = stack->size;
  if (n == 0) {
    // first allocation
    n = DEF_BVC_STACK_SIZE;
    assert(n > 0 && n <= MAX_BVC_STACK_SIZE && stack->data == NULL);
  } else {
    n += (n >> 1); // 50% large   
    assert(n > stack->size);
    if (n > MAX_BVC_STACK_SIZE) {
      out_of_memory();
    }
  }

  stack->data = (thvar_t *) safe_realloc(stack->data, n * sizeof(thvar_t));
  stack->size = n;
}


/*
 * Push x on the stack
 */
static void bvc_stack_push(bvc_stack_t *stack, thvar_t x) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    bvc_stack_extend(stack);
  }
  assert(i < stack->size);
  stack->data[i] = x;
  stack->top = i + 1;
}


/*
 * Empty the stack
 */
static inline void reset_bvc_stack(bvc_stack_t *stack) {
  stack->top = 0;
}


/*
 * Delete
 */
static void delete_bvc_stack(bvc_stack_t *stack) {
  if (stack->data != NULL) {
    safe_free(stack->data);
    stack->data = NULL;
  }
}





/*
 * COMPILER
 */

/*
 * Initialize:
 * - vtbl = attached variable table
 */
void init_bv_compiler(bvc_t *c, bv_vartable_t *vtbl) {
  c->vtbl = vtbl;
  init_bvc_stack(&c->elemexp);
  init_int_hmap(&c->cmap, 0);
}


/*
 * Delete
 */
void delete_bv_compiler(bvc_t *c) {
  delete_bvc_stack(&c->elemexp);
  delete_int_hmap(&c->cmap);
}

/*
 * Empty
 */
void reset_bv_compiler(bvc_t *c) {
  reset_bvc_stack(&c->elemexp);
  int_hmap_reset(&c->cmap);
}


/*
 * Get the variable mapped to x in cmap
 * - return -1 if nothing is mapped to x
 */
thvar_t bvvar_compiles_to(bvc_t *c, thvar_t x) {
  int_hmap_pair_t *p;
  thvar_t y;

  assert(0 < x && x < c->vtbl->nvars);

  y = null_thvar;
  p = int_hmap_get(&c->cmap, x);
  if (p != NULL) {
    y = p->val;
    assert(0 < y && y < c->vtbl->nvars);
  }

  return y;
}


/*
 * Store the mapping [x --> y] in c->cmap
 */
static void bv_compiler_store_map(bvc_t *c, thvar_t x, thvar_t y) {
  int_hmap_pair_t *p;

  assert(0 < x && x < c->vtbl->nvars && 0 < y && y < c->vtbl->nvars && x != y);

  p = int_hmap_get(&c->cmap, x);
  assert(p->val == -1);
  p->val = y;
}



/*
 * CONSTRUCTORS FOR ELEMENTARY EXPRESSIONS
 */

/*
 * In all constructors:
 * - n = number of bits
 * - x (and y) = operands
 */
static thvar_t bv_compiler_mk_bvadd(bvc_t *c, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t v;

  assert(0 < x && x < c->vtbl->nvars && 0 < y && y < c->vtbl->nvars);

  // normalize: left operand <= right operand
  if (x > y) {
    v = x; x = y; y = v;
  }

  assert(find_bvadd(c->vtbl, x, y) == -1); // not already present

  v = get_bvadd(c->vtbl, n, x, y);
  bvc_stack_push(&c->elemexp, v);

  return v;
}

static thvar_t bv_compiler_mk_bvsub(bvc_t *c, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t v;

  assert(0 < x && x < c->vtbl->nvars && 0 < y && y < c->vtbl->nvars);
  assert(find_bvsub(c->vtbl, x, y) == -1); // not already present

  v = get_bvsub(c->vtbl, n, x, y);
  bvc_stack_push(&c->elemexp, v);

  return v;
}

static thvar_t bv_compiler_mk_bvmul(bvc_t *c, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t v;

  assert(0 < x && x < c->vtbl->nvars && 0 < y && y < c->vtbl->nvars);

  // normalize: left operand <= right operand
  if (x > y) {
    v = x; x = y; y = v;
  }

  assert(find_bvmul(c->vtbl, x, y) == -1); // not already present

  v = get_bvmul(c->vtbl, n, x, y);
  bvc_stack_push(&c->elemexp, v);

  return v;
}

static thvar_t bv_compiler_mk_bvneg(bvc_t *c, uint32_t n, thvar_t x) {
  thvar_t v;

  assert(0 < x && x < c->vtbl->nvars);
  assert(find_bvneg(c->vtbl, x) == -1);

  v = get_bvneg(c->vtbl, n, x);
  bvc_stack_push(&c->elemexp, v);

  return v;
}


/*
 * Constructors for monomials (a * x)
 * - n = number of bits
 * - a = coefficient
 * - x = variable
 * - a must be normalized modulo 2^n
 * There are two versions: one for small bitsize (1 <= n <= 64) and
 * one for large bitsize (n > 64).
 */
static thvar_t bv_compiler_mk_mono64(bvc_t *c, uint32_t n, uint64_t a, thvar_t x) {
  thvar_t k;

  assert(1 <= n && n <= 64 && a == norm64(a, n));

  k = get_bvconst64(c->vtbl, n, a);
  return bv_compiler_mk_bvmul(c, n, k, x);
}

static thvar_t bv_compiler_mk_mono(bvc_t *c, uint32_t n, uint32_t *a, thvar_t x) {
  thvar_t k;

  assert(n > 64 && bvconst_is_normalized(a, n));

  k = get_bvconst(c->vtbl, n, a);
  return bv_compiler_mk_bvmul(c, n, k, x);
}


