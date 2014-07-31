/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * VARIABLE TABLE FOR DIFFERENCE LOGIC SOLVERS
 */


#include "utils/memalloc.h"
#include "utils/hash_functions.h"
#include "solvers/floyd_warshall/dl_vartable.h"


/*
 * TRAIL STACK
 */

/*
 * Initialize stack with default size
 */
static void init_dl_trail_stack(dl_trail_stack_t *stack) {
  uint32_t n;

  n = DEF_DL_TRAIL_SIZE;
  assert(n < MAX_DL_TRAIL_SIZE);

  stack->size = n;
  stack->top = 0;
  stack->data = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
}

/*
 * Make the stack 50% larger
 */
static void extend_dl_trail_stack(dl_trail_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n>>1;
  if (n >= MAX_DL_TRAIL_SIZE) {
    out_of_memory();
  }
  stack->data = (uint32_t *) safe_realloc(stack->data, n * sizeof(uint32_t));
  stack->size = n;
}

/*
 * Push n on top of the stack
 */
static void dl_trail_stack_push(dl_trail_stack_t *stack, uint32_t n) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_dl_trail_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i] = n;
  stack->top = i+1;
}

/*
 * Delete the stack
 */
static void delete_dl_trail_stack(dl_trail_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}

/*
 * Empty the stack
 */
static inline void reset_dl_trail_stack(dl_trail_stack_t *stack) {
  stack->top = 0;
}

/*
 * Check emptiness
 */
#ifndef NDEBUG
static inline bool dl_trail_stack_is_empty(dl_trail_stack_t *stack) {
  return stack->top == 0;
}
#endif

/*
 * Get the top element from the stack
 */
static inline uint32_t dl_trail_stack_top(dl_trail_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data[stack->top - 1];
}

/*
 * Remove the top element
 */
static inline void dl_trail_stack_pop(dl_trail_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}




/*
 * VARIABLE TABLE
 */

/*
 * Initialize
 */
void init_dl_vartable(dl_vartable_t *tbl) {
  uint32_t n;

  n = DEF_DL_VARTABLE_SIZE;

  assert(n < MAX_DL_VARTABLE_SIZE);
  tbl->nvars = 0;
  tbl->size = n;
  tbl->triple = (dl_triple_t *) safe_malloc(n * sizeof(dl_triple_t));
  init_int_htbl(&tbl->htbl, 0);
  init_dl_trail_stack(&tbl->stack);
}

/*
 * Make the table 50% larger
 */
static void extend_dl_vartable(dl_vartable_t *tbl) {
  uint32_t n;

  n = tbl->size + 1;
  n += n >> 1;
  if (n >= MAX_DL_VARTABLE_SIZE) {
    out_of_memory();
  }
  tbl->triple = (dl_triple_t *) safe_realloc(tbl->triple, n * sizeof(dl_triple_t));
  tbl->size = n;
}

/*
 * Delete the table
 */
void delete_dl_vartable(dl_vartable_t *tbl) {
  safe_free(tbl->triple);
  tbl->triple = NULL;
  delete_int_htbl(&tbl->htbl);
  delete_dl_trail_stack(&tbl->stack);
}

/*
 * Empty the table
 */
void reset_dl_vartable(dl_vartable_t *tbl) {
  tbl->nvars = 0;
  reset_int_htbl(&tbl->htbl);
  reset_dl_trail_stack(&tbl->stack);
}


/*
 * Allocate a new variable index i
 */
static int32_t dl_vartable_alloc(dl_vartable_t *tbl) {
  int32_t i;

  i = tbl->nvars;
  if (i == tbl->size) {
    extend_dl_vartable(tbl);
  }
  assert(i < tbl->size);
  tbl->nvars = i + 1;

  return i;
}


/*
 * Hash code for triple t
 */
static uint32_t hash_dl_triple(dl_triple_t *t) {
  uint32_t h1, h2;

  q_hash_decompose(&t->constant, &h1, &h2);
  return jenkins_hash_quad(t->target, t->source, h1, h2, 0x78312a3e);
}

static bool eq_dl_triple(dl_triple_t *t1, dl_triple_t *t2) {
  return t1->target == t2->target && t1->source == t2->source && q_eq(&t1->constant, &t2->constant);
}


/*
 * Remove all variables of index >= n
 */
static void dl_vartable_remove_vars(dl_vartable_t *tbl, uint32_t n) {
  uint32_t i, h;

  assert(n <= tbl->nvars);

  for (i=n; i<tbl->nvars; i++) {
    h = hash_dl_triple(tbl->triple + i);
    int_htbl_erase_record(&tbl->htbl, h, i);
  }

  tbl->nvars = n;
}



/*
 * Push: save the number of variables on the trail stack
 */
void dl_vartable_push(dl_vartable_t *tbl) {
  dl_trail_stack_push(&tbl->stack, tbl->nvars);
}


/*
 * Pop: remove all variables created since the matching push
 */
void dl_vartable_pop(dl_vartable_t *tbl) {
  uint32_t n;

  assert(! dl_trail_stack_is_empty(&tbl->stack));
  n = dl_trail_stack_top(&tbl->stack);
  dl_trail_stack_pop(&tbl->stack);
  dl_vartable_remove_vars(tbl, n);
}





/*
 * OPERATIONS ON TRIPLES
 */

/*
 * Normalize triple t: rewrite (x - x + c) to [nil, nil, c]
 */
static void normalize_dl_triple(dl_triple_t *t) {
  if (t->target == t->source) {
    t->target = nil_vertex;
    t->source = nil_vertex;
  }
}

#ifndef NDEBUG
/*
 * Check whether t is normalized
 */
static bool dl_triple_is_normalized(dl_triple_t *t) {
  return t->target != t->source || t->target == nil_vertex;
}

#endif


/*
 * Add t2 to t1 (store the result in t1)
 * - return true if the result is a triple
 * - return false otherwise
 */
static bool add_dl_triple(dl_triple_t *t1, dl_triple_t *t2) {
  int32_t x1, x2, y1, y2;

  assert(dl_triple_is_normalized(t1) && dl_triple_is_normalized(t2));

  x1 = t1->target;
  y1 = t1->source;
  x2 = t2->target;
  y2 = t2->source;


  /*
   * t1 is x1 - y1 + c1
   * t2 is x2 - y2 + c2
   * t1 + t2 is x1 + x2 - y1 - y2 + (c1 + c2)
   */
  q_add(&t1->constant, &t2->constant);

  if (x2 == y2) {
    // result = (x1 - y1 + (c1 + c2))
    return true;
  }

  if (x1 == y2) {
    // result = (x2 - y1 + (c1 + c2))
    t1->target = x2;
    normalize_dl_triple(t1);
    return true;
  }

  if (x2 == y1) {
    // result = (x1 - y2 + (c1 + c2))
    t1->source = y2;
    normalize_dl_triple(t1);
    return true;
  }

  if (x1 == y1) {
    // result = (x2 - y2 + (c1 + c2))
    t1->target = x2;
    t1->source = y2;
    return true;
  }

  return false;
}


/*
 * Subtract t2 from t1 (store the result in t1)
 * - return true if the result is a triple
 * - return false otherwise
 */
static bool sub_dl_triple(dl_triple_t *t1, dl_triple_t *t2) {
  int32_t x1, x2, y1, y2;

  assert(dl_triple_is_normalized(t1) && dl_triple_is_normalized(t2));

  x1 = t1->target;
  y1 = t1->source;
  x2 = t2->target;
  y2 = t2->source;


  /*
   * t1 is x1 - y1 + c1
   * t2 is x2 - y2 + c2
   * t1 - t2 is x1 + y2 - y1 - x2 + (c1 - c2)
   */
  q_sub(&t1->constant, &t2->constant);

  if (x2 == y2) {
    // result = (x1 - y1 + (c1 - c2))
    return true;
  }

  if (x1 == x2) {
    // result = (y2 - y1 + (c1 - c2))
    t1->target = y2;
    normalize_dl_triple(t1);
    return true;
  }

  if (y2 == y1) {
    // result = (x1 - x2 + (c1 - c2))
    t1->source = x2;
    normalize_dl_triple(t1);
    return true;
  }

  if (x1 == y1) {
    // result = (y2 - x2 + (c1 - c2))
    t1->target = y2;
    t1->source = x2;
    return true;
  }

  return false;
}



/*
 * Add/subtract triple t to/from buffer b
 */
static void poly_buffer_add_triple(poly_buffer_t *b, dl_triple_t *t) {
  assert(dl_triple_is_normalized(t));

  if (t->target >= 0) poly_buffer_add_var(b, t->target + 1);
  if (t->source >= 0) poly_buffer_sub_var(b, t->source + 1);
  poly_buffer_add_const(b, &t->constant);
}

static void poly_buffer_sub_triple(poly_buffer_t *b, dl_triple_t *t) {
  assert(dl_triple_is_normalized(t));

  if (t->target >= 0) poly_buffer_sub_var(b, t->target + 1);
  if (t->source >= 0) poly_buffer_add_var(b, t->source + 1);
  poly_buffer_sub_const(b, &t->constant);
}


/*
 * Add/subtract a * t to/from buffer b
 */
static void poly_buffer_addmul_triple(poly_buffer_t *b, dl_triple_t *t, rational_t *a) {
  assert(dl_triple_is_normalized(t));

  if (t->target >= 0) poly_buffer_add_monomial(b, t->target + 1, a);
  if (t->source >= 0) poly_buffer_sub_monomial(b, t->source + 1, a);
  poly_buffer_addmul_monomial(b, const_idx, &t->constant, a);
}

static void poly_buffer_submul_triple(poly_buffer_t *b, dl_triple_t *t, rational_t *a) {
  assert(dl_triple_is_normalized(t));

  if (t->target >= 0) poly_buffer_sub_monomial(b, t->target + 1, a);
  if (t->source >= 0) poly_buffer_add_monomial(b, t->source + 1, a);
  poly_buffer_submul_monomial(b, const_idx, &t->constant, a);
}



/*
 * HASH CONSING
 */
typedef struct dl_var_hobj_s {
  int_hobj_t m;
  dl_vartable_t *table;
  dl_triple_t *triple;
} dl_var_hobj_t;


// Hash code
static uint32_t hash_dl_var(dl_var_hobj_t *o) {
  return hash_dl_triple(o->triple);
}

// Equality test
static bool eq_dl_var(dl_var_hobj_t *o, thvar_t x) {
  dl_vartable_t *tbl;

  tbl = o->table;
  assert(0 <= x && x < tbl->nvars);
  return eq_dl_triple(o->triple, tbl->triple + x);
}

// Build new variable
static int32_t build_dl_var(dl_var_hobj_t *o) {
  dl_vartable_t *tbl;
  dl_triple_t *d;
  int32_t x;

  tbl = o->table;
  d = o->triple;
  x = dl_vartable_alloc(tbl);

  assert(0 <= x && x < tbl->size);
  tbl->triple[x].target = d->target;
  tbl->triple[x].source = d->source;
  q_init(&tbl->triple[x].constant);
  q_set(&tbl->triple[x].constant, &d->constant);

  return x;
}


/*
 * Get the variable for triple d
 */
thvar_t get_dl_var(dl_vartable_t *tbl, dl_triple_t *d) {
  dl_var_hobj_t hobj;

  hobj.m.hash = (hobj_hash_t) hash_dl_var;
  hobj.m.eq = (hobj_eq_t) eq_dl_var;
  hobj.m.build = (hobj_build_t) build_dl_var;

  hobj.table = tbl;
  hobj.triple= d;

  return int_htbl_get_obj(&tbl->htbl, (int_hobj_t*) &hobj);
}



/*
 * Copy the descriptor for x into d
 */
void copy_dl_var_triple(dl_vartable_t *tbl, thvar_t x, dl_triple_t *d) {
  dl_triple_t *dx;

  dx = dl_var_triple(tbl, x);
  d->target = dx->target;
  d->source = dx->source;
  q_set(&d->constant, &dx->constant);
}


/*
 * Add the triples for x and y and store the result in d
 * - return true if the result can be computed (i.e.,
 *   if triple(x) + triple(y) is of the form (w - z + c)
 * - return false otherwise.
 */
bool sum_dl_vars(dl_vartable_t *table, thvar_t x, thvar_t y, dl_triple_t *d) {
  dl_triple_t *dy;

  copy_dl_var_triple(table, x, d);
  dy = dl_var_triple(table, y);
  return add_dl_triple(d, dy);
}


/*
 * Compute triple(x) - triple(y) and store the result in d if that's a triple
 * - return true if triple(x) - triple(y) is of the from (w - z + c)
 * - return false otherwise
 */
bool diff_dl_vars(dl_vartable_t *table, thvar_t x, thvar_t y, dl_triple_t *d) {
  dl_triple_t *dy;

  copy_dl_var_triple(table, x, d);
  dy = dl_var_triple(table, y);
  return sub_dl_triple(d, dy);
}


/*
 * Operation between a poly buffer and a triple:
 * - add_dl_var_to_buffer:       add triple(x) to b
 * - sub_dl_var_from_buffer:     subtract triple(x) from b
 * - addmul_dl_var_to_buffer:    add a * triple(x) to b
 * - submul_dl_var_from_biuffer: subtract a * triple(x) from b
 * These operation do not normalize the buffer b
 */
void add_dl_var_to_buffer(dl_vartable_t *table, poly_buffer_t *b, thvar_t x) {
  poly_buffer_add_triple(b, dl_var_triple(table, x));
}

void sub_dl_var_from_buffer(dl_vartable_t *table, poly_buffer_t *b, thvar_t x) {
  poly_buffer_sub_triple(b, dl_var_triple(table, x));
}

void addmul_dl_var_to_buffer(dl_vartable_t *table, poly_buffer_t *b, thvar_t x, rational_t *a) {
  poly_buffer_addmul_triple(b, dl_var_triple(table, x), a);
}

void submul_dl_var_from_buffer(dl_vartable_t *table, poly_buffer_t *b, thvar_t x, rational_t *a) {
  poly_buffer_submul_triple(b, dl_var_triple(table, x), a);
}


/*
 * Check whether b is a triple (x - y + c) and store the result in d if so
 * - b must be normalized
 * - d->constant must be initialized
 * - return true if the conversion works
 * - return false otherwise
 */
bool convert_poly_buffer_to_dl_triple(poly_buffer_t *b, dl_triple_t *d) {
  monomial_t *p;
  uint32_t n;

  n = poly_buffer_nterms(b);
  p = poly_buffer_mono(b);
  if (n >= 4 || (n == 3 && p[0].var != const_idx)) {
    return false; // can't convert
  }

  // default: zero triple
  d->target = nil_vertex;
  d->source = nil_vertex;
  q_clear(&d->constant);

  // get the constant term of b if any
  if (n > 0 && p[0].var == const_idx) {
    q_set(&d->constant, &p[0].coeff);
    n --;
    p ++;
  }

  // check whether the non-constant terms have the right form
  if (n == 0) {
    return true;

  } else if (n == 1) {
    if (q_is_one(&p[0].coeff)) {
      d->target = p[0].var - 1;
      return true;
    }

    if (q_is_minus_one(&p[0].coeff)) {
      d->source = p[0].var - 1;
      return true;
    }

  } else if (n == 2 && q_opposite(&p[0].coeff, &p[1].coeff)) {
    if (q_is_one(&p[0].coeff)) {
      d->target = p[0].var - 1;
      d->source = p[1].var - 1;
      return true;
    }

    if (q_is_one(&p[1].coeff)) {
      d->target = p[1].var - 1;
      d->source = p[0].var - 1;
      return true;
    }
  }

  return false;
}


/*
 * Try to convert poly buffer *b to a triple [x, y, c]
 * - b must be normalized.
 * - if the conversion works, the returned triple satisfies the property
 *    (b >= 0) <==> (x - y + c >= 0)
 * - return true if the conversion works and store the result into d.
 * - return false otherwise.
 */
bool rescale_poly_buffer_to_dl_triple(poly_buffer_t *b, dl_triple_t *d) {
  rational_t a;
  monomial_t *p;
  uint32_t n;
  int32_t x, y;

  n = poly_buffer_nterms(b);
  p = poly_buffer_mono(b);
  if (n >= 4 || (n == 3 && p[0].var != const_idx)) {
    return false; // can't convert
  }


  /*
   * Attempt to write b as (a x - a y + c) with a > 0
   * and  c is stored in d->constant.
   * Then return (x - y + c/a) as the result.
   * There are special cases for
   *    b = a x + c (then y = nil),
   *    b = - a y + c (then x = nil), etc.
   */
  q_init(&a);
  q_set_one(&a);
  q_clear(&d->constant);
  x = nil_vertex;
  y = nil_vertex;

  // constant term of b
  if (n > 0 && p[0].var == const_idx) {
    q_set(&d->constant, &p[0].coeff);
    n --;
    p ++;
  }

  if (n == 1) {
    if (q_is_pos(&p[0].coeff)) {
      q_set(&a, &p[0].coeff);
      x = p[0].var - 1;
    } else {
      q_set_neg(&a, &p[0].coeff);
      y = p[0].var - 1;
    }

  } else if (n == 2) {
    if (q_opposite(&p[0].coeff, &p[1].coeff)) {
      if (q_is_pos(&p[0].coeff)) {
        q_set(&a, &p[0].coeff);
        x = p[0].var - 1;
        y = p[1].var - 1;
      } else {
        assert(q_is_pos(&p[1].coeff));
        q_set(&a, &p[1].coeff);
        x = p[1].var - 1;
        y = p[0].var - 1;
      }

    } else {
      q_clear(&a); // cleanup
      return false;
    }
  }

  d->target = x;
  d->source = y;
  if (! q_is_one(&a)) {
    q_div(&d->constant, &a);
  }

  q_clear(&a);

  return true;
}


