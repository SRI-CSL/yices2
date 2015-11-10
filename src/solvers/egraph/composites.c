/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Operations on composite objects
 */
#include <stddef.h>

#include "solvers/egraph/composites.h"
#include "utils/int_array_sort.h"
#include "utils/memalloc.h"



/******************
 *  CONSTRUCTORS  *
 *****************/

/*
 * Allocate a new composite: n = arity
 * - this allocates a child array of size 2n
 */
static inline composite_t *alloc_composite(uint32_t n) {
  assert(n <= MAX_COMPOSITE_ARITY);
  n += n;
  return (composite_t *) safe_malloc(sizeof(composite_t) + n * sizeof(int32_t));
}

static inline composite_t *arena_alloc_composite(arena_t *m, uint32_t n) {
  assert(n <= MAX_COMPOSITE_ARITY);
  n += n;
  return (composite_t *) arena_alloc(m, sizeof(composite_t) + n * sizeof(int32_t));
}

static inline composite_t *alloc_lambda_composite(void) {
  return (composite_t *) safe_malloc(sizeof(composite_t) + 3 * sizeof(int32_t));
}

static inline composite_t *arena_alloc_lambda_composite(arena_t *m) {
  return (composite_t *) arena_alloc(m, sizeof(composite_t) + 3 * sizeof(int32_t));
}


/*
 * Initialization
 */
static inline void init_header(composite_t *c, uint32_t tg) {
  c->tag = tg;
  c->hash = 0;
  c->id = null_eterm;
}

static void init_hooks(composite_t *c) {
  uint32_t i, n;
  int32_t *h;

  n = composite_arity(c);
  h = c->child + n;
  for (i=0; i<n; i++) {
    h[i] = no_ptr;
  }
}

static void init_apply(composite_t *c, occ_t f, uint32_t n, occ_t *a) {
  uint32_t i;

  assert(n >= 1);

  init_header(c, mk_apply_tag(n + 1));
  c->child[0] = f;
  for (i=0; i<n; i++) {
    c->child[i+1] = a[i];
  }
  init_hooks(c);
}

static void init_update(composite_t *c, occ_t f, uint32_t n, occ_t *a, occ_t v) {
  uint32_t i;

  assert(n >= 1);
  init_header(c, mk_update_tag(n + 2));
  c->child[0] = f;
  for (i=0; i<n; i++) {
    c->child[i+1] = a[i];
  }
  c->child[n+1] = v;
  init_hooks(c);
}

static void init_tuple(composite_t *c, uint32_t n, occ_t *a) {
  uint32_t i;

  assert(n >= 1);

  init_header(c, mk_tuple_tag(n));
  for (i=0; i<n; i++) {
    c->child[i] = a[i];
  }
  init_hooks(c);
}

static void init_eq(composite_t *c, occ_t t1, occ_t t2) {
  init_header(c, mk_eq_tag());
  c->child[0] = t1;
  c->child[1] = t2;
  init_hooks(c);
}

static void init_distinct(composite_t *c, uint32_t n, occ_t *a) {
  uint32_t i;

  assert(n >= 2); // ? 3 is a better limit

  init_header(c, mk_distinct_tag(n));
  for (i=0; i<n; i++) {
    c->child[i] = a[i];
  }
  init_hooks(c);
}

static void init_ite(composite_t *c, occ_t t1, occ_t t2, occ_t t3) {
  init_header(c, mk_ite_tag());
  c->child[0] = t1;
  c->child[1] = t2;
  c->child[2] = t3;
  init_hooks(c);
}

static void init_or(composite_t *c, uint32_t n, occ_t *a) {
  uint32_t i;

  assert(n >= 2);

  init_header(c, mk_or_tag(n));
  for (i=0; i<n; i++) {
    c->child[i] = a[i];
  }
  init_hooks(c);
}

static void init_lambda(composite_t *c, occ_t t, int32_t tag) {
  init_header(c, mk_lambda_tag());
  c->child[0] = t;
  c->child[1] = no_ptr; // hook
  c->child[2] = tag;
}


/*
 * Long-term composites
 */
composite_t *new_apply_composite(occ_t f, uint32_t n, occ_t *a) {
  composite_t *tmp;

  tmp = alloc_composite(n + 1);
  init_apply(tmp, f, n, a);
  return tmp;
}

composite_t *new_update_composite(occ_t f, uint32_t n, occ_t *a, occ_t v) {
  composite_t *tmp;

  tmp = alloc_composite(n + 2);
  init_update(tmp, f, n, a, v);
  return tmp;
}

composite_t *new_tuple_composite(uint32_t n, occ_t *a) {
  composite_t *tmp;

  tmp = alloc_composite(n);
  init_tuple(tmp, n, a);
  return tmp;
}

composite_t *new_eq_composite(occ_t t1, occ_t t2) {
  composite_t *tmp;

  tmp = alloc_composite(2);
  init_eq(tmp, t1, t2);
  return tmp;
}

composite_t *new_distinct_composite(uint32_t n, occ_t *a) {
  composite_t *tmp;

  tmp = alloc_composite(n);
  init_distinct(tmp, n, a);
  return tmp;
}

composite_t *new_ite_composite(occ_t t1, occ_t t2, occ_t t3) {
  composite_t *tmp;

  tmp = alloc_composite(3);
  init_ite(tmp, t1, t2, t3);
  return tmp;
}

composite_t *new_or_composite(uint32_t n, occ_t *a) {
  composite_t *tmp;

  tmp = alloc_composite(n);
  init_or(tmp, n, a);
  return tmp;
}

composite_t *new_lambda_composite(occ_t t, int32_t tag) {
  composite_t *tmp;

  tmp = alloc_lambda_composite();
  init_lambda(tmp, t, tag);
  return tmp;
}


/*
 * Composites allocated in arena m
 */
composite_t *arena_apply_composite(arena_t *m, occ_t f, uint32_t n, occ_t *a) {
  composite_t *tmp;

  tmp = arena_alloc_composite(m, n + 1);
  init_apply(tmp, f, n, a);
  return tmp;
}

composite_t *arena_update_composite(arena_t *m, occ_t f, uint32_t n, occ_t *a, occ_t v) {
  composite_t *tmp;

  tmp = arena_alloc_composite(m, n + 2);
  init_update(tmp, f, n, a, v);
  return tmp;
}

composite_t *arena_tuple_composite(arena_t *m, uint32_t n, occ_t *a) {
  composite_t *tmp;

  tmp = arena_alloc_composite(m, n);
  init_tuple(tmp, n, a);
  return tmp;
}

composite_t *arena_eq_composite(arena_t *m, occ_t t1, occ_t t2) {
  composite_t *tmp;

  tmp = arena_alloc_composite(m, 2);
  init_eq(tmp, t1, t2);
  return tmp;
}

composite_t *arena_distinct_composite(arena_t *m, uint32_t n, occ_t *a) {
  composite_t *tmp;

  tmp = arena_alloc_composite(m, n);
  init_distinct(tmp, n, a);
  return tmp;
}

composite_t *arena_ite_composite(arena_t *m, occ_t t1, occ_t t2, occ_t t3) {
  composite_t *tmp;

  tmp = arena_alloc_composite(m, 3);
  init_ite(tmp, t1, t2, t3);
  return tmp;
}

composite_t *arena_or_composite(arena_t *m, uint32_t n, occ_t *a) {
  composite_t *tmp;

  tmp = arena_alloc_composite(m, n);
  init_or(tmp, n, a);
  return tmp;
}

composite_t *arena_lambda_composite(arena_t *m, occ_t t, int32_t tag) {
  composite_t *tmp;

  tmp = arena_alloc_lambda_composite(m);
  init_lambda(tmp, t, tag);
  return tmp;
}


/*
 * Variants for or and distinct: do not allocate the hook parts
 * - these composites cannot be attached to the parents vectors
 */
composite_t *new_distinct_composite_var(uint32_t n, occ_t *a) {
  composite_t *tmp;
  uint32_t i;

  assert(n <= MAX_COMPOSITE_ARITY);

  tmp = (composite_t *) safe_malloc(sizeof(composite_t) + n * sizeof(int32_t));
  init_header(tmp, mk_distinct_tag(n));
  for (i=0; i<n; i++) {
    tmp->child[i] = a[i];
  }

  return tmp;
}

composite_t *new_or_composite_var(uint32_t n, occ_t *a) {
  composite_t *tmp;
  uint32_t i;

  assert(n <= MAX_COMPOSITE_ARITY);

  tmp = (composite_t *) safe_malloc(sizeof(composite_t) + n * sizeof(int32_t));
  init_header(tmp, mk_or_tag(n));
  for (i=0; i<n; i++) {
    tmp->child[i] = a[i];
  }

  return tmp;
}




/**************************
 *  HASH-CONSING SUPPORT  *
 *************************/

/*
 * Syntactic equality:
 * check whether  c == (apply f a[0] ... a[n-1]) etc.
 */
static inline bool equal_children(int32_t *ch, uint32_t n, occ_t *a) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (ch[i] != a[i]) return false;
  }
  return true;
}


bool equal_apply(composite_t *c, occ_t f, uint32_t n, occ_t *a) {
  return c->tag == mk_apply_tag(n + 1) && c->child[0] == f &&
    equal_children(c->child + 1, n, a);
}

bool equal_update(composite_t *c, occ_t f, uint32_t n, occ_t *a, occ_t v) {
  return c->tag == mk_update_tag(n + 2) && c->child[0] == f &&
    equal_children(c->child + 1, n, a) && c->child[n+1] == v;
}

bool equal_tuple(composite_t *c, uint32_t n, occ_t *a) {
  return c->tag == mk_tuple_tag(n) && equal_children(c->child, n, a);
}

bool equal_eq(composite_t *c, occ_t t1, occ_t t2) {
  return c->tag == mk_eq_tag() && c->child[0] == t1 && c->child[1] == t2;
}

bool equal_ite(composite_t *c, occ_t t1, occ_t t2, occ_t t3) {
  return c->tag == mk_ite_tag() && c->child[0] == t1 &&
    c->child[1] == t2 && c->child[2] == t3;
}

bool equal_distinct(composite_t *c, uint32_t n, occ_t *a) {
  return c->tag == mk_distinct_tag(n) && equal_children(c->child, n, a);
}

bool equal_or(composite_t *c, uint32_t n, occ_t *a) {
  return c->tag == mk_or_tag(n) && equal_children(c->child, n, a);
}

bool equal_lambda(composite_t *c, occ_t t, int32_t tag) {
  return c->tag == mk_lambda_tag() && c->child[0] == t && c->child[2] == tag;
}


/*
 * The hash functions are based on Jenkins's lookup3.c code
 * (public domain code, see http://www.burtleburtle.net)
 */
#define rot(x,k) (((x)<<(k)) | ((x)>>(32-(k))))

#define mix(x,y,z)                  \
{                                   \
  x -= z;  x ^= rot(z, 4);  z += y; \
  y -= x;  y ^= rot(x, 6);  x += z; \
  z -= y;  z ^= rot(y, 8);  y += x; \
  x -= z;  x ^= rot(z,16);  z += y; \
  y -= x;  y ^= rot(x,19);  x += z; \
  z -= y;  z ^= rot(y, 4);  y += x; \
}

#define final(x,y,z)      \
{                         \
  z ^= y; z -= rot(y,14); \
  x ^= z; x -= rot(z,11); \
  y ^= x; y -= rot(x,25); \
  z ^= y; z -= rot(y,16); \
  x ^= z; x -= rot(z,4);  \
  y ^= x; y -= rot(x,14); \
  z ^= y; z -= rot(y,24); \
}

#define hash_uint32(x)              \
{                                   \
  x = (x + 0x7ed55d16) + (x<<12);   \
  x = (x ^ 0xc761c23c) ^ (x>>19);   \
  x = (x + 0x165667b1) + (x<<5);    \
  x = (x + 0xd3a2646c) ^ (x<<9);    \
  x = (x + 0xfd7046c5) + (x<<3);    \
  x = (x ^ 0xb55a4f09) ^ (x>>16);   \
}



/*
 * Combine x, y, z with a[0] .. a[n-1]
 */
static uint32_t hash_aux(uint32_t n, int32_t *a, uint32_t x, uint32_t y, uint32_t z) {
  while (n > 3) {
    x += a[0];
    y += a[1];
    z += a[2];
    mix(x, y, z);
    n -= 3;
    a += 3;
  }

  switch (n) {
  case 3: z += a[2];
  case 2: y += a[1];
  case 1: x += a[0];
    final(x, y, z);
  default:
    break;
  }

  return z;
}


/*
 * Hashcode for hash-consing
 * (not the same as the internal c->hash, which is used for congruence)
 */
uint32_t hash_apply(occ_t f, uint32_t n, occ_t *a) {
  return hash_aux(n, a, f + mk_apply_tag(n+1), 0x1abe2834, 0x1abe2834);
}

uint32_t hash_update(occ_t f, uint32_t n, occ_t *a, occ_t v) {
  return hash_aux(n, a, f + mk_update_tag(n+2), v, 0x81238354);
}

uint32_t hash_tuple(uint32_t n, occ_t *a) {
  return hash_aux(n, a, mk_tuple_tag(n), 0x3ef56a27, 0x3ef56a27);
}

uint32_t hash_eq(occ_t t1, occ_t t2) {
  uint32_t x;

  x = (t1 << 16) + t2;
  hash_uint32(x);
  return x;
}

uint32_t hash_ite(occ_t t1, occ_t t2, occ_t t3) {
  uint32_t x, y, z;

  x = t1;
  y = t2;
  z = t3;
  final(x, y, z);

  return z;
}

uint32_t hash_distinct(uint32_t n, occ_t *a) {
  return hash_aux(n, a, mk_distinct_tag(n), 0xdef67a81, 0xdef67a81);
}

uint32_t hash_or(uint32_t n, occ_t *a) {
  return hash_aux(n, a, mk_or_tag(n), 0x9279a675, 0x9279a675);
}

uint32_t hash_lambda(occ_t t, int32_t tag) {
  uint32_t x, y, z;

  x = t;
  y = tag;
  z = 0xabdaabda;
  final(x, y, z);

  return z;
}


uint32_t hash_composite(composite_t *c) {
  uint32_t tag, n;

  tag = c->tag;
  n = tag_arity(tag);

  switch (tag_kind(tag)) {
  case COMPOSITE_APPLY:
    return hash_apply(c->child[0], n - 1, c->child + 1);
  case COMPOSITE_UPDATE:
    return hash_update(c->child[0], n - 2, c->child + 1, c->child[n - 1]);
  case COMPOSITE_TUPLE:
    return hash_tuple(n, c->child);
  case COMPOSITE_EQ:
    return hash_eq(c->child[0], c->child[1]);
  case COMPOSITE_ITE:
    return hash_ite(c->child[0], c->child[1], c->child[2]);
  case COMPOSITE_DISTINCT:
    return hash_distinct(n, c->child);
  case COMPOSITE_OR:
    return hash_or(n, c->child);
  case COMPOSITE_LAMBDA:
    return hash_lambda(c->child[0], c->child[2]);
  }
  // prevent GCC warning
  assert(false);
  return 0;
}



/**********************************************
 *  ADDITION AND REMOVAL FROM PARENT VECTORS  *
 *********************************************/

/*
 * Get class id for t (i.e., remove the polarity bits)
 */
static inline class_t get_class(elabel_t *label, occ_t t) {
  return class_of(label[term_of_occ(t)]);
}

/*
 * Get label for t:
 * - if t has positive polarity, that's label[term_of(t)]
 * - if t has negative polarity, that's label[term_of(t)] ^ 1 (flipped polarity)
 */
static inline elabel_t get_label(elabel_t *label, occ_t t) {
  return label[term_of_occ(t)] ^ polarity_of_occ(t);
}

/*
 * Check whether c0 = class of child[i] is a duplicate, i.e.,
 * whether there's a j<i such that get_class(child[j]) == c0
 */
static bool duplicate_class(occ_t *child, elabel_t *label, class_t c0, uint32_t i) {
  uint32_t j;

  for (j=0; j<i; j++) {
    if (get_class(label, child[j]) == c0) return true;
  }
  return false;
}

/*
 * Attach c to the use vectors u, using labeling label
 * - if c->child[i] = t, then c is added to u[k]
 *   where k = class of t = class_of(label[term_of(t)])
 */
void attach_composite(composite_t *c, elabel_t *label, use_vector_t *u) {
  uint32_t i, n;
  int32_t *h, *child;
  int32_t k;
  class_t c0;

  n = composite_arity(c);
  h = composite_hooks(c);
  child = c->child;

  for (i=0; i<n; i++) {
    c0 = get_class(label, child[i]);
    if (duplicate_class(child, label, c0, i)) {
      h[i] = duplicate_ptr;
    } else {
      k = use_vector_store(u + c0, c);
      h[i] = k;
    }
  }
}

/*
 * Converse operation: remove c from the use vectors u
 */
void detach_composite(composite_t *c, elabel_t *label, use_vector_t *u) {
  uint32_t i, n;
  int32_t *h;
  class_t c0;
  int32_t k;

  n = composite_arity(c);
  h = composite_hooks(c);
  for (i=0; i<n; i++) {
    k = h[i];
    if (k >= 0) {
      c0 = get_class(label, c->child[i]);
      clear_use_vector_entry(u + c0, k);
    }
  }
}

/*
 * Remove c from the use vectors, except u[r0]
 */
void separate_composite(composite_t *c, elabel_t *label, use_vector_t *u, class_t r0) {
  uint32_t i, n;
  int32_t *h;
  class_t c0;
  int32_t k;

  n = composite_arity(c);
  h = composite_hooks(c);
  for (i=0; i<n; i++) {
    k = h[i];
    c0 = get_class(label, c->child[i]);
    if (k >= 0 && c0 != r0) {
      clear_use_vector_entry(u + c0, k);
    }
  }
}

/*
 * Remove the hook to r0 from c;
 * - search for the first i such that class[child[i]] = r0.
 * - set corresponding hook[i] to no_ptr
 */
void unhook_composite(composite_t *c, elabel_t *label, class_t r0) {
  uint32_t i, n;
  int32_t *h;
  class_t c0;

  n = composite_arity(c);
  h = composite_hooks(c);
  for (i=0; i<n; i++) {
    c0 = get_class(label, c->child[i]);
    if (c0 == r0) {
      h[i] = no_ptr;
      break;
    }
  }

  assert(i < n);
}

/*
 * Hook composite c to class r0
 * - search for the first child in that class
 * - if its hook is negative, attach cmp to class r0
 * - if its hook is non-negative, there's nothing to do, c is already
 * in r0's use vector.
 */
void hook_composite(composite_t *c, elabel_t *label, use_vector_t *u, class_t r0) {
  uint32_t i, n;
  int32_t *h;
  class_t c0;
  int32_t k;

  n = composite_arity(c);
  h = composite_hooks(c);
  for (i=0; i<n; i++) {
    c0 = get_class(label, c->child[i]);
    if (c0 == r0) {
      k = h[i];
      if (k < 0) {
        k = use_vector_store(u + r0, c);
        h[i] = k;
      }
      break;
    }
  }

  assert(i < n);
}


/*
 * Hide c from the use vectors
 * if u[k] = c then u[k] is marked
 */
void hide_composite(composite_t *c, elabel_t *label, use_vector_t *u) {
  uint32_t i, n;
  int32_t *h;
  class_t c0;
  int32_t k;

  n = composite_arity(c);
  h = composite_hooks(c);
  for (i=0; i<n; i++) {
    k = h[i];
    if (k >= 0) {
      c0 = get_class(label, c->child[i]);
      mark_use_vector_entry(u + c0, k);
    }
  }
}


/*
 * Converse operation: restore c
 * if u[k] = c then u[k] is unmarked
 */
void reveal_composite(composite_t *c, elabel_t *label, use_vector_t *u) {
  uint32_t i, n;
  int32_t *h;
  class_t c0;
  int32_t k;

  n = composite_arity(c);
  h = composite_hooks(c);
  for (i=0; i<n; i++) {
    k = h[i];
    if (k >= 0) {
      c0 = get_class(label, c->child[i]);
      unmark_use_vector_entry(u + c0, k);
    }
  }
}



/****************************
 *  SIGNATURE COMPUTATION   *
 ***************************/

#define INIT_SIGN_BUFFER_SIZE 8

/*
 * Initialize buffer s
 */
void init_sign_buffer(signature_t *s) {
  s->size = INIT_SIGN_BUFFER_SIZE;
  s->tag = 0;
  s->sigma = (elabel_t *) safe_malloc(INIT_SIGN_BUFFER_SIZE * sizeof(elabel_t));
}

/*
 * Increase size to at least n
 */
static void resize_sign_buffer(signature_t *s, uint32_t n) {
  assert(n <= MAX_COMPOSITE_ARITY);
  if (s->size < n) {
    s->size = n;
    s->sigma = (elabel_t *) safe_realloc(s->sigma, n * sizeof(elabel_t));
  }
}

/*
 * Delete
 */
void delete_sign_buffer(signature_t *s) {
  safe_free(s->sigma);
  s->sigma = NULL;
}


/*
 * Normalize the signature for an equality term (eq t0 t1)
 * - s[0] and s[1] must the labels of t0 and t1
 * - ensure lhs has positive polarity and lhs < rhs
 */
static void normalize_sigma_eq(elabel_t *s) {
  elabel_t l;
  uint32_t sgn;

  if (s[1] < s[0]) {
    l = s[0]; s[0] = s[1]; s[1] = l;
  }
  sgn = sign_of(s[0]);
  s[0] ^= sgn;
  s[1] ^= sgn;
}




/*
 * Simple signature for apply/update/tuple terms
 */
void signature_basic(composite_t *c, elabel_t *label, signature_t *s) {
  uint32_t i, n, tag;

  tag = c->tag;
  n = tag_arity(tag);
  resize_sign_buffer(s, n);
  s->tag = tag;
  for (i=0; i<n; i++) {
    s->sigma[i] = get_label(label, c->child[i]);
  }
}

/*
 * equality term
 */
void signature_eq(composite_t *c, elabel_t *label, signature_t *s) {
  assert(c->tag == mk_eq_tag());
  s->tag = mk_eq_tag();
  s->sigma[0] = get_label(label, c->child[0]);
  s->sigma[1] = get_label(label, c->child[1]);
  normalize_sigma_eq(s->sigma);
}

/*
 * Normalize: make l0 positive, swap l1 and l2 if necessary
 * (i.e., rewrite (ite (not t) t1 t2) to (ite t t2 t1))
 */
void signature_ite(composite_t *c, elabel_t *label, signature_t *s) {
  elabel_t l0, l1, l2;

  assert(c->tag == mk_ite_tag());
  l0 = get_label(label, c->child[0]);
  l1 = get_label(label, c->child[1]);
  l2 = get_label(label, c->child[2]);

  s->tag = mk_ite_tag();
  if (is_pos_label(l0)) {
    s->sigma[0] = l0;
    s->sigma[1] = l1;
    s->sigma[2] = l2;
  } else {
    s->sigma[0] = opposite_label(l0);
    s->sigma[1] = l2;
    s->sigma[2] = l1;
  }
}

/*
 * Sort labels in increasing order
 */
void signature_distinct(composite_t *c, elabel_t *label, signature_t *s) {
  uint32_t i, n;
  occ_t *t;

  assert(composite_kind(c) == COMPOSITE_DISTINCT);
  n = composite_arity(c);
  t = c->child;

  resize_sign_buffer(s, n);
  for (i=0; i<n; i++) {
    s->sigma[i] = get_label(label, t[i]);
  }

  int_array_sort(s->sigma, n);
  s->tag = mk_distinct_tag(n);
}

/*
 * Sort, remove false and duplicate labels
 */
void signature_or(composite_t *c, elabel_t *label, signature_t *s) {
  uint32_t i, j, n;
  elabel_t l, l_aux, *a;
  occ_t *t;

  assert(composite_kind(c) == COMPOSITE_OR);
  n = composite_arity(c);
  a = s->sigma;
  t = c->child;

  resize_sign_buffer(s, n);

  // copy labels of t[0] ... t[n-1]
  // remove t[i] if t[i] == false
  j = 0;
  for (i=0; i<n; i++) {
    l = get_label(label, t[i]);
    if (l != false_label) {
      a[j] = l;
      j ++;
    }
  }
  n = j;

  if (n > 1) {
    // sort and remove duplicates
    int_array_sort(a, n);

    l = a[0];
    j = 1;
    for (i=1; i<n; i++) {
      l_aux = a[i];
      if (l_aux != l) {
        a[j] = l_aux;
        j ++;
        l = l_aux;
      }
    }
  }

  s->tag = mk_or_tag(j);
}


/*
 * For a lambda:
 * - the signature depends on label[c->child[0]] and on c->child[2] (lambda tag)
 */
void signature_lambda(composite_t *c, elabel_t *label, signature_t *s) {
  assert(composite_kind(c) == COMPOSITE_LAMBDA && composite_arity(c) == 1);

  s->tag = mk_lambda_tag();
  s->sigma[0] = get_label(label, c->child[0]);
  s->sigma[1] = c->child[2];
}


/*
 * Generic form
 */
void signature_composite(composite_t *c, elabel_t *label, signature_t *s) {
  switch (composite_kind(c)) {
  case COMPOSITE_APPLY:
  case COMPOSITE_UPDATE:
  case COMPOSITE_TUPLE:
    signature_basic(c, label, s);
    break;

  case COMPOSITE_EQ:
    signature_eq(c, label, s);
    break;

  case COMPOSITE_ITE:
    signature_ite(c, label, s);
    break;

  case COMPOSITE_DISTINCT:
    signature_distinct(c, label, s);
    break;

  case COMPOSITE_OR:
    signature_or(c, label, s);
    break;

  case COMPOSITE_LAMBDA:
    signature_lambda(c, label, s);
    break;
  }
}



/*
 * Compute a hash of signature s
 */
uint32_t hash_signature(signature_t *s) {
  uint32_t n;

  n = tag_arity(s->tag);
  return hash_aux(n, s->sigma, s->tag, 0xdeadbeef, 0xdeadbeef);
}



/*
 * Check whether s1 and s2 are equal
 */
bool equal_signatures(signature_t *s1, signature_t *s2) {
  uint32_t tag, i, n;

  tag = s1->tag;
  if (tag != s2->tag) return false;

  n = tag_arity(tag);
  for (i=0; i<n; i++) {
    if (s1->sigma[i] != s2->sigma[i]) return false;
  }

  return true;
}


/*
 * Check whether c's signature is equal to s
 */
bool signature_matches(composite_t *c, signature_t *s, signature_t *aux, elabel_t *label) {
  uint32_t i, n, c_tag, s_tag;
  elabel_t l[3];

  c_tag = c->tag;
  s_tag = s->tag;
  if (tag_kind(c_tag) != tag_kind(s_tag)) return false;

  switch (tag_kind(c_tag)) {
  case COMPOSITE_APPLY:
  case COMPOSITE_UPDATE:
  case COMPOSITE_TUPLE:
    n = tag_arity(c_tag);
    if (n != tag_arity(s_tag)) return false;
    for (i=0; i<n; i++) {
      if (s->sigma[i] != get_label(label, c->child[i])) {
        return false;
      }
    }
    return true;

  case COMPOSITE_EQ:
    l[0] = get_label(label, c->child[0]);
    l[1] = get_label(label, c->child[1]);
    normalize_sigma_eq(l);
    return s->sigma[0] == l[0] && s->sigma[1] == l[1];

  case COMPOSITE_ITE:
    l[0] = get_label(label, c->child[0]);
    l[1] = get_label(label, c->child[1]);
    l[2] = get_label(label, c->child[2]);
    return (s->sigma[0] == l[0] && s->sigma[1] == l[1] && s->sigma[2] == l[2])
      || (s->sigma[0] == opposite_label(l[0]) && s->sigma[1] == l[2] && s->sigma[2] == l[1]);

  case COMPOSITE_DISTINCT:
    signature_distinct(c, label, aux);
    return equal_signatures(s, aux);

  case COMPOSITE_OR:
    signature_or(c, label, aux);
    return equal_signatures(s, aux);

  case COMPOSITE_LAMBDA:
    return s->sigma[0] == get_label(label, c->child[0]) && s->sigma[1] == c->child[2];
  }

  // prevents a GCC warning
  assert(false);
  return false;
}



/**********************************
 *  SUPPORT FOR THE ARRAY SOLVER  *
 *********************************/

/*
 * Signature of (apply g i_1 ... i_n) given c = (apply f i_1 ... i_n)
 */
void signature_modified_apply(composite_t *c, eterm_t g, elabel_t *label, signature_t *s) {
  uint32_t i, n, tag;

  tag = c->tag;
  n = tag_arity(tag);
  resize_sign_buffer(s, n);
  s->tag = tag;
  s->sigma[0] = label[g];  // function term = label of g
  for (i=1; i<n; i++) {    // children
    s->sigma[i] = get_label(label, composite_child(c, i));
  }
}


/*
 * Variant: signature of (apply glabel i1 ... in)
 */
void signature_modified_apply2(composite_t *c, elabel_t glabel, elabel_t *label, signature_t *s) {
  uint32_t i, n, tag;

  tag = c->tag;
  n = tag_arity(tag);
  resize_sign_buffer(s, n);
  s->tag = tag;
  s->sigma[0] = glabel;    // function label
  for (i=1; i<n; i++) {    // children
    s->sigma[i] = get_label(label, composite_child(c, i));
  }
}


/*
 * Check whether two apply composites have the same argument tuple (modulo the egraph)
 * - c must be of the form (apply f i_1 ... i_n)
 *   d must be of the form (apply g j_i ... j_m)
 * - return true if n == m and label[i_1] = label[j_1], ..., label[i_n] = label[j_m]
 */
bool same_arg_signature(composite_t *c, composite_t *d, elabel_t *label) {
  uint32_t i, n;

  assert(composite_kind(c) == COMPOSITE_APPLY && composite_kind(d) == COMPOSITE_APPLY);

  n = composite_arity(c);
  if (n != composite_arity(d)) {
    return false;
  }

  for (i=1; i<n; i++) {
    if (get_label(label, composite_child(c, i)) != get_label(label, composite_child(d, i))) {
      return false;
    }
  }

  return true;
}


/*
 * Compute a hash code of c's argument tuple
 * - c must be of the form (apply f i_1 ... i_n)
 * - return a hash computed based one n and label[i_1], ..., label[i_n]
 * - so if same_arg_signature(c, d, label) is true then
 *   hash_arg_signature(c, label) = hash_arg_signature(d, label).
 */
uint32_t hash_arg_signature(composite_t *c, elabel_t *label) {
  int32_t *a;
  uint32_t n;
  uint32_t x, y, z;

  assert(composite_kind(c) == COMPOSITE_APPLY);
  n = composite_arity(c);
  assert(n > 0);
  n --;
  a = c->child + 1; // skip child[0] = f

  x = y = z = 0xdeadbeef + (n << 2);
  while (n > 3) {
    x += (uint32_t) get_label(label, a[0]);
    y += (uint32_t) get_label(label, a[1]);
    z += (uint32_t) get_label(label, a[2]);
    mix(x, y, z);
    n -= 3;
    a += 3;
  }

  switch (n) {
  case 3: z += (uint32_t) get_label(label, a[2]);
  case 2: y += (uint32_t) get_label(label, a[1]);
  case 1: x += (uint32_t) get_label(label, a[0]);
    final(x, y, z);
  default:
    break;
  }

  return z;
}




/**********************
 *  CONGRUENCE TABLE  *
 *********************/

/*
 * For debugging: check whether n is a power of two
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Initialization.
 * - n = size, if n = 0, the default size is used.
 */
void init_congruence_table(congruence_table_t *tbl, uint32_t n) {
  uint32_t i;
  composite_t **tmp;

  if (n == 0) {
    n = DEFAULT_CONGRUENCE_TBL_SIZE;
  }

  if (n >= MAX_CONGRUENCE_TBL_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  tmp = (composite_t **) safe_malloc(n * sizeof(composite_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL_COMPOSITE;
  }

  tbl->data = tmp;
  tbl->size = n;
  tbl->nelems = 0;
  tbl->ndeleted = 0;

  tbl->resize_threshold = (uint32_t)(n * CONGRUENCE_TBL_RESIZE_RATIO);
  tbl->cleanup_threshold = (uint32_t)(n * CONGRUENCE_TBL_CLEANUP_RATIO);

  init_sign_buffer(&tbl->buffer);
}


/*
 * Reset: remove all composites
 */
void reset_congruence_table(congruence_table_t *tbl) {
  uint32_t i, n;

  n = tbl->size;
  for (i=0; i<n; i++) {
    tbl->data[i] = NULL_COMPOSITE;
  }

  tbl->nelems = 0;
  tbl->ndeleted = 0;
}


/*
 * Delete
 */
void delete_congruence_table(congruence_table_t *tbl) {
  safe_free(tbl->data);
  tbl->data = NULL;
  delete_sign_buffer(&tbl->buffer);
}


/*
 * Store composite d in a clean data array
 * - mask = size of data - 1
 * - d->hash is the hash code of d
 * data must not contain any deleted eterms and must have at least one empty slot
 */
static void congruence_table_clean_copy(composite_t **data, composite_t *d, uint32_t mask) {
  uint32_t j;

  j = d->hash & mask;
  while (data[j] != NULL_COMPOSITE) {
    j ++;
    j &= mask;
  }
  data[j] = d;
}


/*
 * Check whether a pointer is non-deleted and non-null
 */
static inline bool live_ptr(composite_t *d) {
  return (((uintptr_t) d) & ~((uintptr_t) 1)) != 0;
}


/*
 * Remove deleted elements
 */
static void congruence_table_cleanup(congruence_table_t *tbl) {
  composite_t **tmp, *d;
  uint32_t j, n, mask;

  n = tbl->size;
  tmp = (composite_t **) safe_malloc(n * sizeof(composite_t *));
  for (j=0; j<n; j++) {
    tmp[j] = NULL_COMPOSITE;
  }

  mask = n - 1;
  for (j=0; j<n; j++) {
    d = tbl->data[j];
    if (live_ptr(d)) {
      congruence_table_clean_copy(tmp, d, mask);
    }
  }

  safe_free(tbl->data);
  tbl->data = tmp;
  tbl->ndeleted = 0;
}


/*
 * Remove deleted elements and make the table twice as large
 */
static void congruence_table_extend(congruence_table_t *tbl) {
  composite_t **tmp;
  uint32_t n, n2, j, mask;
  composite_t *d;

  n = tbl->size;
  n2 = n<<1;
  if (n2 >= MAX_CONGRUENCE_TBL_SIZE) {
    out_of_memory();
  }

  tmp = (composite_t **) safe_malloc(n2 * sizeof(composite_t *));
  for (j=0; j<n2; j++) {
    tmp[j] = NULL_COMPOSITE;
  }

  mask = n2 - 1;
  for (j=0; j<n; j++) {
    d = tbl->data[j];
    if (live_ptr(d)) {
      congruence_table_clean_copy(tmp, d, mask);
    }
  }

  safe_free(tbl->data);
  tbl->data = tmp;
  tbl->ndeleted = 0;
  tbl->size = n2;

  tbl->resize_threshold = (uint32_t)(n2 * CONGRUENCE_TBL_RESIZE_RATIO);
  tbl->cleanup_threshold = (uint32_t)(n2 * CONGRUENCE_TBL_CLEANUP_RATIO);
}


/*
 * Remove c from the congruence table.
 * - c must be in the table otherwise the function loops
 */
void congruence_table_remove(congruence_table_t *tbl, composite_t *c) {
  uint32_t mask, j;

  mask = tbl->size - 1;
  j = c->hash & mask;
  while (tbl->data[j] != c) {
    j ++;
    j &= mask;
  }

  assert(tbl->data[j] == c);
  tbl->data[j] = DELETED_COMPOSITE;
  tbl->nelems --;
  tbl->ndeleted ++;
  if (tbl->ndeleted > tbl->cleanup_threshold) {
    congruence_table_cleanup(tbl);
  }
}


/*
 * Remove c from the table if it's present. No change otherwise.
 * The table must not be full.
 * - return true if c has been removed
 * - return false if c was not present
 */
bool congruence_table_remove_if_present(congruence_table_t *tbl, composite_t *c) {
  uint32_t mask, j;
  composite_t *aux;

  assert(tbl->size > tbl->ndeleted + tbl->nelems);

  mask = tbl->size - 1;
  j = c->hash & mask;
  for (;;) {
    aux = tbl->data[j];
    if (aux == c) break;
    if (aux == NULL_COMPOSITE) return false; // c not in the table
    j ++;
    j &= mask;
  }

  assert(tbl->data[j] == c);
  tbl->data[j] = DELETED_COMPOSITE;
  tbl->nelems --;
  tbl->ndeleted ++;
  if (tbl->ndeleted > tbl->cleanup_threshold) {
    congruence_table_cleanup(tbl);
  }

  return true;
}




/*
 * Add c to tbl,
 * - use only if it is known that no term is congruent to c
 */
void congruence_table_add(congruence_table_t *tbl, composite_t *c) {
  uint32_t mask, j;

  assert(tbl->size > tbl->ndeleted + tbl->nelems);

  mask = tbl->size - 1;
  j = c->hash & mask;
  while (live_ptr(tbl->data[j])) {
    j ++;
    j &= mask;
  }

  tbl->data[j] = c;
  tbl->nelems ++;
  if (tbl->nelems + tbl->ndeleted > tbl->resize_threshold) {
    congruence_table_extend(tbl);
  }
}


/*
 * Search for a composite of signature s in the table.
 * Return NULL_COMPOSITE if there's none.
 * - the table must not be full
 */
composite_t  *congruence_table_find(congruence_table_t *tbl, signature_t *s, elabel_t *label) {
  uint32_t mask, j, h;
  composite_t *c;

  mask = tbl->size - 1;
  h = hash_signature(s);
  j = h & mask;
  for (;;) {
    c = tbl->data[j];
    if (c == NULL_COMPOSITE ||
        (c != DELETED_COMPOSITE && c->hash == h && signature_matches(c, s, &tbl->buffer, label))) {
      return c;
    }
    j ++;
    j &= mask;
  }
}




/*
 * Auxiliary functions for find_eq to avoid intermediate signature buffer
 */
// cf. hash_signature
static inline uint32_t hash_sigma_eq(elabel_t *sigma) {
  return hash_aux(2, sigma, mk_eq_tag(), 0xdeadbeef, 0xdeadbeef);
}

static inline bool matches_sigma_eq(composite_t *c, elabel_t *sigma, elabel_t *label) {
  elabel_t s[2];
  s[0] = get_label(label, c->child[0]);
  s[1] = get_label(label, c->child[1]);
  normalize_sigma_eq(s);
  return s[0] == sigma[0] && s[1] == sigma[1];
}


/*
 * Search for a composite congruent to (eq t1 t2)
 * - return NULL_COMPOSITE if there's none
 */
composite_t *congruence_table_find_eq(congruence_table_t *tbl, occ_t t1, occ_t t2, elabel_t *label) {
  uint32_t mask, j, h;
  composite_t *c;
  elabel_t s[2];

  s[0] = get_label(label, t1);
  s[1] = get_label(label, t2);
  normalize_sigma_eq(s);
  h = hash_sigma_eq(s);

  mask = tbl->size - 1;
  j = h & mask;
  for (;;) {
    c = tbl->data[j];
    if (c == NULL_COMPOSITE ||
        (c != DELETED_COMPOSITE &&
         c->tag == mk_eq_tag() && c->hash == h && matches_sigma_eq(c, s, label))) {
      return c;
    }
    j ++;
    j &= mask;
  }

}


/*
 * Find a composite term congruent to c modulo root in tbl.
 * If there is none, insert c in tbl.
 */
composite_t  *congruence_table_get(congruence_table_t *tbl, composite_t *c, signature_t *s, elabel_t *label) {
  uint32_t mask, j, k, h;
  composite_t *aux;

  assert(tbl->size > tbl->ndeleted + tbl->nelems);

  mask = tbl->size - 1;
  h = hash_signature(s);
  c->hash = h;
  j = h & mask;

  for (;;) {
    aux = tbl->data[j];
    if (aux == NULL_COMPOSITE) goto add;
    if (aux == DELETED_COMPOSITE) break;
    if (aux->hash == h && signature_matches(aux, s, &tbl->buffer, label)) goto found;
    j ++;
    j &= mask;
  }

  // j is where addition will happen if necessary
  k = j;
  for (;;) {
    k++;
    k &= mask;
    aux = tbl->data[k];
    if (aux == NULL_COMPOSITE) {
      tbl->ndeleted --;
      goto add;
    }
    if (aux != DELETED_COMPOSITE &&
        aux->hash == h && signature_matches(aux, s, &tbl->buffer, label)) goto found;
  }

 add:
  tbl->data[j] = c;
  tbl->nelems ++;
  if (tbl->nelems + tbl->ndeleted > tbl->resize_threshold) {
    congruence_table_extend(tbl);
  }
  return c;


 found:
  return aux;
}




/*
 * Check whether c is a congruence root
 * - use the internal buffer to compute c's signature and hash code
 * - no change to c->hash
 */
bool congruence_table_is_root(congruence_table_t *tbl, composite_t *c, elabel_t *label) {
  uint32_t mask, j;
  signature_t *s;
  composite_t *aux;

  assert(tbl->size > tbl->ndeleted + tbl->nelems);

  s = &tbl->buffer;
  signature_composite(c, label, s);

  mask = tbl->size - 1;
  j = hash_signature(s) & mask;
  for (;;) {
    aux = tbl->data[j];
    if (aux == c) return true;
    if (aux == NULL_COMPOSITE) return false;
    j ++;
    j &= mask;
  }
}


