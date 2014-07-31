/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * VARIABLE TABLE FOR BITVECTOR SOLVER
 */

#include "utils/memalloc.h"
#include "utils/hash_functions.h"
#include "terms/bv64_constants.h"
#include "terms/bv_constants.h"

#include "solvers/bv/bv_vartable.h"


/*
 * Initialize table
 * - use the default size
 * - the eterm array is not allocated here, but on the first
 *   call to attach_eterm
 * - variable 0 is reserved to prevent confusion with const_idx
 */
void init_bv_vartable(bv_vartable_t *table) {
  uint32_t n;

  n = DEF_BVVARTABLE_SIZE;
  assert(1 <= n && n < MAX_BVVARTABLE_SIZE);

  table->nvars = 1;
  table->size = n;
  table->bit_size = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  table->kind = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  table->def = (bvvar_desc_t *) safe_malloc(n * sizeof(bvvar_desc_t));
  table->eterm = NULL;
  table->map = (literal_t **) safe_malloc(n * sizeof(literal_t *));

  // fake descriptor for variable 0
  table->map[0] = NULL;
  table->def[0].ptr = NULL;
  table->kind[0] = BVTAG_VAR;
  table->bit_size[0] = 0;

  init_int_htbl(&table->htbl, 0);
}


/*
 * Make the table 50% larger
 */
static void extend_bv_vartable(bv_vartable_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;

  if (n >= MAX_BVVARTABLE_SIZE) {
    out_of_memory();
  }

  table->bit_size = (uint32_t *) safe_realloc(table->bit_size, n * sizeof(uint32_t));
  table->kind = (uint8_t *) safe_realloc(table->kind, n * sizeof(uint8_t));
  table->def = (bvvar_desc_t *) safe_realloc(table->def, n * sizeof(bvvar_desc_t));
  if (table->eterm != NULL) {
    table->eterm = (eterm_t *) safe_realloc(table->eterm, n * sizeof(eterm_t));
  }
  table->map = (literal_t **) safe_realloc(table->map, n * sizeof(literal_t *));

  table->size = n;
}


/*
 * Delete the table
 */
void delete_bv_vartable(bv_vartable_t *table) {
  uint32_t i, n;

  n = table->nvars;
  for (i=1; i<n; i++) {
    int_array_decref(table->map[i]);
    switch (bvvar_tag(table, i)) {
    case BVTAG_CONST:
    case BVTAG_POLY64:
    case BVTAG_PPROD:
    case BVTAG_BIT_ARRAY:
    case BVTAG_ITE:
      safe_free(table->def[i].ptr);
      break;

    case BVTAG_POLY:
      free_bvpoly(table->def[i].ptr);
      break;

    default:
      break;
    }
  }

  safe_free(table->bit_size);
  safe_free(table->kind);
  safe_free(table->def);
  safe_free(table->eterm);
  safe_free(table->map);

  table->bit_size = NULL;
  table->kind = NULL;
  table->def = NULL;
  table->eterm = NULL;
  table->map = NULL;

  delete_int_htbl(&table->htbl);
}


/*
 * Reset: empty the table
 */
void reset_bv_vartable(bv_vartable_t *table) {
  uint32_t i, n;

  n = table->nvars;
  for (i=1; i<n; i++) {
    int_array_decref(table->map[i]);
    switch (bvvar_tag(table, i)) {
    case BVTAG_CONST:
    case BVTAG_POLY64:
    case BVTAG_PPROD:
    case BVTAG_BIT_ARRAY:
    case BVTAG_ITE:
      safe_free(table->def[i].ptr);
      break;

    case BVTAG_POLY:
      free_bvpoly(table->def[i].ptr);
      break;

    default:
      break;
    }
  }

  table->nvars = 1;

  reset_int_htbl(&table->htbl);
}


/*
 * Attach egraph term t to variable x
 * - x must be not have an eterm attached already
 */
void attach_eterm_to_bvvar(bv_vartable_t *table, thvar_t x, eterm_t t) {
  eterm_t *tmp;
  uint32_t i, n;

  assert(1 <= x && x < table->nvars && t != null_eterm);

  tmp = table->eterm;
  if (tmp == NULL) {
    n = table->size;
    tmp = (eterm_t *) safe_malloc(n * sizeof(eterm_t));
    n = table->nvars;
    for (i=0; i<n; i++) {
      tmp[i] = null_eterm;
    }
    table->eterm = tmp;
  }
  assert(tmp[x] == null_eterm);
  tmp[x] = t;
}




/*
 * Remove all eterms of id >= nterms
 */
void bv_vartable_remove_eterms(bv_vartable_t *table, uint32_t nterms) {
  eterm_t *tmp;
  uint32_t i, n;
  eterm_t t;

  tmp = table->eterm;

  if (tmp != NULL) {
    n = table->nvars;
    for (i=1; i<n; i++) {
      t = tmp[i];
      if (t != null_eterm && t >= nterms) {
        tmp[i] = null_eterm;
      }
    }
  }
}



/*
 * Hash codes of a variable descriptor
 *
 * For bvpoly and bvpoly64 we use
 * hash_bvpoly   (in bv_polynomials)
 * hash_bvpoly64 (in bv64_polynomials)
 *
 */
// n = number of bits
static inline uint32_t hash_bvconst64(uint64_t c, uint32_t n) {
  uint32_t a, b;
  a = jenkins_hash_uint64(c);
  b = jenkins_hash_uint32(n);
  return jenkins_hash_mix2(a, b);
}

static inline uint32_t hash_bvconst(uint32_t *c, uint32_t n) {
  return bvconst_hash(c, n);
}

// array of k pairs (variable, exponent)
static inline uint32_t hash_bvpprod_array(varexp_t *a, uint32_t k) {
  assert(k <= UINT32_MAX/2);
  return jenkins_hash_intarray((int32_t *) a, 2 * k);
}

static inline uint32_t hash_bvpprod(pprod_t *p) {
  return hash_bvpprod_array(p->prod, p->len);
}

static inline uint32_t hash_bvarray(literal_t *b, uint32_t n) {
  return jenkins_hash_intarray2(b, n, 0xaed32b8);
}

static inline uint32_t hash_bvite(literal_t c, thvar_t x, thvar_t y) {
  return jenkins_hash_triple(c, x, y, 0xfe2efd45);
}

static inline uint32_t hash_bvite_ptr(bv_ite_t *d) {
  return hash_bvite(d->cond, d->left, d->right);
}

static inline uint32_t hash_bvdiv(thvar_t x, thvar_t y) {
  return jenkins_hash_pair(x, y, 0x2389a23f);
}

static inline uint32_t hash_bvrem(thvar_t x, thvar_t y) {
  return jenkins_hash_pair(x, y, 0x237bc32f);
}

static inline uint32_t hash_bvsdiv(thvar_t x, thvar_t y) {
  return jenkins_hash_pair(x, y, 0x9afe2ab2);
}

static inline uint32_t hash_bvsrem(thvar_t x, thvar_t y) {
  return jenkins_hash_pair(x, y, 0xbe7bca36);
}

static inline uint32_t hash_bvsmod(thvar_t x, thvar_t y) {
  return jenkins_hash_pair(x, y, 0xeab2d457);
}

static inline uint32_t hash_bvshl(thvar_t x, thvar_t y) {
  return jenkins_hash_pair(x, y, 0xc2ad173f);
}

static inline uint32_t hash_bvlshr(thvar_t x, thvar_t y) {
  return jenkins_hash_pair(x, y, 0x81023ae5);
}

static inline uint32_t hash_bvashr(thvar_t x, thvar_t y) {
  return jenkins_hash_pair(x, y, 0xc3e4fed1);
}

static inline uint32_t hash_bvadd(thvar_t x, thvar_t y) {
  return jenkins_hash_pair(x, y, 0x198cea23);
}

static inline uint32_t hash_bvsub(thvar_t x, thvar_t y) {
  return jenkins_hash_pair(x, y, 0xb8b423c6);
}

static inline uint32_t hash_bvmul(thvar_t x, thvar_t y) {
  return jenkins_hash_pair(x, y, 0x43c94873);
}

static inline uint32_t hash_bvneg(thvar_t x) {
  return jenkins_hash_pair(x, x, 0x4b0d5cff);
}



/*
 * Remove all variables of index >= nv
 */
void bv_vartable_remove_vars(bv_vartable_t *table, uint32_t nv) {
  uint32_t i, n, h;

  assert(1 <= nv && nv <= table->nvars);

  h = 0; // stop GCC warning

  n = table->nvars;
  for (i=nv; i<n; i++) {
    switch (bvvar_tag(table, i)) {
    case BVTAG_VAR:
      // no hash consing, no descriptor
      int_array_decref(table->map[i]);
      continue;

    case BVTAG_CONST64:
      h = hash_bvconst64(table->def[i].val, table->bit_size[i]);
      break;

    case BVTAG_CONST:
      h = hash_bvconst(table->def[i].ptr, table->bit_size[i]);
      safe_free(table->def[i].ptr);
      break;

    case BVTAG_POLY64:
      h = hash_bvpoly64(table->def[i].ptr);
      safe_free(table->def[i].ptr);
      break;

    case BVTAG_POLY:
      h = hash_bvpoly(table->def[i].ptr);
      free_bvpoly(table->def[i].ptr);
      break;

    case BVTAG_PPROD:
      h = hash_bvpprod(table->def[i].ptr);
      safe_free(table->def[i].ptr);
      break;

    case BVTAG_BIT_ARRAY:
      h = hash_bvarray(table->def[i].ptr, table->bit_size[i]);
      safe_free(table->def[i].ptr);
      break;

    case BVTAG_ITE:
      h = hash_bvite_ptr(table->def[i].ptr);
      safe_free(table->def[i].ptr);
      break;

    case BVTAG_UDIV:
      h = hash_bvdiv(table->def[i].op[0], table->def[i].op[1]);
      break;

    case BVTAG_UREM:
      h = hash_bvrem(table->def[i].op[0], table->def[i].op[1]);
      break;

    case BVTAG_SDIV:
      h = hash_bvsdiv(table->def[i].op[0], table->def[i].op[1]);
      break;

    case BVTAG_SREM:
      h = hash_bvsrem(table->def[i].op[0], table->def[i].op[1]);
      break;

    case BVTAG_SMOD:
      h = hash_bvsmod(table->def[i].op[0], table->def[i].op[1]);
      break;

    case BVTAG_SHL:
      h = hash_bvshl(table->def[i].op[0], table->def[i].op[1]);
      break;

    case BVTAG_LSHR:
      h = hash_bvlshr(table->def[i].op[0], table->def[i].op[1]);
      break;

    case BVTAG_ASHR:
      h = hash_bvashr(table->def[i].op[0], table->def[i].op[1]);
      break;

    case BVTAG_ADD:
      h = hash_bvadd(table->def[i].op[0], table->def[i].op[1]);
      break;

    case BVTAG_SUB:
      h = hash_bvsub(table->def[i].op[0], table->def[i].op[1]);
      break;

    case BVTAG_MUL:
      h = hash_bvmul(table->def[i].op[0], table->def[i].op[1]);
      break;

    case BVTAG_NEG:
      h = hash_bvneg(table->def[i].op[0]);
      break;
    }

    int_htbl_erase_record(&table->htbl, h, i);
    int_array_decref(table->map[i]);
  }

  table->nvars = nv;
}



/*
 * Allocate a new variable id of n bits
 * - the descriptors are partially initialized:
 *   bit_size = n
 *   eterm = null_eterm if table->eterm exists
 *   map = NULL
 * - def and kind are not set
 */
static thvar_t bv_vartable_alloc_id(bv_vartable_t *table, uint32_t n) {
  uint32_t x;

  x = table->nvars;
  if (x == table->size) {
    extend_bv_vartable(table);
  }
  assert(x < table->size);
  table->bit_size[x] = n;
  table->map[x] = NULL;
  if (table->eterm != NULL) {
    table->eterm[x] = null_eterm;
  }

  table->nvars = x + 1;

  return x;
}



/*
 * Constructors:
 * - all constructors create a new theory variable with the given definition
 * - when present n = bitsize of the new variable
 */
thvar_t make_bvvar(bv_vartable_t *table, uint32_t n) {
  thvar_t x;

  x = bv_vartable_alloc_id(table, n);
  table->kind[x] = BVTAG_VAR;

  return x;
}

static thvar_t make_bvconst64(bv_vartable_t *table, uint32_t n, uint64_t val) {
  thvar_t x;

  assert(norm64(val, n) == val);
  x = bv_vartable_alloc_id(table, n);
  table->kind[x] = BVTAG_CONST64;
  table->def[x].val = val;

  return x;
}

static thvar_t make_bvconst(bv_vartable_t *table, uint32_t n, uint32_t *val) {
  uint32_t *tmp;
  thvar_t x;
  uint32_t w;

  // make a copy of val
  w = (n + 31) >> 5;
  tmp = (uint32_t *) safe_malloc(w * sizeof(uint32_t));
  bvconst_set(tmp, w, val);
  bvconst_normalize(tmp, n);

  x = bv_vartable_alloc_id(table, n);
  table->kind[x] = BVTAG_CONST;
  table->def[x].ptr = tmp;

  return x;
}

static thvar_t make_bvpoly64(bv_vartable_t *table, bvpoly_buffer_t *b) {
  thvar_t x;

  x = bv_vartable_alloc_id(table, b->bitsize);
  table->kind[x] = BVTAG_POLY64;
  table->def[x].ptr = bvpoly_buffer_getpoly64(b);

  return x;
}

static thvar_t make_bvpoly(bv_vartable_t *table, bvpoly_buffer_t *b) {
  thvar_t x;

  x = bv_vartable_alloc_id(table, b->bitsize);
  table->kind[x] = BVTAG_POLY;
  table->def[x].ptr = bvpoly_buffer_getpoly(b);

  return x;
}

static thvar_t make_bvpprod(bv_vartable_t *table, uint32_t n, pp_buffer_t *b) {
  thvar_t x;

  x = bv_vartable_alloc_id(table, n);
  table->kind[x] = BVTAG_PPROD;
  table->def[x].ptr = pp_buffer_getprod(b);

  return x;
}

static thvar_t make_bvarray(bv_vartable_t *table, uint32_t n, literal_t *a) {
  literal_t *b;
  uint32_t i;
  thvar_t x;

  // make a copy of a
  b = (literal_t *) safe_malloc(n * sizeof(literal_t));
  for (i=0; i<n; i++) {
    b[i] = a[i];
  }

  x = bv_vartable_alloc_id(table, n);
  table->kind[x] = BVTAG_BIT_ARRAY;
  table->def[x].ptr = b;

  return x;
}

static thvar_t make_bvite(bv_vartable_t *table, uint32_t n, literal_t c, thvar_t left, thvar_t right) {
  bv_ite_t *b;
  thvar_t x;

  b = (bv_ite_t *) safe_malloc(sizeof(bv_ite_t));
  b->cond = c;
  b->left = left;
  b->right = right;

  x = bv_vartable_alloc_id(table, n);
  table->kind[x] = BVTAG_ITE;
  table->def[x].ptr = b;

  return x;
}


// binary operator: tag must be in BVTAG_UDIV ... BVTAG_ASHR
static thvar_t make_bvbinop(bv_vartable_t *table, bvvar_tag_t tag, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t z;

  z = bv_vartable_alloc_id(table, n);
  table->kind[z] = tag;
  table->def[z].op[0] = x;
  table->def[z].op[1] = y;

  return z;
}



/*
 * HASH CONSING OBJECTS (cf. int_hash_tables)
 */
typedef struct bvconst64_hobj_s {
  int_hobj_t m;
  bv_vartable_t *tbl;
  uint64_t val;
  uint32_t nbits;
} bvconst64_hobj_t;

typedef struct bvconst_hobj_s {
  int_hobj_t m;
  bv_vartable_t *tbl;
  uint32_t *val;
  uint32_t nbits;
} bvconst_hobj_t;

typedef struct bvpoly_hobj_s {
  int_hobj_t m;
  bv_vartable_t *tbl;
  bvpoly_buffer_t *buffer;
} bvpoly_hobj_t;

typedef struct bvpprod_hobj_s {
  int_hobj_t m;
  bv_vartable_t *tbl;
  pp_buffer_t *buffer;
  uint32_t nbits;
} bvpprod_hobj_t;

typedef struct bvarray_hobj_s {
  int_hobj_t m;
  bv_vartable_t *tbl;
  literal_t *val;
  uint32_t nbits;
} bvarray_hobj_t;

typedef struct bvite_hobj_s {
  int_hobj_t m;
  bv_vartable_t *tbl;
  literal_t cond;
  thvar_t left;
  thvar_t right;
  uint32_t nbits;
} bvite_hobj_t;

// for all binary constructors
typedef struct bvop_hobj_s {
  int_hobj_t m;
  bv_vartable_t *tbl;
  thvar_t left;
  thvar_t right;
  uint32_t nbits;
}  bvop_hobj_t;


/*
 * Hash functions
 */
static uint32_t hash_bvconst64_hobj(bvconst64_hobj_t *p) {
  return hash_bvconst64(p->val, p->nbits);
}

static uint32_t hash_bvconst_hobj(bvconst_hobj_t *p) {
  return hash_bvconst(p->val, p->nbits);
}

static uint32_t hash_bvpoly64_hobj(bvpoly_hobj_t *p) {
  return bvpoly_buffer_hash64(p->buffer);
}

static uint32_t hash_bvpoly_hobj(bvpoly_hobj_t *p) {
  return bvpoly_buffer_hash(p->buffer);
}

static uint32_t hash_bvpprod_hobj(bvpprod_hobj_t *p) {
  pp_buffer_t *b;

  b = p->buffer;
  return hash_bvpprod_array(b->prod, b->len);
}

static uint32_t hash_bvarray_hobj(bvarray_hobj_t *p) {
  return hash_bvarray(p->val, p->nbits);
}

static uint32_t hash_bvite_hobj(bvite_hobj_t *p) {
  return hash_bvite(p->cond, p->left, p->right);
}

static uint32_t hash_bvdiv_hobj(bvop_hobj_t *p) {
  return hash_bvdiv(p->left, p->right);
}

static uint32_t hash_bvrem_hobj(bvop_hobj_t *p) {
  return hash_bvrem(p->left, p->right);
}

static uint32_t hash_bvsdiv_hobj(bvop_hobj_t *p) {
  return hash_bvsdiv(p->left, p->right);
}

static uint32_t hash_bvsrem_hobj(bvop_hobj_t *p) {
  return hash_bvsrem(p->left, p->right);
}

static uint32_t hash_bvsmod_hobj(bvop_hobj_t *p) {
  return hash_bvsmod(p->left, p->right);
}

static uint32_t hash_bvshl_hobj(bvop_hobj_t *p) {
  return hash_bvshl(p->left, p->right);
}

static uint32_t hash_bvlshr_hobj(bvop_hobj_t *p) {
  return hash_bvlshr(p->left, p->right);
}

static uint32_t hash_bvashr_hobj(bvop_hobj_t *p) {
  return hash_bvashr(p->left, p->right);
}

static uint32_t hash_bvadd_hobj(bvop_hobj_t *p) {
  return hash_bvadd(p->left, p->right);
}

static uint32_t hash_bvsub_hobj(bvop_hobj_t *p) {
  return hash_bvsub(p->left, p->right);
}

static uint32_t hash_bvmul_hobj(bvop_hobj_t *p) {
  return hash_bvmul(p->left, p->right);
}

static uint32_t hash_bvneg_hobj(bvop_hobj_t *p) {
  return hash_bvneg(p->left);
}



/*
 * Equality tests
 */
static bool eq_bvconst64_hobj(bvconst64_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_CONST64 &&
    table->bit_size[i] == p->nbits && table->def[i].val == p->val;
}

static bool eq_bvconst_hobj(bvconst_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;
  uint32_t w;

  table = p->tbl;
  if (bvvar_tag(table, i) != BVTAG_CONST || table->bit_size[i] != p->nbits) {
    return false;
 }
  w = (p->nbits + 31) >> 5;
  return bvconst_eq(p->val, table->def[i].ptr, w);
}

static bool eq_bvpoly64_hobj(bvpoly_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_POLY64 &&
    bvpoly_buffer_equal_poly64(p->buffer, table->def[i].ptr);
}

static bool eq_bvpoly_hobj(bvpoly_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_POLY &&
    bvpoly_buffer_equal_poly(p->buffer, table->def[i].ptr);
}


// helper function
static bool pp_buffer_eq_pprod(pp_buffer_t *buffer, pprod_t *p) {
  uint32_t n;

  n = buffer->len;
  return p->len == n && varexp_array_equal(buffer->prod, p->prod, n);
}

static bool eq_bvpprod_hobj(bvpprod_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_PPROD &&
    pp_buffer_eq_pprod(p->buffer, table->def[i].ptr);
}


static bool eq_bvarray_hobj(bvarray_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;
  literal_t *a;
  uint32_t j, n;

  table = p->tbl;
  n = p->nbits;
  if (bvvar_tag(table, i) != BVTAG_BIT_ARRAY || table->bit_size[i] != n) {
    return false;
  }

  a = table->def[i].ptr;
  for (j=0; j<n; j++) {
    if (a[j] != p->val[j]) return false;
  }

  return true;
}

static bool eq_bvite_hobj(bvite_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;
  bv_ite_t *d;

  table = p->tbl;
  if (bvvar_tag(table, i) == BVTAG_ITE) {
    d = table->def[i].ptr;
    return d->cond == p->cond && d->left == p->left && d->right == p->right;
  } else {
    return false;
  }
}

static bool eq_bvdiv_hobj(bvop_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_UDIV && table->def[i].op[0] == p->left &&
    table->def[i].op[1] == p->right;
}

static bool eq_bvrem_hobj(bvop_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_UREM && table->def[i].op[0] == p->left &&
    table->def[i].op[1] == p->right;
}

static bool eq_bvsdiv_hobj(bvop_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_SDIV && table->def[i].op[0] == p->left &&
    table->def[i].op[1] == p->right;
}

static bool eq_bvsrem_hobj(bvop_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_SREM && table->def[i].op[0] == p->left &&
    table->def[i].op[1] == p->right;
}

static bool eq_bvsmod_hobj(bvop_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_SMOD && table->def[i].op[0] == p->left &&
    table->def[i].op[1] == p->right;
}

static bool eq_bvshl_hobj(bvop_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_SHL && table->def[i].op[0] == p->left &&
    table->def[i].op[1] == p->right;
}

static bool eq_bvlshr_hobj(bvop_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_LSHR && table->def[i].op[0] == p->left &&
    table->def[i].op[1] == p->right;
}

static bool eq_bvashr_hobj(bvop_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_ASHR && table->def[i].op[0] == p->left &&
    table->def[i].op[1] == p->right;
}


static bool eq_bvadd_hobj(bvop_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_ADD && table->def[i].op[0] == p->left &&
    table->def[i].op[1] == p->right;
}

static bool eq_bvsub_hobj(bvop_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_SUB && table->def[i].op[0] == p->left &&
    table->def[i].op[1] == p->right;
}

static bool eq_bvmul_hobj(bvop_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_MUL && table->def[i].op[0] == p->left &&
    table->def[i].op[1] == p->right;
}

static bool eq_bvneg_hobj(bvop_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_NEG && table->def[i].op[0] == p->left;
}





/*
 * Build
 */
static thvar_t build_bvconst64_hobj(bvconst64_hobj_t *p) {
  return make_bvconst64(p->tbl, p->nbits, p->val);
}

static thvar_t build_bvconst_hobj(bvconst_hobj_t *p) {
  return make_bvconst(p->tbl, p->nbits, p->val);
}

static thvar_t build_bvpoly64_hobj(bvpoly_hobj_t *p) {
  return make_bvpoly64(p->tbl, p->buffer);
}

static thvar_t build_bvpoly_hobj(bvpoly_hobj_t *p) {
  return make_bvpoly(p->tbl, p->buffer);
}

static thvar_t build_bvpprod_hobj(bvpprod_hobj_t *p) {
  return make_bvpprod(p->tbl, p->nbits, p->buffer);
}

static thvar_t build_bvarray_hobj(bvarray_hobj_t *p) {
  return make_bvarray(p->tbl, p->nbits, p->val);
}

static thvar_t build_bvite_hobj(bvite_hobj_t *p) {
  return make_bvite(p->tbl, p->nbits, p->cond, p->left, p->right);
}

static thvar_t build_bvdiv_hobj(bvop_hobj_t *p) {
  return make_bvbinop(p->tbl, BVTAG_UDIV, p->nbits, p->left, p->right);
}

static thvar_t build_bvrem_hobj(bvop_hobj_t *p) {
  return make_bvbinop(p->tbl, BVTAG_UREM, p->nbits, p->left, p->right);
}

static thvar_t build_bvsdiv_hobj(bvop_hobj_t *p) {
  return make_bvbinop(p->tbl, BVTAG_SDIV, p->nbits, p->left, p->right);
}

static thvar_t build_bvsrem_hobj(bvop_hobj_t *p) {
  return make_bvbinop(p->tbl, BVTAG_SREM, p->nbits, p->left, p->right);
}

static thvar_t build_bvsmod_hobj(bvop_hobj_t *p) {
  return make_bvbinop(p->tbl, BVTAG_SMOD, p->nbits, p->left, p->right);
}

static thvar_t build_bvshl_hobj(bvop_hobj_t *p) {
  return make_bvbinop(p->tbl, BVTAG_SHL, p->nbits, p->left, p->right);
}

static thvar_t build_bvlshr_hobj(bvop_hobj_t *p) {
  return make_bvbinop(p->tbl, BVTAG_LSHR, p->nbits, p->left, p->right);
}

static thvar_t build_bvashr_hobj(bvop_hobj_t *p) {
  return make_bvbinop(p->tbl, BVTAG_ASHR, p->nbits, p->left, p->right);
}

static thvar_t build_bvadd_hobj(bvop_hobj_t *p) {
  return make_bvbinop(p->tbl, BVTAG_ADD, p->nbits, p->left, p->right);
}

static thvar_t build_bvsub_hobj(bvop_hobj_t *p) {
  return make_bvbinop(p->tbl, BVTAG_SUB, p->nbits, p->left, p->right);
}

static thvar_t build_bvmul_hobj(bvop_hobj_t *p) {
  return make_bvbinop(p->tbl, BVTAG_MUL, p->nbits, p->left, p->right);
}

static thvar_t build_bvneg_hobj(bvop_hobj_t *p) {
  return make_bvbinop(p->tbl, BVTAG_NEG, p->nbits, p->left, null_thvar);
}


/*
 * Hash objects
 */
static bvconst64_hobj_t bvconst64_hobj = {
  { (hobj_hash_t) hash_bvconst64_hobj, (hobj_eq_t) eq_bvconst64_hobj, (hobj_build_t) build_bvconst64_hobj },
  NULL,
  0, 0,
};

static bvconst_hobj_t bvconst_hobj = {
  { (hobj_hash_t) hash_bvconst_hobj, (hobj_eq_t) eq_bvconst_hobj, (hobj_build_t) build_bvconst_hobj },
  NULL,
  NULL, 0,
};

static bvpoly_hobj_t bvpoly64_hobj = {
  { (hobj_hash_t) hash_bvpoly64_hobj, (hobj_eq_t) eq_bvpoly64_hobj, (hobj_build_t) build_bvpoly64_hobj },
  NULL,
  NULL,
};

static bvpoly_hobj_t bvpoly_hobj = {
  { (hobj_hash_t) hash_bvpoly_hobj, (hobj_eq_t) eq_bvpoly_hobj, (hobj_build_t) build_bvpoly_hobj },
  NULL,
  NULL,
};

static bvpprod_hobj_t bvpprod_hobj = {
  { (hobj_hash_t) hash_bvpprod_hobj, (hobj_eq_t) eq_bvpprod_hobj, (hobj_build_t) build_bvpprod_hobj },
  NULL,
  NULL, 0,
};

static bvarray_hobj_t bvarray_hobj = {
  { (hobj_hash_t) hash_bvarray_hobj, (hobj_eq_t) eq_bvarray_hobj, (hobj_build_t) build_bvarray_hobj },
  NULL,
  NULL, 0.
};

static bvite_hobj_t bvite_hobj = {
  { (hobj_hash_t) hash_bvite_hobj, (hobj_eq_t) eq_bvite_hobj, (hobj_build_t) build_bvite_hobj },
  NULL,
  0, 0, 0, 0,
};

static bvop_hobj_t bvdiv_hobj = {
  { (hobj_hash_t) hash_bvdiv_hobj, (hobj_eq_t) eq_bvdiv_hobj, (hobj_build_t) build_bvdiv_hobj },
  NULL,
  0, 0, 0,
};

static bvop_hobj_t bvrem_hobj = {
  { (hobj_hash_t) hash_bvrem_hobj, (hobj_eq_t) eq_bvrem_hobj, (hobj_build_t) build_bvrem_hobj },
  NULL,
  0, 0, 0,
};

static bvop_hobj_t bvsdiv_hobj = {
  { (hobj_hash_t) hash_bvsdiv_hobj, (hobj_eq_t) eq_bvsdiv_hobj, (hobj_build_t) build_bvsdiv_hobj },
  NULL,
  0, 0, 0,
};

static bvop_hobj_t bvsrem_hobj = {
  { (hobj_hash_t) hash_bvsrem_hobj, (hobj_eq_t) eq_bvsrem_hobj, (hobj_build_t) build_bvsrem_hobj },
  NULL,
  0, 0, 0,
};

static bvop_hobj_t bvsmod_hobj = {
  { (hobj_hash_t) hash_bvsmod_hobj, (hobj_eq_t) eq_bvsmod_hobj, (hobj_build_t) build_bvsmod_hobj },
  NULL,
  0, 0, 0,
};

static bvop_hobj_t bvshl_hobj = {
  { (hobj_hash_t) hash_bvshl_hobj, (hobj_eq_t) eq_bvshl_hobj, (hobj_build_t) build_bvshl_hobj },
  NULL,
  0, 0, 0,
};

static bvop_hobj_t bvlshr_hobj = {
  { (hobj_hash_t) hash_bvlshr_hobj, (hobj_eq_t) eq_bvlshr_hobj, (hobj_build_t) build_bvlshr_hobj },
  NULL,
  0, 0, 0,
};

static bvop_hobj_t bvashr_hobj = {
  { (hobj_hash_t) hash_bvashr_hobj, (hobj_eq_t) eq_bvashr_hobj, (hobj_build_t) build_bvashr_hobj },
  NULL,
  0, 0, 0,
};


static bvop_hobj_t bvadd_hobj = {
  { (hobj_hash_t) hash_bvadd_hobj, (hobj_eq_t) eq_bvadd_hobj, (hobj_build_t) build_bvadd_hobj },
  NULL,
  0, 0, 0,
};


static bvop_hobj_t bvsub_hobj = {
  { (hobj_hash_t) hash_bvsub_hobj, (hobj_eq_t) eq_bvsub_hobj, (hobj_build_t) build_bvsub_hobj },
  NULL,
  0, 0, 0,
};


static bvop_hobj_t bvmul_hobj = {
  { (hobj_hash_t) hash_bvmul_hobj, (hobj_eq_t) eq_bvmul_hobj, (hobj_build_t) build_bvmul_hobj },
  NULL,
  0, 0, 0,
};


static bvop_hobj_t bvneg_hobj = {
  { (hobj_hash_t) hash_bvneg_hobj, (hobj_eq_t) eq_bvneg_hobj, (hobj_build_t) build_bvneg_hobj },
  NULL,
  0, 0, 0,
};



/*
 * Hash-consing constructors
 */
thvar_t get_bvconst64(bv_vartable_t *table, uint32_t n, uint64_t val) {
  bvconst64_hobj.tbl = table;
  bvconst64_hobj.val = val;
  bvconst64_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvconst64_hobj.m);
}

thvar_t get_bvconst(bv_vartable_t *table, uint32_t n, uint32_t *val) {
  bvconst_hobj.tbl = table;
  bvconst_hobj.val = val;
  bvconst_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvconst_hobj.m);
}

thvar_t get_bvpoly64(bv_vartable_t *table, bvpoly_buffer_t *buffer) {
  bvpoly64_hobj.tbl = table;
  bvpoly64_hobj.buffer = buffer;
  return int_htbl_get_obj(&table->htbl, &bvpoly64_hobj.m);
}

thvar_t get_bvpoly(bv_vartable_t *table, bvpoly_buffer_t *buffer) {
  bvpoly_hobj.tbl = table;
  bvpoly_hobj.buffer = buffer;
  return int_htbl_get_obj(&table->htbl, &bvpoly_hobj.m);
}

thvar_t get_bvpprod(bv_vartable_t *table, uint32_t n, pp_buffer_t *buffer) {
  bvpprod_hobj.tbl = table;
  bvpprod_hobj.buffer = buffer;
  bvpprod_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvpprod_hobj.m);
}

thvar_t get_bvarray(bv_vartable_t *table, uint32_t n, literal_t *a) {
  bvarray_hobj.tbl = table;
  bvarray_hobj.val = a;
  bvarray_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvarray_hobj.m);
}

thvar_t get_bvite(bv_vartable_t *table, uint32_t n, literal_t l, thvar_t x, thvar_t y) {
  bvite_hobj.tbl = table;
  bvite_hobj.cond = l;
  bvite_hobj.left = x;
  bvite_hobj.right = y;
  bvite_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvite_hobj.m);
}

thvar_t get_bvdiv(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvdiv_hobj.tbl = table;
  bvdiv_hobj.left = x;
  bvdiv_hobj.right = y;
  bvdiv_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvdiv_hobj.m);
}

thvar_t get_bvrem(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvrem_hobj.tbl = table;
  bvrem_hobj.left = x;
  bvrem_hobj.right = y;
  bvrem_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvrem_hobj.m);
}

thvar_t get_bvsdiv(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvsdiv_hobj.tbl = table;
  bvsdiv_hobj.left = x;
  bvsdiv_hobj.right = y;
  bvsdiv_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvsdiv_hobj.m);
}

thvar_t get_bvsrem(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvsrem_hobj.tbl = table;
  bvsrem_hobj.left = x;
  bvsrem_hobj.right = y;
  bvsrem_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvsrem_hobj.m);
}

thvar_t get_bvsmod(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvsmod_hobj.tbl = table;
  bvsmod_hobj.left = x;
  bvsmod_hobj.right = y;
  bvsmod_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvsmod_hobj.m);
}

thvar_t get_bvshl(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvshl_hobj.tbl = table;
  bvshl_hobj.left = x;
  bvshl_hobj.right = y;
  bvshl_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvshl_hobj.m);
}

thvar_t get_bvlshr(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvlshr_hobj.tbl = table;
  bvlshr_hobj.left = x;
  bvlshr_hobj.right = y;
  bvlshr_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvlshr_hobj.m);
}

thvar_t get_bvashr(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvashr_hobj.tbl = table;
  bvashr_hobj.left = x;
  bvashr_hobj.right = y;
  bvashr_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvashr_hobj.m);
}


thvar_t get_bvadd(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvadd_hobj.tbl = table;
  bvadd_hobj.left = x;
  bvadd_hobj.right = y;
  bvadd_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvadd_hobj.m);
}

thvar_t get_bvsub(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvsub_hobj.tbl = table;
  bvsub_hobj.left = x;
  bvsub_hobj.right = y;
  bvsub_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvsub_hobj.m);
}

thvar_t get_bvmul(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvmul_hobj.tbl = table;
  bvmul_hobj.left = x;
  bvmul_hobj.right = y;
  bvmul_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvmul_hobj.m);
}

thvar_t get_bvneg(bv_vartable_t *table, uint32_t n, thvar_t x) {
  bvneg_hobj.tbl = table;
  bvneg_hobj.left = x;
  bvneg_hobj.right = null_thvar;
  bvneg_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvneg_hobj.m);
}




/*
 * Search for (div x y), (rem x y), etc.
 * - return -1 if the term is not in the table
 */
thvar_t find_div(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
         table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  bvdiv_hobj.tbl = table;
  bvdiv_hobj.left = x;
  bvdiv_hobj.right = y;
  bvdiv_hobj.nbits = n;

  return int_htbl_find_obj(&table->htbl, &bvdiv_hobj.m);
}

thvar_t find_rem(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
         table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  bvrem_hobj.tbl = table;
  bvrem_hobj.left = x;
  bvrem_hobj.right = y;
  bvrem_hobj.nbits = n;

  return int_htbl_find_obj(&table->htbl, &bvrem_hobj.m);
}

thvar_t find_sdiv(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
         table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  bvsdiv_hobj.tbl = table;
  bvsdiv_hobj.left = x;
  bvsdiv_hobj.right = y;
  bvsdiv_hobj.nbits = n;

  return int_htbl_find_obj(&table->htbl, &bvsdiv_hobj.m);
}

thvar_t find_srem(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
         table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  bvsrem_hobj.tbl = table;
  bvsrem_hobj.left = x;
  bvsrem_hobj.right = y;
  bvsrem_hobj.nbits = n;

  return int_htbl_find_obj(&table->htbl, &bvsrem_hobj.m);
}


thvar_t find_bvadd(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
         table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  bvadd_hobj.tbl = table;
  bvadd_hobj.left = x;
  bvadd_hobj.right = y;
  bvadd_hobj.nbits = n;
  return int_htbl_find_obj(&table->htbl, &bvadd_hobj.m);
}

thvar_t find_bvsub(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
         table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  bvsub_hobj.tbl = table;
  bvsub_hobj.left = x;
  bvsub_hobj.right = y;
  bvsub_hobj.nbits = n;
  return int_htbl_find_obj(&table->htbl, &bvsub_hobj.m);
}

thvar_t find_bvmul(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
         table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  bvmul_hobj.tbl = table;
  bvmul_hobj.left = x;
  bvmul_hobj.right = y;
  bvmul_hobj.nbits = n;
  return int_htbl_find_obj(&table->htbl, &bvmul_hobj.m);
}

thvar_t find_bvneg(bv_vartable_t *table, thvar_t x) {
  uint32_t n;

  assert(valid_bvvar(table, x));

  n = table->bit_size[x];
  bvneg_hobj.tbl = table;
  bvneg_hobj.left = x;
  bvneg_hobj.right = null_thvar;
  bvneg_hobj.nbits = n;
  return int_htbl_find_obj(&table->htbl, &bvneg_hobj.m);
}



