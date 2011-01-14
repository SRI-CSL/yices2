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



/********************
 *  VARIABLE TABLE  *
 *******************/

/*
 * Initialize table
 * - use the default size
 * - the eterm array is not allocated here, but on the first
 *   call to attach_eterm
 */
static void init_bv_vartable(bv_vartable_t *table) {
  uint32_t n;

  n = DEF_BVVARTABLE_SIZE;
  assert(n < MAX_BVVARTABLE_SIZE);

  table->nvars = 0;
  table->size = n;
  table->bit_size = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  table->kind = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  table->def = (bvvar_desc_t *) safe_malloc(n * sizeof(bvvar_desc_t));
  table->eterm = NULL;
  table->map = (literal_t **) safe_malloc(n * sizeof(literal_t *));

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
static void delete_bv_vartable(bv_vartable_t *table) {
  uint32_t i, n;

  n = table->nvars;
  for (i=0; i<n; i++) {
    safe_free(table->map[i]);
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
static void reset_bv_vartable(bv_vartable_t *table) {
  uint32_t i, n;

  n = table->nvars;
  for (i=0; i<n; i++) {
    safe_free(table->map[i]);
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

  table->nvars = 0;

  reset_int_htbl(&table->htbl);  
}


/*
 * Attach egraph term t to variable x
 * - x must be not have an eterm attached already
 */
static void attach_eterm_to_bvvar(bv_vartable_t *table, thvar_t x, eterm_t t) {
  eterm_t *tmp;
  uint32_t i, n;

  assert(0 <= x && x < table->nvars && t != null_eterm);

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
 * Check whether x has an eterm attached
 */
static inline bool bvvar_has_eterm(bv_vartable_t *table, thvar_t x) {
  assert(0 <= x && x < table->nvars);
  return table->eterm != NULL && table->eterm[x] != null_eterm;
}


/*
 * Get the eterm attached to x or null_eterm 
 */
static inline eterm_t bvvar_get_eterm(bv_vartable_t *table, thvar_t x) {
  eterm_t t;

  assert(0 <= x && x < table->nvars);
  t = null_eterm;
  if (table->eterm != NULL) {
    t = table->eterm[x];
  }
  return t;
}



/*
 * Remove all eterms of id >= nterms
 */
static void bv_vartable_remove_eterms(bv_vartable_t *table, uint32_t nterms) {
  eterm_t *tmp;
  uint32_t i, n;
  eterm_t t;

  tmp = table->eterm;

  if (tmp != NULL) {
    n = table->nvars;
    for (i=0; i<n; i++) {
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
  a = jenkins_hash_int64((int64_t) c);
  b = jenkins_hash_int32((int32_t) n);
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



/*
 * Remove all variables of index >= nv
 */
static void bv_vartable_remove_vars(bv_vartable_t *table, uint32_t nv) {
  uint32_t i, n, h;

  assert(nv <= table->nvars);

  h = 0; // stop GCC warning

  n = table->nvars;
  for (i=nv; i<n; i++) {
    switch (bvvar_tag(table, i)) {
    case BVTAG_VAR:
      // no hash consing, no descriptor
      safe_free(table->map[i]);
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
      h = hash_bvarray(table->map[i], table->bit_size[i]);
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
    }

    int_htbl_erase_record(&table->htbl, h, i);
    safe_free(table->map[i]);
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
static thvar_t make_bvvar(bv_vartable_t *table, uint32_t n) {
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

static thvar_t make_bvdiv(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t z;

  z = bv_vartable_alloc_id(table, n);
  table->kind[z] = BVTAG_UDIV;
  table->def[z].op[0] = x;
  table->def[z].op[1] = y;

  return x;
} 

static thvar_t make_bvrem(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t z;

  z = bv_vartable_alloc_id(table, n);
  table->kind[z] = BVTAG_UREM;
  table->def[z].op[0] = x;
  table->def[z].op[1] = y;

  return x;
} 

static thvar_t make_bvsdiv(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t z;

  z = bv_vartable_alloc_id(table, n);
  table->kind[z] = BVTAG_SDIV;
  table->def[z].op[0] = x;
  table->def[z].op[1] = y;

  return x;
} 

static thvar_t make_bvsrem(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t z;

  z = bv_vartable_alloc_id(table, n);
  table->kind[z] = BVTAG_SREM;
  table->def[z].op[0] = x;
  table->def[z].op[1] = y;

  return x;
} 

static thvar_t make_bvsmod(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t z;

  z = bv_vartable_alloc_id(table, n);
  table->kind[z] = BVTAG_SMOD;
  table->def[z].op[0] = x;
  table->def[z].op[1] = y;

  return x;
} 

static thvar_t make_bvshl(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t z;

  z = bv_vartable_alloc_id(table, n);
  table->kind[z] = BVTAG_SHL;
  table->def[z].op[0] = x;
  table->def[z].op[1] = y;

  return x;
} 

static thvar_t make_bvlshr(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t z;

  z = bv_vartable_alloc_id(table, n);
  table->kind[z] = BVTAG_LSHR;
  table->def[z].op[0] = x;
  table->def[z].op[1] = y;

  return x;
} 

static thvar_t make_bvashr(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  thvar_t z;

  z = bv_vartable_alloc_id(table, n);
  table->kind[z] = BVTAG_ASHR;
  table->def[z].op[0] = x;
  table->def[z].op[1] = y;

  return x;
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
  return make_bvdiv(p->tbl, p->nbits, p->left, p->right);
}

static thvar_t build_bvrem_hobj(bvop_hobj_t *p) {
  return make_bvrem(p->tbl, p->nbits, p->left, p->right);
}

static thvar_t build_bvsdiv_hobj(bvop_hobj_t *p) {
  return make_bvsdiv(p->tbl, p->nbits, p->left, p->right);
}

static thvar_t build_bvsrem_hobj(bvop_hobj_t *p) {
  return make_bvsrem(p->tbl, p->nbits, p->left, p->right);
}

static thvar_t build_bvsmod_hobj(bvop_hobj_t *p) {
  return make_bvsmod(p->tbl, p->nbits, p->left, p->right);
}

static thvar_t build_bvshl_hobj(bvop_hobj_t *p) {
  return make_bvshl(p->tbl, p->nbits, p->left, p->right);
}

static thvar_t build_bvlshr_hobj(bvop_hobj_t *p) {
  return make_bvlshr(p->tbl, p->nbits, p->left, p->right);
}

static thvar_t build_bvashr_hobj(bvop_hobj_t *p) {
  return make_bvashr(p->tbl, p->nbits, p->left, p->right);
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


/*
 * Hash-consing constructors
 */
static thvar_t get_bvconst64(bv_vartable_t *table, uint32_t n, uint64_t val) {
  bvconst64_hobj.tbl = table;
  bvconst64_hobj.val = val;
  bvconst64_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvconst64_hobj.m);
}

static thvar_t get_bvconst(bv_vartable_t *table, uint32_t n, uint32_t *val) {
  bvconst_hobj.tbl = table;
  bvconst_hobj.val = val;
  bvconst_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvconst_hobj.m);
}

static thvar_t get_bvpoly64(bv_vartable_t *table, bvpoly_buffer_t *buffer) {
  bvpoly64_hobj.tbl = table;
  bvpoly64_hobj.buffer = buffer;
  return int_htbl_get_obj(&table->htbl, &bvpoly64_hobj.m);
}

static thvar_t get_bvpoly(bv_vartable_t *table, bvpoly_buffer_t *buffer) {
  bvpoly_hobj.tbl = table;
  bvpoly_hobj.buffer = buffer;
  return int_htbl_get_obj(&table->htbl, &bvpoly_hobj.m);
}

static thvar_t get_bvpprod(bv_vartable_t *table, uint32_t n, pp_buffer_t *buffer) {
  bvpprod_hobj.tbl = table;
  bvpprod_hobj.buffer = buffer;
  bvpprod_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvpprod_hobj.m);
}

static thvar_t get_bvarray(bv_vartable_t *table, uint32_t n, literal_t *a) {
  bvarray_hobj.tbl = table;
  bvarray_hobj.val = a;
  bvarray_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvarray_hobj.m);
}

static thvar_t get_bvite(bv_vartable_t *table, uint32_t n, literal_t l, thvar_t x, thvar_t y) {
  bvite_hobj.tbl = table;
  bvite_hobj.cond = l;
  bvite_hobj.left = x;
  bvite_hobj.right = y;
  bvite_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvite_hobj.m);
}

static thvar_t get_bvdiv(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvdiv_hobj.tbl = table;
  bvdiv_hobj.left = x;
  bvdiv_hobj.right = y;
  bvdiv_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvdiv_hobj.m);
}

static thvar_t get_bvrem(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvrem_hobj.tbl = table;
  bvrem_hobj.left = x;
  bvrem_hobj.right = y;
  bvrem_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvrem_hobj.m);
}

static thvar_t get_bvsdiv(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvsdiv_hobj.tbl = table;
  bvsdiv_hobj.left = x;
  bvsdiv_hobj.right = y;
  bvsdiv_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvsdiv_hobj.m);
}

static thvar_t get_bvsrem(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvsrem_hobj.tbl = table;
  bvsrem_hobj.left = x;
  bvsrem_hobj.right = y;
  bvsrem_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvsrem_hobj.m);
}

static thvar_t get_bvsmod(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvsmod_hobj.tbl = table;
  bvsmod_hobj.left = x;
  bvsmod_hobj.right = y;
  bvsmod_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvsmod_hobj.m);
}

static thvar_t get_bvshl(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvshl_hobj.tbl = table;
  bvshl_hobj.left = x;
  bvshl_hobj.right = y;
  bvshl_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvshl_hobj.m);
}

static thvar_t get_bvlshr(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvlshr_hobj.tbl = table;
  bvlshr_hobj.left = x;
  bvlshr_hobj.right = y;
  bvlshr_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvlshr_hobj.m);
}

static thvar_t get_bvashr(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y) {
  bvashr_hobj.tbl = table;
  bvashr_hobj.left = x;
  bvashr_hobj.right = y;
  bvashr_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, &bvashr_hobj.m);
}



#if 0

// NOT USED YET

/*
 * Search for (div x y), (rem x y), etc.
 * - return -1 if the term is not in the table
 */
static thvar_t find_div(bv_vartable_t *table, thvar_t x, thvar_t y) {
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

static thvar_t find_rem(bv_vartable_t *table, thvar_t x, thvar_t y) {
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

static thvar_t find_sdiv(bv_vartable_t *table, thvar_t x, thvar_t y) {
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

static thvar_t find_srem(bv_vartable_t *table, thvar_t x, thvar_t y) {
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


#endif


/****************
 *  ATOM TABLE  *
 ***************/

/*
 * Initialization
 * - use the default size
 * - the table is initially empty
 */
static void init_bv_atomtable(bv_atomtable_t *table) {
  uint32_t n;

  n = DEF_BVATOMTABLE_SIZE;
  assert(n < MAX_BVATOMTABLE_SIZE);

  table->natoms = 0;
  table->size = n;
  table->data = (bvatm_t *) safe_malloc(n * sizeof(bvatm_t));

  init_int_htbl(&table->htbl, 0); // use default size
}


/*
 * Make the table 50% larger
 */
static void extend_bv_atomtable(bv_atomtable_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;

  if (n >= MAX_BVATOMTABLE_SIZE) {
    out_of_memory();
  }

  table->data = (bvatm_t *) safe_realloc(table->data, n * sizeof(bvatm_t));
  table->size = n;
}


/*
 * Delete the table
 */
static void delete_bv_atomtable(bv_atomtable_t *table) {
  safe_free(table->data);
  table->data = NULL;

  delete_int_htbl(&table->htbl);
}


/*
 * Empty the table
 */
static void reset_bv_atomtable(bv_atomtable_t *table) {
  table->natoms = 0;
  reset_int_htbl(&table->htbl);
}


/*
 * Hash code of atom (op x y)
 */
static inline uint32_t hash_bvatm(bvatm_tag_t op, thvar_t x, thvar_t y) {
  return jenkins_hash_triple(op, x, y, 0xab3a23fe);
}


/*
 * Remove all atoms of index >= na
 */
static void bv_atomtable_remove_atoms(bv_atomtable_t *table, uint32_t na) {
  bvatm_t *a;
  uint32_t i, n, h;

  assert(na <= table->natoms);

  n = table->natoms;
  a = table->data;
  for (i=na; i<n; i++) {
    h = hash_bvatm(bvatm_tag(a + i), a[i].left, a[i].right);
    int_htbl_erase_record(&table->htbl, h, i);
  }
  table->natoms = na;
}


/*
 * Create a new atom (op x y)
 * - return its index
 * - lit is null_literal
 * - the atom is unmarked
 */
static int32_t make_atom(bv_atomtable_t *table, bvatm_tag_t op, thvar_t x, thvar_t y) {
  uint32_t i;

  i = table->natoms;
  if (i == table->size) {
    extend_bv_atomtable(table);
  }
  assert(i < table->size);
  table->data[i].header = op;
  table->data[i].lit = null_literal;
  table->data[i].left = x;
  table->data[i].right = y;

  table->natoms = i+1;

  return i;
}

/*
 * Hash consing
 */
typedef struct bvatm_hobj_s {
  int_hobj_t m;
  bv_atomtable_t *tbl;
  bvatm_tag_t op;
  thvar_t left;
  thvar_t right;
} bvatm_hobj_t;


static uint32_t hash_bvatm_hobj(bvatm_hobj_t *p) {
  return hash_bvatm(p->op, p->left, p->right);
}

static bool eq_bvatm_hobj(bvatm_hobj_t *p, int32_t i) {
  bv_atomtable_t *table;

  table = p->tbl;
  return bvatm_tag(table->data + i) == p->op && table->data[i].left == p->left 
    && table->data[i].right == p->right;
}

static int32_t build_bvatm_hobj(bvatm_hobj_t *p) {
  bv_atomtable_t *table;

  table = p->tbl;
  return make_atom(table, p->op, p->left, p->right);
}


static bvatm_hobj_t bvatm_hobj = {
  { (hobj_hash_t) hash_bvatm_hobj, (hobj_eq_t) eq_bvatm_hobj, (hobj_build_t) build_bvatm_hobj },
  NULL,
  0, 0, 0,
};


static int32_t get_bv_atom(bv_atomtable_t *table, bvatm_tag_t op, thvar_t x, thvar_t y) {
  bvatm_hobj.tbl = table;
  bvatm_hobj.op = op;
  bvatm_hobj.left = x;
  bvatm_hobj.right = y;
  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &bvatm_hobj);
}


/*
 * Normalize + hash consing
 */
static int32_t get_bveq_atom(bv_atomtable_t *table, thvar_t x, thvar_t y) {
  thvar_t aux;

  if (x > y) {
    aux = x; x = y; y = aux;
  }
  return get_bv_atom(table, BVEQ_ATM, x, y);
}

static inline int32_t get_bvuge_atom(bv_atomtable_t *table, thvar_t x, thvar_t y) {
  return get_bv_atom(table, BVUGE_ATM, x, y);
}

static inline int32_t get_bvsge_atom(bv_atomtable_t *table, thvar_t x, thvar_t y) {
  return get_bv_atom(table, BVSGE_ATM, x, y);
}



#if 0 

// NOT USED YET

/*
 * Search for an atom
 * - return the atom id if it exists
 * - return -1 otherwise
 */
static int32_t find_bv_atom(bv_atomtable_t *table, bvatm_tag_t op, thvar_t x, thvar_t y) {
  bvatm_hobj.tbl = table;
  bvatm_hobj.op = op;
  bvatm_hobj.left = x;
  bvatm_hobj.right = y;
  return int_htbl_find_obj(&table->htbl, (int_hobj_t *) &bvatm_hobj);
}

static int32_t find_bveq_atom(bv_atomtable_t *table, thvar_t x, thvar_t y) {
  thvar_t aux;

  if (x > y) {
    aux = x; x = y; y = aux;
  }
  return find_bv_atom(table, BVEQ_ATM, x, y);
}

static inline int32_t find_bvuge_atom(bv_atomtable_t *table, thvar_t x, thvar_t y) {
  return find_bv_atom(table, BVUGE_ATM, x, y);
}

static inline int32_t find_bvsge_atom(bv_atomtable_t *table, thvar_t x, thvar_t y) {
  return find_bv_atom(table, BVSGE_ATM, x, y);
}

#endif


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
 */
static void bv_trail_save(bv_trail_stack_t *stack, uint32_t nv, uint32_t na) {
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








/*****************************************
 *  SIMPLIFICATION + TERM CONSTRUCTION   *
 ****************************************/

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
 * - nbits = number of bits in c and x (nbist > 64)
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
  uint32_t na, nv;

  assert(solver->decision_level == solver->base_level);

  nv = solver->vtbl.nvars;
  na = solver->atbl.natoms;
  bv_trail_save(&solver->trail_stack, nv, na);

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
 *   then map containts n+1 elements variables, and map[i] is the internalization of t_i
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
    bvpoly_buffer_add_monomial(buffer, map[i], p->mono[i].coeff);
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
    bvpoly_buffer_add_mono64(buffer, map[i], p->mono[i].coeff);
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
   * We build a term constant * (x_1 ^ d_1 ... x_k^d_k)
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
 * TODO: check for simplifications
 */
thvar_t bv_solver_create_bvdiv(bv_solver_t *solver, thvar_t x, thvar_t y) {
  uint32_t n;

  n = bvvar_bitsize(&solver->vtbl, x);
  assert(bvvar_bitsize(&solver->vtbl, y) == n);

  return get_bvdiv(&solver->vtbl, n, x, y);
}

thvar_t bv_solver_create_bvrem(bv_solver_t *solver, thvar_t x, thvar_t y) {
  uint32_t n;

  n = bvvar_bitsize(&solver->vtbl, x);
  assert(bvvar_bitsize(&solver->vtbl, y) == n);

  return get_bvrem(&solver->vtbl, n, x, y);
}

thvar_t bv_solver_create_bvsdiv(bv_solver_t *solver, thvar_t x, thvar_t y) {
  uint32_t n;

  n = bvvar_bitsize(&solver->vtbl, x);
  assert(bvvar_bitsize(&solver->vtbl, y) == n);

  return get_bvsdiv(&solver->vtbl, n, x, y);
}

thvar_t bv_solver_create_bvsrem(bv_solver_t *solver, thvar_t x, thvar_t y) {
  uint32_t n;

  n = bvvar_bitsize(&solver->vtbl, x);
  assert(bvvar_bitsize(&solver->vtbl, y) == n);

  return get_bvsrem(&solver->vtbl, n, x, y);
}

thvar_t bv_solver_create_bvsmod(bv_solver_t *solver, thvar_t x, thvar_t y) {
  uint32_t n;

  n = bvvar_bitsize(&solver->vtbl, x);
  assert(bvvar_bitsize(&solver->vtbl, y) == n);

  return get_bvsmod(&solver->vtbl, n, x, y);
}


thvar_t bv_solver_create_bvshl(bv_solver_t *solver, thvar_t x, thvar_t y) {
  uint32_t n;

  n = bvvar_bitsize(&solver->vtbl, x);
  assert(bvvar_bitsize(&solver->vtbl, y) == n);

  return get_bvshl(&solver->vtbl, n, x, y);
}

thvar_t bv_solver_create_bvlshr(bv_solver_t *solver, thvar_t x, thvar_t y) {
  uint32_t n;

  n = bvvar_bitsize(&solver->vtbl, x);
  assert(bvvar_bitsize(&solver->vtbl, y) == n);

  return get_bvlshr(&solver->vtbl, n, x, y);
}

thvar_t bv_solver_create_bvashr(bv_solver_t *solver, thvar_t x, thvar_t y) {
  uint32_t n;

  n = bvvar_bitsize(&solver->vtbl, x);
  assert(bvvar_bitsize(&solver->vtbl, y) == n);

  return get_bvashr(&solver->vtbl, n, x, y);
}


/*
 * Return the i-th bit of theory variable x as a literal
 */
literal_t bv_solver_select_bit(bv_solver_t *solver, thvar_t x, uint32_t i) {
  bv_vartable_t *vtbl;
  literal_t l;

  assert(valid_bvvar(&solver->vtbl, x) && i < bvvar_bitsize(&solver->vtbl, x));

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
  uint32_t n;
  int32_t i;
  literal_t l;
  bvar_t v;
  
  atbl = &solver->atbl;
  n = atbl->natoms;
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
 * Atom (bvge x y) (unsigned comparison)
 */
literal_t bv_solver_create_ge_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_atomtable_t *atbl;
  uint32_t n;
  int32_t i;
  literal_t l;
  bvar_t v;
  
  atbl = &solver->atbl;
  n = atbl->natoms;
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
 * Atom (bvsge x y) (signed comparison)
 */
literal_t bv_solver_create_sge_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_atomtable_t *atbl;
  uint32_t n;
  int32_t i;
  literal_t l;
  bvar_t v;
  
  atbl = &solver->atbl;
  n = atbl->natoms;
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
 * ATOM ASSERTIONS
 */

/*
 * Assert (x == y) if tt is true
 * assert (x != y) if tt is false
 */
void bv_solver_assert_eq_axiom(bv_solver_t *solver, thvar_t x, thvar_t y, bool tt) {
  literal_t l;

  l = bv_solver_create_eq_atom(solver, x, y);
  add_unit_clause(solver->core, signed_literal(l, tt));
}


/*
 * Assert (bvge x y) if tt is true
 * Assert (not (bvge x y)) if tt is false
 */
void bv_solver_assert_ge_axiom(bv_solver_t *solver, thvar_t x, thvar_t y, bool tt) {
  literal_t l;

  l = bv_solver_create_ge_atom(solver, x, y);
  add_unit_clause(solver->core, signed_literal(l, tt));
}


/*
 * Assert (bvsge x y) if tt is true
 * Assert (not (bvsge x y)) if tt is false
 */
void bv_solver_assert_sge_axiom(bv_solver_t *solver, thvar_t x, thvar_t y, bool tt) {
  literal_t l;

  l = bv_solver_create_sge_atom(solver, x, y);
  add_unit_clause(solver->core, signed_literal(l, tt));
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






