/*
 * BIT-VECTOR SOLVER (BASELINE)
 */

#include <assert.h>

#include "memalloc.h"
#include "bv_constants.h"
#include "hash_functions.h"
#include "int_powers.h"
#include "int_partitions.h"
// #include "int_hash_classes.h"

#include "bvsolver.h"

#define TRACE 0
#define DUMP  0

#if TRACE || DUMP || 1

#include <stdio.h>
#include <inttypes.h>

#include "cputime.h"
#include "solver_printer.h"

#endif


#if DUMP

static void bv_solver_dump_state(bv_solver_t *solver, char *filename);

#endif


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
  table->map = (bvvar_map_t *) safe_malloc(n * sizeof(bvvar_map_t));

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
  table->map = (bvvar_map_t *) safe_realloc(table->map, n * sizeof(bvvar_map_t));

  table->size = n;
}


/*
 * Delete the table
 */
static void delete_bv_vartable(bv_vartable_t *table) {
  uint32_t i, n;

  n = table->nvars;
  for (i=0; i<n; i++) {
    if (table->bit_size[i] >= 2) {
      safe_free(table->map[i].array);
    }
    switch (bvvar_tag(table, i)) {
    case BVTAG_BIG_CONST:
      safe_free(table->def[i].pval);
      break;
    case BVTAG_BIT_ARRAY:
      safe_free(table->def[i].bit);
      break;
    case BVTAG_ITE:
      safe_free(table->def[i].ite);
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
    if (table->bit_size[i] >= 2) {
      safe_free(table->map[i].array);
    }
    switch (bvvar_tag(table, i)) {
    case BVTAG_BIG_CONST:
      safe_free(table->def[i].pval);
      break;
    case BVTAG_BIT_ARRAY:
      safe_free(table->def[i].bit);
      break;
    case BVTAG_ITE:
      safe_free(table->def[i].ite);
      break;
    default:
      break;
    }    
  }

  table->nvars = 0;

  reset_int_htbl(&table->htbl);  
}




/*
 * Hash codes
 */
// n = number of bits
static inline uint32_t hash_small_const(uint64_t c, uint32_t n) {
  uint32_t a, b;
  a = jenkins_hash_int64((int64_t) c);
  b = jenkins_hash_int32((int32_t) n);
  return jenkins_hash_mix2(a, b);
}

static inline uint32_t hash_big_const(uint32_t *c, uint32_t n) {
  return bvconst_hash(c, n);
}

static inline uint32_t hash_select(uint32_t i, thvar_t x) {
  return jenkins_hash_pair(i, x, 0x328a63e0);
}

static inline uint32_t hash_bitop(bvvar_tag_t op, bit_t x, bit_t y) {
  return jenkins_hash_triple(op, x, y, 0x43896432);
}

static inline uint32_t hash_bit(bit_t b) {
  return jenkins_hash_int32(b);
}

static inline uint32_t hash_bit_array(bit_t *b, uint32_t n) {
  return jenkins_hash_intarray_var(n, b, 0xaed32b8);
}

static inline uint32_t hash_bvop(bvvar_tag_t op, thvar_t x, thvar_t y) {
  return jenkins_hash_triple(op, x, y, 0x328fae23);
}

static inline uint32_t hash_bvite(literal_t c, thvar_t x, thvar_t y) {
  return jenkins_hash_triple(c, x, y, 0xfe2efd45);
}


/*
 * Remove all variables of index >= nv
 */
static void bv_vartable_remove_vars(bv_vartable_t *table, uint32_t nv) {
  bvvar_tag_t tag;
  uint32_t i, n, h;

  assert(nv <= table->nvars);

  h = 0; // stop GCC warning

  n = table->nvars;
  for (i=nv; i<n; i++) {
    tag = bvvar_tag(table, i);
    switch (tag) {
    case BVTAG_VAR:  // no hash consing for variables
      continue; 
    case BVTAG_SMALL_CONST:
      h = hash_small_const(table->def[i].ival, table->bit_size[i]);
      break;
    case BVTAG_BIG_CONST:
      h = hash_big_const(table->def[i].pval, table->bit_size[i]);
      safe_free(table->def[i].pval);
      break;
    case BVTAG_TRUE: // should not happen
      assert(false);
      continue;
    case BVTAG_SELECT:
      h = hash_select(table->def[i].sel.idx, table->def[i].sel.var);
      break;
    case BVTAG_XOR:
    case BVTAG_OR:
      h = hash_bitop(tag, table->def[i].bop[0], table->def[i].bop[1]);
      break;
    case BVTAG_BIT:
      h = hash_bit(table->def[i].bval);
      break;
    case BVTAG_BIT_ARRAY:
      h = hash_bit_array(table->def[i].bit, table->bit_size[i]);
      safe_free(table->def[i].bit);
      break;
    case BVTAG_ADD:
    case BVTAG_SUB:
    case BVTAG_NEG:
    case BVTAG_MUL:
    case BVTAG_UDIV:
    case BVTAG_UREM:
    case BVTAG_SDIV:
    case BVTAG_SREM:
    case BVTAG_SMOD:
    case BVTAG_SHL:
    case BVTAG_LSHR:
    case BVTAG_ASHR:
      h = hash_bvop(tag, table->def[i].op[0], table->def[i].op[1]);
      break;
    case BVTAG_ITE:
      h = hash_bvite(table->def[i].ite->cond, table->def[i].ite->left, table->def[i].ite->right);
      safe_free(table->def[i].ite);
      break;
    }
    int_htbl_erase_record(&table->htbl, h, i);
  }

  table->nvars = nv;
}



/*
 * Allocate a new variable id of n bits
 * - the descriptors are partially initialized:
 *   bit_size = n
 *   eterm = null_eterm if table->eterm exists
 *   bits = NULL
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
  if (n >= 2) {
    table->map[x].array = NULL;
  } else {
    table->map[x].lit = null_literal;
  }
  if (table->eterm != NULL) {
    table->eterm[x] = null_eterm;
  }

  table->nvars = x + 1;

  return x;
}



/*
 * Constructors
 */
static inline thvar_t make_var(bv_vartable_t *table, uint32_t n) {
  thvar_t x;

  x = bv_vartable_alloc_id(table, n);
  table->kind[x] = BVTAG_VAR;

  return x;
}

static inline thvar_t make_small_const(bv_vartable_t *table, uint32_t n, uint64_t val) {
  thvar_t x;  

  x = bv_vartable_alloc_id(table, n);
  table->kind[x] = BVTAG_SMALL_CONST;
  table->def[x].ival = val;

  return x;
}

static inline thvar_t make_big_const(bv_vartable_t *table, uint32_t n, uint32_t *val) {
  uint32_t *tmp;
  thvar_t x;
  uint32_t w;

  // make a copy of val
  w = (n + 31) >> 5;
  tmp = (uint32_t *) safe_malloc(w * sizeof(uint32_t));
  bvconst_set(tmp, w, val);
  bvconst_normalize(tmp, n);
 
  x = bv_vartable_alloc_id(table, n);
  table->kind[x] = BVTAG_BIG_CONST;
  table->def[x].pval = tmp;

  return x;
}

static inline thvar_t make_bit_true(bv_vartable_t *table) {
  thvar_t x;

  x = bv_vartable_alloc_id(table, 0);
  table->kind[x] = BVTAG_TRUE;

  return x;
}

static inline thvar_t make_select(bv_vartable_t *table, uint32_t i, thvar_t v) {
  thvar_t x;

  x = bv_vartable_alloc_id(table, 0);
  table->kind[x] = BVTAG_SELECT;
  table->def[x].sel.idx = i;
  table->def[x].sel.var = v;

  return x;
}


static inline thvar_t make_bitop(bv_vartable_t *table, bvvar_tag_t op, bit_t left, bit_t right) {
  thvar_t x;

  assert(op == BVTAG_XOR || op == BVTAG_OR);

  x = bv_vartable_alloc_id(table, 0);
  table->kind[x] = op;
  table->def[x].bop[0] = left;
  table->def[x].bop[1] = right;

  return x;
}

static inline thvar_t make_bit(bv_vartable_t *table, bit_t b) {
  thvar_t x;

  x = bv_vartable_alloc_id(table, 1);
  table->kind[x] = BVTAG_BIT;
  table->def[x].bval = b;

  return x;
}

static inline thvar_t make_bitarray(bv_vartable_t *table, uint32_t n, bit_t *a) {
  bit_t *b;
  uint32_t i;
  thvar_t x;

  // make a copy of a
  b = (bit_t *) safe_malloc(n * sizeof(bit_t));
  for (i=0; i<n; i++) {
    b[i] = a[i];
  }

  x = bv_vartable_alloc_id(table, n);
  table->kind[x] = BVTAG_BIT_ARRAY;
  table->def[x].bit = b;

  return x;
}

static inline thvar_t make_binop(bv_vartable_t *table, uint32_t n, bvvar_tag_t op, thvar_t left, thvar_t right) {
  thvar_t x;

  assert(BVTAG_ADD <= op && op <= BVTAG_ASHR);

  x = bv_vartable_alloc_id(table, n);
  table->kind[x] = op;
  table->def[x].op[0] = left;
  table->def[x].op[1] = right;

  return x;
}


static inline thvar_t make_bvite(bv_vartable_t *table, uint32_t n, literal_t c, thvar_t left, thvar_t right) {
  bv_ite_t *b;
  thvar_t x;

  b = (bv_ite_t *) safe_malloc(sizeof(bv_ite_t));
  b->cond = c;
  b->left = left;
  b->right = right;

  x = bv_vartable_alloc_id(table, n);
  table->kind[x] = BVTAG_ITE;
  table->def[x].ite = b;

  return x;
}





/*
 * HASH CONSING
 */
typedef struct small_const_hobj_s {
  int_hobj_t m;
  bv_vartable_t *tbl;
  uint64_t val;
  uint32_t nbits;
} small_const_hobj_t;

typedef struct big_const_hobj_s {
  int_hobj_t m;
  bv_vartable_t *tbl;
  uint32_t *val;
  uint32_t nbits;
} big_const_hobj_t;

typedef struct select_hobj_s {
  int_hobj_t m;
  bv_vartable_t *tbl;
  uint32_t idx;
  thvar_t var;
} select_hobj_t;

typedef struct bitop_hobj_s {
  int_hobj_t m;
  bv_vartable_t *tbl;
  bvvar_tag_t op;
  bit_t left;
  bit_t right;
} bitop_hobj_t;

typedef struct bit_hobj_s {
  int_hobj_t m;
  bv_vartable_t *tbl;
  bit_t val;
} bit_hobj_t;

typedef struct bit_array_hobj_s {
  int_hobj_t m;
  bv_vartable_t *tbl;
  bit_t *val;
  uint32_t nbits;
} bit_array_hobj_t;

typedef struct binop_hobj_s {
  int_hobj_t m;
  bv_vartable_t *tbl;
  bvvar_tag_t op;
  thvar_t left;
  thvar_t right;
  uint32_t nbits;
} binop_hobj_t;

typedef struct bvite_hobj_s {
  int_hobj_t m;
  bv_vartable_t *tbl;
  literal_t cond;
  bit_t left;
  bit_t right;
  uint32_t nbits;
} bvite_hobj_t;


/*
 * Hash functions
 */
static uint32_t hash_small_const_hobj(small_const_hobj_t *p) {
  return hash_small_const(p->val, p->nbits);
}

static uint32_t hash_big_const_hobj(big_const_hobj_t *p) {
  return hash_big_const(p->val, p->nbits);
}

static uint32_t hash_select_hobj(select_hobj_t *p) {
  return hash_select(p->idx, p->var);
}

static uint32_t hash_bitop_hobj(bitop_hobj_t *p) {
  return hash_bitop(p->op, p->left, p->right);
}

static uint32_t hash_bit_hobj(bit_hobj_t *p) {
  return hash_bit(p->val);
}

static uint32_t hash_bit_array_hobj(bit_array_hobj_t *p) {
  return hash_bit_array(p->val, p->nbits);
}

static uint32_t hash_binop_hobj(binop_hobj_t *p) {
  return hash_bvop(p->op, p->left, p->right);
}

static uint32_t hash_bvite_hobj(bvite_hobj_t *p) {
  return hash_bvite(p->cond, p->left, p->right);
}


/*
 * Equality tests
 */
static bool eq_small_const_hobj(small_const_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_SMALL_CONST && 
    table->bit_size[i] == p->nbits && table->def[i].ival == p->val;
}

static bool eq_big_const_hobj(big_const_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;
  uint32_t w;

  table = p->tbl;
  if (bvvar_tag(table, i) != BVTAG_BIG_CONST || table->bit_size[i] != p->nbits) {
    return false;
 }
  w = (p->nbits + 31) >> 5;
  return bvconst_eq(p->val, table->def[i].pval, w);
}

static bool eq_select_hobj(select_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_SELECT && table->def[i].sel.idx == p->idx &&
    table->def[i].sel.var == p->var;
}

static bool eq_bitop_hobj(bitop_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == p->op && table->def[i].bop[0] == p->left &&
    table->def[i].bop[1] == p->right;
}

static bool eq_bit_hobj(bit_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == BVTAG_BIT && table->def[i].bval == p->val;
}

static bool eq_bit_array_hobj(bit_array_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;
  bit_t *a;
  uint32_t j, n;

  table = p->tbl;
  n = p->nbits;
  if (bvvar_tag(table, i) != BVTAG_BIT_ARRAY || table->bit_size[i] != n) {
    return false;
  }

  a = table->def[i].bit;
  for (j=0; j<n; j++) {
    if (a[j] != p->val[j]) return false;
  }

  return true;
}

static bool eq_binop_hobj(binop_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;

  table = p->tbl;
  return bvvar_tag(table, i) == p->op && table->def[i].op[0] == p->left &&
    table->def[i].op[1] == p->right;
}

static bool eq_bvite_hobj(bvite_hobj_t *p, thvar_t i) {
  bv_vartable_t *table;
  bv_ite_t *d;

  table = p->tbl;
  if (bvvar_tag(table, i) == BVTAG_ITE) {
    d = table->def[i].ite;
    return d->cond == p->cond && d->left == p->left && d->right == p->right;
  } else {
    return false;
  }
}


/*
 * Build
 */
static thvar_t build_small_const_hobj(small_const_hobj_t *p) {
  return make_small_const(p->tbl, p->nbits, p->val);
}

static thvar_t build_big_const_hobj(big_const_hobj_t *p) {
  return make_big_const(p->tbl, p->nbits, p->val);
}

static thvar_t build_select_hobj(select_hobj_t *p) {
  return make_select(p->tbl, p->idx, p->var);
}

static thvar_t build_bitop_hobj(bitop_hobj_t *p) {
  return make_bitop(p->tbl, p->op, p->left, p->right);
}

static thvar_t build_bit_hobj(bit_hobj_t *p) {
  return make_bit(p->tbl, p->val);
}

static thvar_t build_bit_array_hobj(bit_array_hobj_t *p) {
  return make_bitarray(p->tbl, p->nbits, p->val);
}

static thvar_t build_binop_hobj(binop_hobj_t *p) {
  return make_binop(p->tbl, p->nbits, p->op, p->left, p->right);
}

static thvar_t build_bvite_hobj(bvite_hobj_t *p) {
  return make_bvite(p->tbl, p->nbits, p->cond, p->left, p->right);
}


/*
 * Hash objects
 */
static small_const_hobj_t small_const_hobj = {
  { (hobj_hash_t) hash_small_const_hobj, (hobj_eq_t) eq_small_const_hobj, (hobj_build_t) build_small_const_hobj },
  NULL,
  0, 0,
};

static big_const_hobj_t big_const_hobj = {
  { (hobj_hash_t) hash_big_const_hobj, (hobj_eq_t) eq_big_const_hobj, (hobj_build_t) build_big_const_hobj },
  NULL,
  NULL, 0,
};

static select_hobj_t select_hobj = {
  { (hobj_hash_t) hash_select_hobj, (hobj_eq_t) eq_select_hobj, (hobj_build_t) build_select_hobj },
  NULL,
  0, 0,
};

static bitop_hobj_t bitop_hobj = {
  { (hobj_hash_t) hash_bitop_hobj, (hobj_eq_t) eq_bitop_hobj, (hobj_build_t) build_bitop_hobj },
  NULL,
  0, 0, 0,
};

static bit_hobj_t bit_hobj = {
  { (hobj_hash_t) hash_bit_hobj, (hobj_eq_t) eq_bit_hobj, (hobj_build_t) build_bit_hobj },
  NULL,
  0.
};

static bit_array_hobj_t bit_array_hobj = {
  { (hobj_hash_t) hash_bit_array_hobj, (hobj_eq_t) eq_bit_array_hobj, (hobj_build_t) build_bit_array_hobj },
  NULL,
  NULL, 0.
};

static binop_hobj_t binop_hobj = {
  { (hobj_hash_t) hash_binop_hobj, (hobj_eq_t) eq_binop_hobj, (hobj_build_t) build_binop_hobj },
  NULL,
  0, 0, 0, 0,
};

static bvite_hobj_t bvite_hobj = {
  { (hobj_hash_t) hash_bvite_hobj, (hobj_eq_t) eq_bvite_hobj, (hobj_build_t) build_bvite_hobj },
  NULL,
  0, 0, 0, 0,
};


/*
 * Hash-consing constructors
 */
static thvar_t get_small_const(bv_vartable_t *table, uint32_t n, uint64_t val) {
  small_const_hobj.tbl = table;
  small_const_hobj.val = val;
  small_const_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &small_const_hobj);
}

static thvar_t get_big_const(bv_vartable_t *table, uint32_t n, uint32_t *val) {
  big_const_hobj.tbl = table;
  big_const_hobj.val = val;
  big_const_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &big_const_hobj);
}

static thvar_t get_select(bv_vartable_t *table, uint32_t idx, thvar_t x) {
  select_hobj.tbl = table;
  select_hobj.idx = idx;
  select_hobj.var = x;
  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &select_hobj);
}

static thvar_t get_bitop(bv_vartable_t *table, bvvar_tag_t op, bit_t left, bit_t right) {
  bitop_hobj.tbl = table;
  bitop_hobj.op = op;
  bitop_hobj.left = left;
  bitop_hobj.right = right;
  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &bitop_hobj);
}

static thvar_t get_bit(bv_vartable_t *table, bit_t b) {
  bit_hobj.tbl = table;
  bit_hobj.val = b;
  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &bit_hobj);
}

static thvar_t get_bit_array(bv_vartable_t *table, uint32_t n, bit_t *a) {
  bit_array_hobj.tbl = table;
  bit_array_hobj.val = a;
  bit_array_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &bit_array_hobj);
}

static thvar_t get_binop(bv_vartable_t *table, uint32_t n, bvvar_tag_t op, thvar_t x, thvar_t y) {
  binop_hobj.tbl = table;
  binop_hobj.op = op;
  binop_hobj.left = x;
  binop_hobj.right = y;
  binop_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &binop_hobj);
}

static thvar_t get_bvite(bv_vartable_t *table, uint32_t n, literal_t l, thvar_t x, thvar_t y) {
  bvite_hobj.tbl = table;
  bvite_hobj.cond = l;
  bvite_hobj.left = x;
  bvite_hobj.right = y;
  bvite_hobj.nbits = n;
  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &bvite_hobj);
}



/*
 * Bit-level operations
 * - normalize and return a bit
 * - for (xor x y): ensure x < y and both children have positive polarity
 * - for (or x y): ensure x < y
 */
static bit_t get_xor(bv_vartable_t *table, bit_t x, bit_t y) {
  uint32_t sign;
  bit_t aux;

  assert(valid_bit(table, x) && valid_bit(table, y));

  sign = sign_of_bit(x) ^ sign_of_bit(y);
  x &= ~1; // clear sign bit 
  y &= ~1; // clear sign bit

  if (x > y) {
    aux = x; x = y; y = aux;
  }

  return mk_bit(get_bitop(table, BVTAG_XOR, x, y), sign);
}


static bit_t get_or(bv_vartable_t *table, bit_t x, bit_t y) {
  bit_t aux;

  assert(valid_bit(table, x) && valid_bit(table, y));

  if (x > y) {
    aux = x; x = y; y = aux;
  }

  return pos_bit(get_bitop(table, BVTAG_OR, x, y));
}


/*
 * Normalization and construction
 */
static thvar_t get_add(bv_vartable_t *table, thvar_t x, thvar_t y) {
  thvar_t aux;
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
	 table->bit_size[x] == table->bit_size[y]);

  if (x > y) {
    aux = x; x = y; y = aux;
  }
  n = table->bit_size[x];

  return get_binop(table, n, BVTAG_ADD, x, y);
}

static thvar_t get_sub(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
	 table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  return get_binop(table, n, BVTAG_SUB, x, y);
}

static thvar_t get_neg(bv_vartable_t *table, thvar_t x) {
  uint32_t n;

  assert(valid_bvvar(table, x));
  n = table->bit_size[x];
  return get_binop(table, n, BVTAG_NEG, x, null_thvar);
}

static thvar_t get_mul(bv_vartable_t *table, thvar_t x, thvar_t y) {
  thvar_t aux;
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
	 table->bit_size[x] == table->bit_size[y]);

  if (x > y) {
    aux = x; x = y; y = aux;
  }
  n = table->bit_size[x];

  return get_binop(table, n, BVTAG_MUL, x, y);
}

static thvar_t get_udiv(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
	 table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  return get_binop(table, n, BVTAG_UDIV, x, y);
}

static thvar_t get_urem(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
	 table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  return get_binop(table, n, BVTAG_UREM, x, y);
}

static thvar_t get_sdiv(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
	 table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  return get_binop(table, n, BVTAG_SDIV, x, y);
}

static thvar_t get_srem(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
	 table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  return get_binop(table, n, BVTAG_SREM, x, y);
}

static thvar_t get_smod(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
	 table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  return get_binop(table, n, BVTAG_SMOD, x, y);
}

static thvar_t get_shl(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
	 table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  return get_binop(table, n, BVTAG_SHL, x, y);
}

static thvar_t get_lshr(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
	 table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  return get_binop(table, n, BVTAG_LSHR, x, y);  
}

static thvar_t get_ashr(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
	 table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  return get_binop(table, n, BVTAG_ASHR, x, y);  
}

static thvar_t get_ite(bv_vartable_t *table, literal_t c, thvar_t x, thvar_t y) {
  uint32_t n;
  thvar_t aux;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
	 table->bit_size[x] == table->bit_size[y]);
 
  // Normalization: rewrite (ite (not b) x y) to (ite b y x)
  // Could check whether c is true or false?? 
  if (is_neg(c)) {
    aux = x; x = y; y = aux;
    c = not(c);
  }

  n = table->bit_size[x];
  return get_bvite(table, n, c, x, y);
}



/*
 * Search for (op x y). Return -1 if it's not in the table.
 */
static thvar_t find_binop(bv_vartable_t *table, uint32_t n, bvvar_tag_t op, thvar_t x, thvar_t y) {
  binop_hobj.tbl = table;
  binop_hobj.op = op;
  binop_hobj.left = x;
  binop_hobj.right = y;
  binop_hobj.nbits = n;
  return int_htbl_find_obj(&table->htbl, (int_hobj_t *) &binop_hobj);
}

static thvar_t find_udiv(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
	 table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  return find_binop(table, n, BVTAG_UDIV, x, y);
}

static thvar_t find_urem(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
	 table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  return find_binop(table, n, BVTAG_UREM, x, y);
}

static thvar_t find_sdiv(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
	 table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  return find_binop(table, n, BVTAG_SDIV, x, y);
}

static thvar_t find_srem(bv_vartable_t *table, thvar_t x, thvar_t y) {
  uint32_t n;

  assert(valid_bvvar(table, x) && valid_bvvar(table, y) &&
	 table->bit_size[x] == table->bit_size[y]);

  n = table->bit_size[x];
  return find_binop(table, n, BVTAG_SREM, x, y);
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





/***************
 *  PARTITION  *
 **************/

/*
 * TRAIL STACK
 */

/*
 * Initialize the stack: don't allocate anything yet
 */
static void init_bv_ptrail(bv_ptrail_t *stack) {
  stack->size = 0;
  stack->top = 0;
  stack->top_frame = -1;
  stack->data = NULL;
}


/*
 * Delete the stack
 */
static void delete_bv_ptrail(bv_ptrail_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Empty the stack
 */
static void reset_bv_ptrail(bv_ptrail_t *stack) {
  stack->top = 0;
  stack->top_frame = -1;
}

/*
 * Extend: allocate the initial data array or make it 50% larger
 */
static void extend_bv_ptrail(bv_ptrail_t *stack) {
  uint32_t n;

  n = stack->size;
  if (n == 0) {
    n = DEF_BVTRAIL_SIZE;
  } else {
    assert(n >= 2);
    n += (n >> 1);
  }

  if (n >= MAX_BVTRAIL_SIZE) {
    out_of_memory();
  }

  stack->data = (int32_t *) safe_realloc(stack->data, n * sizeof(int32_t));
  stack->size = n;
}



/*
 * Push integer u on top of the stack
 */
static void bv_ptrail_push(bv_ptrail_t *stack, int32_t u) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_bv_ptrail(stack);
  }
  assert(i < stack->size);
  stack->data[i] = u;
  stack->top = i+1;
}


/*
 * Start a new frame
 */
static void bv_ptrail_new_frame(bv_ptrail_t *stack) {
  int32_t k;

  k = stack->top;
  bv_ptrail_push(stack, stack->top_frame);
  stack->top_frame = k;
}


/*
 * Remove the top frame
 */
static void bv_ptrail_pop_frame(bv_ptrail_t *stack) {
  int32_t k;

  assert(stack->top_frame >= 0);

  k = stack->top_frame;
  stack->top_frame = stack->data[k];
  stack->top = k;
}


/*
 * Encoding of variable + increment bit
 * - incr true means bit = 1, false: bit = 0
 */
static inline int32_t merge_code(thvar_t y, bool incr) {
  return (((int32_t) y) << 1) | (int32_t) incr;
}


/*
 * Conversion of code back to variable & increment bit
 */
static inline thvar_t var_of_merge_code(int32_t c) {
  return (thvar_t) (c >> 1);
}

static inline bool incr_of_merge_code(int32_t c) {
  return (c & 1);
}



/*
 * Push code for (y, incr)
 */
static inline void bv_ptrail_push_code(bv_ptrail_t *stack, thvar_t y, bool incr) {
  bv_ptrail_push(stack, merge_code(y, incr));
}



/*
 * PARTITION TABLE
 */

/*
 * Initialization: create an empty table
 */
static void init_bv_partition(bv_partition_t *p) {
  p->nelems = 0;
  p->size = 0;
  p->parent = NULL;
  p->rank = NULL;
  p->level = 0;
  init_bv_ptrail(&p->trail);
}


/*
 * Deletion
 */
static void delete_bv_partition(bv_partition_t *p) {
  safe_free(p->parent);
  safe_free(p->rank);
  p->parent = NULL;
  p->rank = NULL;
  delete_bv_ptrail(&p->trail);
}


/*
 * Reset: empty the table
 */
static inline void reset_bv_partition(bv_partition_t *p) {
  p->nelems = 0;
  p->level = 0;
  reset_bv_ptrail(&p->trail);
}


/*
 * Make sure the arrays parent and rank are large enough to store
 * parent[x] and rank[x]. Do nothing if x < p->nelems.
 * Otherwise, make parent and rank large enough and initialize
 * parent[y] to -1 for all y from p->nelems to x.
 */
static void resize_bv_partition(bv_partition_t *p, thvar_t x) {
  uint32_t n;
  thvar_t y;

  n = p->size;
  if (n <= x) {
    if (n == 0) {
      n = DEF_BVPARTITION_SIZE;
    } else {
      n += n>>1; // try to increase by 50%
    }
    if (n <= x) {
      n = x+1;
    }
    if (n >= MAX_BVPARTITION_SIZE) {
      out_of_memory();
    }

    p->size = n;
    p->parent = (int32_t *) safe_realloc(p->parent, n * sizeof(int32_t));
    p->rank = (uint8_t *) safe_realloc(p->rank, n * sizeof(uint8_t));
  }

  assert(x < p->size);

  for (y = p->nelems; y <= x; y++) {
    p->parent[y] = -1;
  }
  p->nelems = y;
}




/*
 * PARTITION OPERATIONS FOR BIT-VECTOR VARIABLES
 */

/*
 * Add bit-vector variable x to the partition table with initial rank rnk
 * - x must not be present in p
 * - rnk must be either 0 or 255
 * - x is made root of its class
 * If level > 0, x is saved on the trail stack.
 */
static void bv_partition_add_aux(bv_partition_t *p, thvar_t x, uint8_t rnk) {
  assert(x >= 0);
  if (x >= p->nelems) {
    resize_bv_partition(p, x);
  }
  assert(p->parent[x] == -1);
  p->parent[x] = x;
  p->rank[x] = rnk;

  if (p->level > 0) {
    bv_ptrail_push_code(&p->trail, x, false);
  }
}

// add x with rank 0
static inline void bv_partition_add(bv_partition_t *p, thvar_t x) {
  bv_partition_add_aux(p, x, 0);
}

// add x with maximal rank
static inline void bv_partition_add_root(bv_partition_t *p, thvar_t x) {
  bv_partition_add_aux(p, x, 255);
}


/*
 * Find the root of a bit-vector variable x in p
 * - return null_thvar if x is not in the table
 * We don't use path compression here since we may have to undo the 
 * merging of classes.
 */
static thvar_t bv_partition_find_root(bv_partition_t *p, thvar_t x) {
  thvar_t *parent;
  thvar_t y;

  assert(x >= 0);

  if (x >= p->nelems) return null_thvar;

  parent = p->parent;
  y = parent[x];
  if (y < 0) return null_thvar;

  // find the root
  while (x != y) {
    x = y;
    y = parent[x];
  }

  return y;
}



/*
 * Get the root of x in p. Return x itself if x is not in the table.
 */
static thvar_t bv_partition_get_root(bv_partition_t *p, thvar_t x) {
  thvar_t r;

  r = bv_partition_find_root(p, x);
  if (r == null_thvar) {
    return x;
  } else {
    return r;
  }
}



/*
 * Check whether x is a root variable
 */
static inline bool bv_is_root(bv_partition_t *p, thvar_t x) {
  assert(x >= 0);
  return x < p->nelems && p->parent[x] == x;
}


/*
 * Merge the classes of x and y
 * - x and y must be distinct root 
 * - x or y must have rank < 255
 */
static void merge_bv_classes(bv_partition_t *p, thvar_t x, thvar_t y) {
  uint8_t rx, ry;

  assert(bv_is_root(p, x) && bv_is_root(p, y) && x != y);

  rx = p->rank[x];
  ry = p->rank[y];

  assert(rx < 255 || ry < 255);

  if (p->level == 0) {
    // nothing saved on the trail stack
    if (rx < ry) {
      // y stays root
      p->parent[x] = y;
    } else {
      // x stays root, increment its rank if rx == ry
      p->parent[y] = x;
      if (rx == ry) {
	p->rank[x] = rx + 1;
      }
    }
  } else {
    // save whichever of x or y is no longer root
    if (rx < ry) {
      p->parent[x] = y;
      bv_ptrail_push_code(&p->trail, x, false);
    } else if (ry < rx) {
      p->parent[y] = x;
      bv_ptrail_push_code(&p->trail, y, false);
    } else {
      // keep x as root
      p->parent[y] = x;
      p->rank[x] = rx + 1;
      bv_ptrail_push_code(&p->trail, y, true);
    }
  }
}


/*
 * Check whether x is mapped to another variable y
 */
static inline bool bv_is_replaced(bv_partition_t *p, thvar_t x) {
  assert(x >= 0);
  return x < p->nelems && p->parent[x] != x && p->parent[x] != null_thvar;
}



/*
 * PUSH/POP
 */


/*
 * Push: start a new frame
 */
static void bv_partition_push(bv_partition_t *p) {
  p->level ++;
  bv_ptrail_new_frame(&p->trail);
}


/*
 * Pop: restore the previous partition
 */
static void bv_partition_pop(bv_partition_t *p) {
  bv_ptrail_t *stack;
  uint32_t n, k;
  int32_t c;
  thvar_t y, x;

  assert(p->level > 0 && p->trail.top_frame >= 0 && 
	 p->trail.top > p->trail.top_frame);

  stack = &p->trail;
  k = stack->top_frame;
  n = stack->top - 1;
  while (n > k) {
    c = stack->data[n];
    y = var_of_merge_code(c);
    assert(0 <= y && y < p->nelems);
    x = p->parent[y];
    assert(0 <= x && x < p->nelems);
    if (x == y) {
      // undo add y
      p->parent[y] = -1;
    } else {
      // undo merge x y
      p->parent[y] = y;
      if (incr_of_merge_code(c)) {	
	p->rank[x] --;
	assert(p->rank[x] == p->rank[y]);
      }
    }
    n --;
  }

  bv_ptrail_pop_frame(stack);
  p->level --;
}




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




/***********************
 *  PROPAGATION QUEUE  *
 **********************/

/*
 * Initialization: use the default size
 */
static void init_bv_prop_queue(bv_prop_queue_t *queue) {
  uint32_t n;

  n = DEF_BV_PROPQUEUE_SIZE;
  assert(n < MAX_BV_PROPQUEUE_SIZE);

  queue->nvars = 0;
  queue->size = n;
  queue->unsat = false;
  queue->value = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  init_int_queue(&queue->queue, 0);
}


/*
 * Deletion
 */
static void delete_bv_prop_queue(bv_prop_queue_t *queue) {
  safe_free(queue->value);
  queue->value = NULL;
  delete_int_queue(&queue->queue);
}


/*
 * Make the queue large enough to store value[x]
 * - do nothing if x < queue->nvars
 * - otherwise, make value large enough and initialize value[y] to UNDEF 
 *   for all nvars <= y <= x
 */
static void resize_bv_prop_queue(bv_prop_queue_t *queue, thvar_t x) {
  uint32_t i, n;

  n = queue->size;
  if (n <= x) {
    n += n>>1;   // try to make the queue 50% larger
    if (n <= x) {
      n = x+1;
    } 

    if (n >= MAX_BV_PROPQUEUE_SIZE) {
      out_of_memory();
    } 

    queue->size = n;
    queue->value = (uint8_t *) safe_realloc(queue->value, n * sizeof(uint8_t));
  }

  assert(x < queue->size);

  for (i = queue->nvars; i <= x; i++) {
    queue->value[i] = VAL_UNDEF;
  }
  queue->nvars = i;
}



/*
 * Assign value v to x
 */
static void bv_prop_queue_assign(bv_prop_queue_t *queue, thvar_t x, bval_t v) {
  resize_bv_prop_queue(queue, x);
  queue->value[x] = v;
}

/*
 * Get the value of x in the queue
 */
static inline bval_t bv_prop_queue_get_val(bv_prop_queue_t *queue, thvar_t x) {
  if (x >= queue->nvars) {
    return VAL_UNDEF;
  } else {
    return queue->value[x];
  }
}

/*
 * Same thing for bit b
 */
static bval_t bv_prop_queue_get_bit_val(bv_prop_queue_t *queue, bit_t b) {
  bval_t vx;

  vx = bv_prop_queue_get_val(queue, var_of_bit(b));
  if (is_neg(b)) {
    vx = opposite_bval(vx);
  }
  return vx;
}

/*
 * Add x to the queue
 */
static inline void bv_prop_queue_push(bv_prop_queue_t *queue, thvar_t x) {
  int_queue_push(&queue->queue, x);
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





/**************************************
 *  CACHE FOR LOWER AND UPPER BOUNDS  *
 *************************************/

/*
 * Get a bound descriptor for x in the bounds cache
 * - return NULL if there's no cache or if the requested
 *   descriptor is not present in the cache
 * - tag must be either BVBOUND_SIGNED or BVBOUND_UNSIGNED
 */
static bvbound_t *get_cached_bvbound(bv_solver_t *solver, thvar_t x, bvbound_tag_t tag) {
  bvbound_cache_t *cache;
  bvbound_t *b;

  assert(valid_bvvar(&solver->vtbl, x));

  cache = solver->bounds;
  b = NULL;
  if (cache != NULL) {
    b = find_bvbound(cache, tag, x);
  }

  return b;
}


/*
 * Return the internal cache
 * - allocate and initialize it if needed
 */
static bvbound_cache_t *get_bounds_cache(bv_solver_t *solver) {
  bvbound_cache_t *cache;

  cache = solver->bounds;
  if (cache == NULL) {
    cache = (bvbound_cache_t *) safe_malloc(sizeof(bvbound_cache_t));
    init_bvbound_cache(cache, 0); // use default initial size
    solver->bounds = cache;
  }
  
  return cache;
}


/*
 * Store bounds on x in the cache
 * - the first function is for bounds computed as 64bit numbers
 * - the second function works in all cases: lower and upper as bounds
 *   represented as arrays of 32bit words
 * Return the bvbound object created
 */
static bvbound_t *add_bvbound64_to_cache(bv_solver_t *solver, thvar_t x, bvbound_tag_t tag, uint64_t lower, uint64_t upper) {
  bvbound_cache_t *cache;
  uint32_t n;

  cache = get_bounds_cache(solver);
  n = bvvar_bitsize(&solver->vtbl, x);
  return cache_bvbound64(cache, tag, x, n, lower, upper);  
}

#if 0
// NOT USED
static bvbound_t *add_bvbound_to_cache(bv_solver_t *solver, thvar_t x, bvbound_tag_t tag, uint32_t *lower, uint32_t *upper) {
  bvbound_cache_t *cache;
  uint32_t n;

  cache = get_bounds_cache(solver);
  n = bvvar_bitsize(&solver->vtbl, x);
  return cache_bvbound(cache, tag, x, n, lower, upper);
}

#endif





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





/***************
 *  UTILITIES  *
 **************/

/*
 * Mask for normalizing an n-bit constant for n <= 64
 * - x & mask64(n) is the normalization of x 
 *  (i.e., high-order bits are 0)
 * - warning: shift by 64 is undefined in C
 */
static inline uint64_t mask64(uint32_t n) {
  assert(0 < n && n <= 64);
  return (~((uint64_t) 0)) >> (64 - n);
}

/*
 * Mask to select the sign bit in an n-bit number
 */
static inline uint64_t sgn_bit_mask64(uint32_t n) {
  assert(0 < n && n <= 64);
  return ((uint64_t) 1) << (n - 1);
}


/*
 * Test whether bit k of c is 1 or 0
 * - true means 1, false means 0
 */
static inline bool tst_bit64(uint64_t c, uint32_t k) {
  assert(0 <= k && k < 64);
  return c & (((uint64_t) 1) << k);
}


/*
 * Clear or set bit k of c
 */
static inline uint64_t clr_bit64(uint64_t c, uint32_t k) {
  assert(0 <= k && k < 64);
  return c & ~(((uint64_t) 1) << k);
}

static inline uint64_t set_bit64(uint64_t c, uint32_t k) {
  assert(0 <= k && k < 64);
  return c | (((uint64_t) 1) << k);
}


/*
 * Get the sign bit of c, interpreted as an n-bit 2s-complement
 * number
 */
static inline bool tst_sign_bit64(uint64_t c, uint32_t n) {
  assert(0 < n && n <= 64);
  return tst_bit64(c, n-1);
}

static inline bool is_neg64(uint64_t c, uint32_t n) {
  return tst_sign_bit64(c, n);
}

static inline bool is_pos64(uint64_t c, uint32_t n) {
  return ! tst_sign_bit64(c, n);
}


/*
 * Convert c into a signed 64 bit number
 */
static int64_t signed_int64(uint64_t c, uint32_t n) {
  assert(0 < n && n <= 64);
  if (is_neg64(c, n)) {
    return c | ~mask64(n); // sign extend
  } else {
    return c;
  }
}


/*
 * Maximal and miminal n-bit signed number
 */
static inline uint64_t max_signed64(uint32_t n) {
  assert(0 < n && n <= 64);
  return (n == 1) ? 0 : mask64(n-1); // all bits 1, except the sign bit
}

static inline uint64_t min_signed64(uint32_t n) {
  return sgn_bit_mask64(n); // all bits 0, except the sign bit
}


/*
 * Check whether a >= b: both are interpreted as n-bit signed numbers
 */
static bool signed64_ge(uint64_t a, uint64_t b, uint32_t n) {
  uint64_t sa, sb;

  sa = a & sgn_bit_mask64(n); // sign of a << (n-1)
  sb = b & sgn_bit_mask64(n); // sign of b << (n-1)

  // a >= b iff (sign of a = 0 and sign of b = 1) 
  //         or (sign_of a == sign_of b and a >= b);
  return (sa < sb) || (sa == sb && a >= b);
}

/*
 * Check whether a>b: both are interpreted as n-bit signed numbers
 */
static bool signed64_gt(uint64_t a, uint64_t b, uint32_t n) {
  uint64_t sa, sb;

  sa = a & sgn_bit_mask64(n); // sign of a << (n-1)
  sb = b & sgn_bit_mask64(n); // sign of b << (n-1)

  // a >= b iff (sign of a = 0 and sign of b = 1) 
  //         or (sign_of a == sign_of b and a > b);
  return (sa < sb) || (sa == sb && a > b);
}




/************************************
 *  CONVERSION OF ARITHMETIC TERMS  *
 ***********************************/

/*
 * Auxiliary function: compute x * y
 * - with x == null_thvar interpreted as 1
 */
static thvar_t get_mul_aux(bv_vartable_t *vtbl, thvar_t x, thvar_t y) {
  assert(y != null_thvar);

  if (x == null_thvar) {
    return y;
  } else {
    return get_mul(vtbl, x, y);
  }
}

/*
 * Auxiliary function: compute x + y
 * - with x == null_thvar interpreted as 0
 */
static thvar_t get_add_aux(bv_vartable_t *vtbl, thvar_t x, thvar_t y) {
  assert(y != null_thvar);

  if (x == null_thvar) {
    return y;
  } else {
    return get_add(vtbl, x, y);
  }
}


/*
 * Compute x - y with x == null_thvar interpreted as 0
 */
static thvar_t get_sub_aux(bv_vartable_t *vtbl, thvar_t x, thvar_t y) {
  assert(y != null_thvar);

  if (x == null_thvar) {
    return get_neg(vtbl, y);
  } else {
    return get_sub(vtbl, x, y);
  }
}



/*
 * Construct the constant 0 with nbits
 */
static thvar_t get_zero(bv_solver_t *solver, uint32_t nbits) {
  if (nbits > 64) {
    bvconstant_set_all_zero(&solver->aux1, nbits);
    return get_big_const(&solver->vtbl, nbits, solver->aux1.data);
  } else {
    return get_small_const(&solver->vtbl, nbits, 0);
  }
}




/*
 * Return a variable equal to x^d
 */
static thvar_t bv_solver_create_var_exp(bv_solver_t *solver, thvar_t x, int32_t d) {
  thvar_t a, b;

  assert(d >= 1);

  if (d == 1) {
    return x;
  } else if (d == 2) {
    return get_mul(&solver->vtbl, x, x);

  } else {
    a = null_thvar;
    b = x;
    for (;;) {
      assert(d > 0);
      if ((d & 1) != 0) {
	a = get_mul_aux(&solver->vtbl, a, b);
      }
      d >>= 1;
      if (d == 0) break;
      b = get_mul(&solver->vtbl, b, b);
    }

    return a;
  }
}


/*
 * Multiply c by x^d when x is a large constant
 * - c must be a buffer large enough for (nbits/32) words
 * WARNING: this does nor normalize c modulo 2^nbits. 
 * Normalization must be done later.
 */
static void bv_solver_eval_big_exp(bv_solver_t *solver, uint32_t nbits, uint32_t *c, thvar_t x, uint32_t d) {
  uint32_t w;

  assert(bvvar_is_big_const(&solver->vtbl, x) && bvvar_bitsize(&solver->vtbl, x) == nbits);

  w = (nbits + 31) >> 5;
  bvconst_mulpower(c, w, big_const_value(&solver->vtbl, x), d); // c := c * x^d
}


/*
 * Return x^d when x is a small constant (64bits)
 * - not reduced modulo 2^nbits
 */
static inline uint64_t bv_solver_eval_small_exp(bv_solver_t *solver, thvar_t x, uint32_t d) {
  return upower64(small_const_value(&solver->vtbl, x), d);
}



/*
 * Construct c * x when c is a large constant
 * - c must be normalized modulo 2^nbits and must be nonzero
 */
static thvar_t eval_big_mul(bv_solver_t *solver, uint32_t nbits, uint32_t *c, thvar_t x) {
  bv_vartable_t *vtbl;
  uint32_t w;

  vtbl = &solver->vtbl;
  w = (nbits + 31) >> 5;
  if (bvconst_is_one(c, w)) {
    return x;
  } else if (bvconst_is_minus_one(c, nbits)) {
    return get_neg(vtbl, x);
  } else {    
    return get_mul(vtbl, get_big_const(vtbl, nbits, c), x);
  }
}


/*
 * Construct c * x when c is a small constant
 * - c must be normalized modulo 2^nbits and must be nonzero
 */
static thvar_t eval_small_mul(bv_solver_t *solver, uint32_t nbits, uint64_t c, thvar_t x) {
  bv_vartable_t *vtbl;

  vtbl = &solver->vtbl;

  if (c == (uint64_t) 1) {
    return x;
  } else if (c == mask64(nbits)) { 
    // i.e., c is -1
    return get_neg(vtbl, x);
  } else {
    return get_mul(vtbl, get_small_const(vtbl, nbits, c), x);
  }
}




/*
 * Return a variable equal to a product (x_1^d_1 * ... * x_k^d_k)
 * - the product is stored in buffer b
 * - there must be at least one element (x_1^d_1) in the buffer
 * - all variables in the buffer must have the same bitsize
 */
static thvar_t bv_solver_create_product(bv_solver_t *solver, vpbuffer_t *b) {
  thvar_t prod, x;
  uint32_t i, n;

  n = b->len;
  assert(n > 0);
  prod = bv_solver_create_var_exp(solver, b->prod[0].var, b->prod[0].exp); // x_1^d_1
  for (i=1; i<n; i++) {
    // x := x_i ^ d_i
    x = bv_solver_create_var_exp(solver, b->prod[i].var, b->prod[i].exp);
    prod = get_mul(&solver->vtbl, prod, x);
  }
  return prod;
}







/*
 * Convert varproduct v to an internal variable
 * - nbits = bitsize of v
 * - apply the variable renaming defined by bv_map
 * - all variables of v must occur in bv_map
 * - replace constants by their values
 */
static thvar_t bv_solver_map_varprod(bv_solver_t *solver, varprod_t *v, itable_t *bv_map, uint32_t nbits) {
  vpbuffer_t *b;
  bv_vartable_t *vtbl;
  uint32_t i, n, w;
  uint64_t c;
  uint32_t *coeff;
  thvar_t x;

  b = &solver->prod_buffer;
  vpbuffer_reset(b);

  vtbl = &solver->vtbl;

  // width in 32-bit words
  w = (nbits + 31) >> 5;

  // initialize the constant coeff (and c)
  c = 1;
  coeff = NULL; // stop GCC warning
  if (nbits > 64) {
    bvconstant_set_bitsize(&solver->aux1, nbits);
    coeff = solver->aux1.data;
    bvconst_set_one(coeff, w);
  }

  n = v->len;
  for (i=0; i<n; i++) {
    x = itable_get(bv_map, v->prod[i].var);
    assert(x != nil);
    switch (bvvar_tag(vtbl, x)) {
    case BVTAG_SMALL_CONST:
      // c := c * val(x)^d
      c *= bv_solver_eval_small_exp(solver, x, v->prod[i].exp);
      break;
    case BVTAG_BIG_CONST:
      // coeff := coeff * val(x)^d 
      bv_solver_eval_big_exp(solver, nbits, coeff, x, v->prod[i].exp);
      break;
    default:
      // add x^d to the product
      vpbuffer_mul_varexp(b, x, v->prod[i].exp);
      break;
    }
  }

  /*
   * b contains x_1^d_1 ... x_k^d_k (normalized)
   * c or coeff contains the constant factor
   */
  if (nbits > 64) {
    /* 
     * normalize coeff, then build coeff * (x_1^d_1 ... x_k^d_k)
     */
    bvconst_normalize(coeff, nbits);
    if (bvconst_is_zero(coeff, w) || b->len == 0) {
      return get_big_const(vtbl, nbits, coeff);
    } else {
      x = bv_solver_create_product(solver, b);
      return eval_big_mul(solver, nbits, coeff, x);
    }
  } else {
    /*
     * normalize c then build c * (x_1^d_1 ... x_k^d_k)
     */
    c &= mask64(nbits); // normalize c
    if (c == 0 || b->len == 0) {
      return get_small_const(vtbl, nbits, c);
    } else {
      x = bv_solver_create_product(solver, b);
      return eval_small_mul(solver, nbits, c, x);
    }
  }
}




/*
 * Construct x +/- a * y
 * - if x == null_thvar, it's interpreted as 0
 * - if y == const_idx, it's interpreted as 1
 * - neg defines the sign: if neg, build x - a * y else build x + a * y
 * - a must be a nonzero constant, normalized modulo 2^nbits
 */
static thvar_t eval_small_addmul(bv_solver_t *solver, uint32_t nbits, thvar_t x, bool neg, uint64_t a, thvar_t y) {
  bv_vartable_t *vtbl;

  assert(0 < nbits && nbits <= 64 && a != 0);

  vtbl = &solver->vtbl;

  if (x == null_thvar && y == const_idx) {
    if (neg) {
      a = (-a) & mask64(nbits);
    }
    return get_small_const(vtbl, nbits, a);
  }

  // convert a * y
  if (y == const_idx) {
    y = get_small_const(vtbl, nbits, a);
  } else {
    y = eval_small_mul(solver, nbits, a, y);
  }

  if (neg) {
    return get_sub_aux(vtbl, x, y);
  } else {
    return get_add_aux(vtbl, x, y);
  }
}




/*
 * Construct x +/- a * y
 * - if x == null_thvar, it's interpreted as 0
 * - if y == const_idx, it's interpreted as 1
 * - neg defines the sign: if neg, build x - a * y else build x + a * y
 * - a must be a nonzero constant, normalized modulo 2^nbits
 */
static thvar_t eval_big_addmul(bv_solver_t *solver, uint32_t nbits, thvar_t x, bool neg, uint32_t *a, thvar_t y) {
  bv_vartable_t *vtbl;
  uint32_t *c;
  uint32_t w;

  assert(nbits > 64);

  vtbl = &solver->vtbl;

  if (x == null_thvar && y == const_idx) {
    if (neg) {
      bvconstant_set_bitsize(&solver->aux1, nbits);
      c = solver->aux1.data;
      w = solver->aux1.width;
      bvconst_negate2(c, w, a);
      return get_big_const(vtbl, nbits, c);
    } else {
      return get_big_const(vtbl, nbits, a);
    }
  }

  // convert a * y
  if (y == const_idx) {
    y = get_big_const(vtbl, nbits, a);
  } else {
    y = eval_big_mul(solver, nbits, a, y);
  }

  if (neg) {
    return get_sub_aux(vtbl, x, y);
  } else {
    return get_add_aux(vtbl, x, y);
  }  
}





/*
 * Convert bitvector polynomial p to an internal variable
 * - bv_map = variable substitution
 * - all primitive variables of p must occur in bv_map
 * - replace constants by their values
 */
static thvar_t bv_solver_map_poly(bv_solver_t *solver, bvarith_expr_t *p, itable_t *bv_map) {
  bv_vartable_t *vtbl;
  bvpoly_buffer_t *b;
  bv_var_manager_t *m;
  uint32_t i, n, nbits;
  int32_t x;
  thvar_t y;
  
  nbits = p->size;
  b = &solver->buffer;
  reset_bvpoly_buffer(b, nbits);

  m = solver->bv_manager;
  vtbl = &solver->vtbl;

  /*
   * Convert p to a polynomial stored in buffer b
   * - substitute variables of p by their image in bv_map
   * - convert auxiliary variables of p to products
   * - replace small/big constants by their value
   */
  n = p->nterms;
  for (i=0; i<n; i++) {
    x = p->mono[i].var;
    if (x == const_idx) {
      if (nbits <= 64) {
	bvpoly_buffer_add_const64(b, p->mono[i].coeff.c);
      } else {
	bvpoly_buffer_add_constant(b, p->mono[i].coeff.ptr);
      }
    } else {
      y = itable_get(bv_map, x);
      if (y == nil) {
	// x not internalized yet: so x must be an auxiliary variable
	assert(bv_var_manager_var_is_aux(m, x));
	y = bv_solver_map_varprod(solver, bv_var_manager_var_product(m, x), bv_map, nbits);
	// store the mapping x |-> y in bv_map
	itable_map(bv_map, x, y);
      }
      assert(valid_bvvar(vtbl, y) && bvvar_bitsize(vtbl, y) == nbits);

      // replace y by its value if it's a constant
      switch (bvvar_tag(vtbl, y)) {
      case BVTAG_SMALL_CONST:
	bvpoly_buffer_addmul_mono64(b, const_idx, p->mono[i].coeff.c, small_const_value(vtbl, y));
	break;

      case BVTAG_BIG_CONST:
	bvpoly_buffer_addmul_monomial(b, const_idx, p->mono[i].coeff.ptr, big_const_value(vtbl, y));
	break;

      default:
	// y is not a constant
       	if (nbits <= 64) {
	  bvpoly_buffer_add_mono64(b, y, p->mono[i].coeff.c);
	} else {
	  bvpoly_buffer_add_monomial(b, y, p->mono[i].coeff.ptr);
	}
	break;
      }
    }
  }

  /*
   * Normalize b then convert it to a sum of products
   */
  normalize_bvpoly_buffer(b);
  y = null_thvar;
  n = bvpoly_buffer_num_terms(b);
  if (nbits <= 64) {
    for (i=0; i<n; i++) {
      y = eval_small_addmul(solver, nbits, y, bvpoly_buffer_is_neg(b, i), bvpoly_buffer_coeff64(b, i), bvpoly_buffer_var(b, i));
    }
  } else {
    for (i=0; i<n; i++) {
      y = eval_big_addmul(solver, nbits, y, bvpoly_buffer_is_neg(b, i), bvpoly_buffer_coeff(b, i), bvpoly_buffer_var(b, i));
    }
  }

  if (y == null_thvar) {
    assert(n == 0);
    return get_zero(solver, nbits);
  } else {
    return y;
  }
}




/************************
 *  DIVISION/REMAINDER  *
 ***********************/

/*
 * Quotient in unsigned division: (x/y)
 */
static thvar_t map_udiv(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  uint64_t vx, vy;
  uint32_t n, w;

  vtbl = &solver->vtbl;

  x = bv_partition_get_root(&solver->partition, x);
  y = bv_partition_get_root(&solver->partition, y);

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_SMALL_CONST) {
      n = bvvar_bitsize(vtbl, x);
      assert(n == bvvar_bitsize(vtbl, y) && n <= 64);
      vx = vtbl->def[x].ival;
      vy = vtbl->def[y].ival;
      if (vy == 0) {
#if TRACE
	printf("---> Warning: division by zero bitvector\n");
	fflush(stdout);
#endif
	vx = mask64(n); // all ones
      } else {
	vx /= vy;
	assert(vx == (vx & mask64(n)));
      }
      return get_small_const(vtbl, n, vx);

    } else if (xtag == BVTAG_BIG_CONST) {
      n = bvvar_bitsize(vtbl, x);
      assert(n == bvvar_bitsize(vtbl, y) && n > 64);
      w = (n + 31) >> 5; // word size
      aux = &solver->aux1;
      if (bvconst_is_zero(vtbl->def[y].pval, w)) {
#if TRACE
	printf("---> Warning: division by zero bitvector\n");
	fflush(stdout);
#endif
	bvconstant_set_all_one(aux, n);
      } else {
	bvconstant_set_bitsize(aux, n);
	bvconst_udiv2(aux->data, n, vtbl->def[x].pval, vtbl->def[y].pval);
      }
      return get_big_const(vtbl, n, aux->data);
    }
  }

  return get_udiv(vtbl, x, y);
}

/*
 * Remainder in unsigned division of x by y
 */
static thvar_t map_urem(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  uint64_t vx, vy;
  uint32_t n, w;

  vtbl = &solver->vtbl;

  x = bv_partition_get_root(&solver->partition, x);
  y = bv_partition_get_root(&solver->partition, y);

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_SMALL_CONST) {
      n = bvvar_bitsize(vtbl, x);
      assert(n == bvvar_bitsize(vtbl, y) && n <= 64);
      vx = vtbl->def[x].ival;
      vy = vtbl->def[y].ival;
      if (vy == 0) {
#if TRACE
	printf("---> Warning: division by zero bitvector\n");
	fflush(stdout);
#endif
	// remainder = vx in that case
      } else {
	vx %= vy;
	assert(vx == (vx & mask64(n)));
      }
      return get_small_const(vtbl, n, vx);

    } else if (xtag == BVTAG_BIG_CONST) {
      n = bvvar_bitsize(vtbl, x);
      assert(n == bvvar_bitsize(vtbl, y) && n > 64);
      w = (n + 31) >> 5; // word size
      aux = &solver->aux1;
      if (bvconst_is_zero(vtbl->def[y].pval, w)) {
#if TRACE
	printf("---> Warning: division by zero bitvector\n");
	fflush(stdout);
#endif
	bvconstant_copy(aux, n, vtbl->def[x].pval); // result = x
      } else {
	bvconstant_set_bitsize(aux, n);
	bvconst_urem2(aux->data, n, vtbl->def[x].pval, vtbl->def[y].pval);
      }
      return get_big_const(vtbl, n, aux->data);
    }
  }
  
  return get_urem(&solver->vtbl, x, y);
}


/*
 * Quotient in signed division: (x/y) rounding toward 0
 */
static thvar_t map_sdiv(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  int64_t vx, vy;
  uint64_t z;
  uint32_t n, w;

  vtbl = &solver->vtbl;

  x = bv_partition_get_root(&solver->partition, x);
  y = bv_partition_get_root(&solver->partition, y);

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_SMALL_CONST) {
      n = bvvar_bitsize(vtbl, x);
      assert(n == bvvar_bitsize(vtbl, y) && n <= 64);
      vx = signed_int64(vtbl->def[x].ival, n);
      vy = signed_int64(vtbl->def[y].ival, n);
      if (vy == 0) {
#if TRACE
	printf("---> Warning: division by zero bitvector\n");
	fflush(stdout);
#endif
	if (vx >= 0) {
	  vx = -1;
	} else {
	  vx = 1;
	}
      } else {
	vx /= vy;
      }
      z = ((uint64_t) vx) & mask64(n);
      return get_small_const(vtbl, n, z);

    } else if (xtag == BVTAG_BIG_CONST) {
      n = bvvar_bitsize(vtbl, x);
      assert(n == bvvar_bitsize(vtbl, y) && n > 64);
      w = (n + 31) >> 5; // word size
      aux = &solver->aux1;
      if (bvconst_is_zero(vtbl->def[y].pval, w)) {
#if TRACE
	printf("---> Warning: division by zero bitvector\n");
	fflush(stdout);
#endif
	if (bvconst_tst_bit(vtbl->def[x].pval, n-1)) {
	  // x is negative: q = 1
	  bvconstant_set_bitsize(aux, n);
	  bvconst_set_one(aux->data, w);
	} else {
	  // x >= 0: q = -1
	  bvconstant_set_all_one(aux, n);
	}
      } else {
	bvconstant_set_bitsize(aux, n);
	bvconst_sdiv2(aux->data, n, vtbl->def[x].pval, vtbl->def[y].pval);
      }
      return get_big_const(vtbl, n, aux->data);
    }
  }

  return get_sdiv(&solver->vtbl, x, y);
}


/*
 * Remainder in signed division: (x/y) rounding toward 0
 */
static thvar_t map_srem(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  int64_t vx, vy;
  uint64_t z;
  uint32_t n, w;

  vtbl = &solver->vtbl;

  x = bv_partition_get_root(&solver->partition, x);
  y = bv_partition_get_root(&solver->partition, y);

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_SMALL_CONST) {
      n = bvvar_bitsize(vtbl, x);
      assert(n == bvvar_bitsize(vtbl, y) && n <= 64);
      vx = signed_int64(vtbl->def[x].ival, n);
      vy = signed_int64(vtbl->def[y].ival, n);
      if (vy == 0) {
#if TRACE
	printf("---> Warning: division by zero bitvector\n");
	fflush(stdout); // keep vx unchanged
#endif
      } else {
	// NOTE: check whether this is correct. check the C standard.
	vx %= vy;
      }
      z = ((uint64_t) vx) & mask64(n);
      return get_small_const(vtbl, n, z);

    } else if (xtag == BVTAG_BIG_CONST) {
      n = bvvar_bitsize(vtbl, x);
      assert(n == bvvar_bitsize(vtbl, y) && n > 64);
      w = (n + 31) >> 5; // word size
      aux = &solver->aux1;
      if (bvconst_is_zero(vtbl->def[y].pval, w)) {
#if TRACE
	printf("---> Warning: division by zero bitvector\n");
	fflush(stdout);
#endif
	bvconstant_copy(aux, n, vtbl->def[x].pval); // result = x
      } else {
	bvconstant_set_bitsize(aux, n);
	bvconst_srem2(aux->data, n, vtbl->def[x].pval, vtbl->def[y].pval);
      }
      return get_big_const(vtbl, n, aux->data);
    }
  }

  return get_srem(&solver->vtbl, x, y);
}


/*
 * Remainder: signed division with rounding toward - infinity
 */
static thvar_t map_smod(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvconstant_t *aux;
  bvvar_tag_t xtag, ytag;
  int64_t vx, vy, d;
  uint64_t z;
  uint32_t n, w;

  vtbl = &solver->vtbl;

  x = bv_partition_get_root(&solver->partition, x);
  y = bv_partition_get_root(&solver->partition, y);

  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  // deal with constants
  if (xtag == ytag) {
    if (xtag == BVTAG_SMALL_CONST) {
      n = bvvar_bitsize(vtbl, x);
      assert(n == bvvar_bitsize(vtbl, y) && n <= 64);
      vx = signed_int64(vtbl->def[x].ival, n);
      vy = signed_int64(vtbl->def[y].ival, n);
      if (vy == 0) {
#if TRACE
	printf("---> Warning: division by zero bitvector\n");
	fflush(stdout); // leave vx unchanged
#endif
      } else {
	d = vx/vy;
	if (vx == d * vy) {
	  vx = 0;
	} else {
	  if (d < 0) d --; // floor division
	  vx -= d * vy; // remainder = vx - d * vy
	}
      }
      z = ((uint64_t) vx) & mask64(n);
      return get_small_const(vtbl, n, z);

    } else if (xtag == BVTAG_BIG_CONST) {
      n = bvvar_bitsize(vtbl, x);
      assert(n == bvvar_bitsize(vtbl, y) && n > 64);
      w = (n + 31) >> 5; // word size
      aux = &solver->aux1;
      if (bvconst_is_zero(vtbl->def[y].pval, w)) {
#if TRACE
	printf("---> Warning: division by zero bitvector\n");
	fflush(stdout);
#endif
	bvconstant_copy(aux, n, vtbl->def[x].pval); // result = x
      } else {
	bvconstant_set_bitsize(aux, n);
	bvconst_smod2(aux->data, n, vtbl->def[x].pval, vtbl->def[y].pval);
      }
      return get_big_const(vtbl, n, aux->data);
    }
  }

  return get_smod(&solver->vtbl, x, y);
}





/**********************************
 *  CONVERSION OF BVLOGIC ARRAYS  *
 *********************************/

/*
 * Support for AIG simplifications: (this is very much the same 
 * code as in bit_expr.c)
 *
 * aig_shape(bit_t x): returns a code that identify the shape of x
 *   the code is interpreted as follows:
 *   AIG_POS_OR:  x is (or a b)
 *   AIG_NEG_OR:  x is ~(or a b)
 *   AIG_POS_XOR: x is (xor a b)
 *   AIG_NEG_XOR: x is ~(xor a b)
 *   AIG_ATOM:    anything else
 */
typedef enum aig_shape {
  AIG_POS_XOR,
  AIG_NEG_XOR,
  AIG_POS_OR,
  AIG_NEG_OR,
  AIG_ATOM,
} aig_shape_t;


/*
 * Table to compute the shape of bit x
 * - given k = bvvar_tag of node (x>>1) 
 *   and s = sign (0 or 1) of x
 *   then shape[k << 1 | s] = code for bit x
 * WARNING: we assume BVTAG_TRUE <= k <= BVTAG_OR
 * (i.e., 3 <= k <= 6)
 */
static const uint8_t const shape[14] = {
  AIG_ATOM, // BVTAG_VAR, POS         (should not happen)
  AIG_ATOM, // BVTAG_VAR, NEG         (should not happen)
  AIG_ATOM, // BVTAG_SMALL_CONST, POS (should not happen)
  AIG_ATOM, // BVTAG_SMALL_CONST, NEG (should not happen)
  AIG_ATOM, // BVTAG_BIG_CONST, POS   (should not happen)
  AIG_ATOM, // BVTAG_BIG_CONST, NEG   (should not happen)

  AIG_ATOM, // BVTAG_TRUE, POS
  AIG_ATOM, // BVTAG_TRUE, NEG
  AIG_ATOM, // BVTAG_SELECT, POS
  AIG_ATOM, // BVTAG_SELECT, NEG
  AIG_POS_XOR, // BVTAG_XOR, POS
  AIG_NEG_XOR, // BVTAG_XOR, NEG
  AIG_POS_OR,  // BVTAG_OR, POS
  AIG_NEG_OR,  // BVTAG_OR, NEG
};


/*
 * Shape of bit x
 */
static inline aig_shape_t shape_of_bit(bv_vartable_t *table, bit_t x) {
  int32_t k;

  assert(valid_bit(table, x));
  k = (bvvar_tag(table, var_of_bit(x)) << 1) | sign_of_bit(x);
  assert(6 <= k && k < 14);
  return (aig_shape_t) shape[k];
}


/*
 * Combination of two non-atomic shapes s1 and s2 into a single code
 */
typedef enum aig_shape_pair {
  AIG_POS_XOR_POS_XOR,
  AIG_POS_XOR_NEG_XOR,
  AIG_POS_XOR_POS_OR,
  AIG_POS_XOR_NEG_OR,
  AIG_NEG_XOR_POS_XOR,
  AIG_NEG_XOR_NEG_XOR,
  AIG_NEG_XOR_POS_OR,
  AIG_NEG_XOR_NEG_OR,
  AIG_POS_OR_POS_XOR,
  AIG_POS_OR_NEG_XOR,
  AIG_POS_OR_POS_OR,
  AIG_POS_OR_NEG_OR,
  AIG_NEG_OR_POS_XOR,
  AIG_NEG_OR_NEG_XOR,
  AIG_NEG_OR_POS_OR,
  AIG_NEG_OR_NEG_OR,
} aig_shape_pair_t;


/*
 * Combine the shapes s1 and s2
 */
static inline aig_shape_pair_t combine_shapes(aig_shape_t s1, aig_shape_t s2) {
  assert(0 <= s1 && s1 <= AIG_NEG_OR && 0 <= s2 && s2 <= AIG_NEG_OR);
  return (aig_shape_pair_t) (s1 << 2 | s2);
}


/*
 * Apply local rewrite rules to (OR a b)
 */
static bit_t simplify_bit_or(bv_vartable_t *table, bit_t a, bit_t b) {
  thvar_t va, vb;
  bit_t a0, a1;
  bit_t b0, b1;
  aig_shape_t a_shape, b_shape;  

  a0 = null_bit;
  a1 = null_bit;
  b0 = null_bit;
  b1 = null_bit;

  /*
   * Simplifications based on b + shape and children of a
   */
  a_shape = shape_of_bit(table, a);
  va = var_of_bit(a);
  if (a_shape != AIG_ATOM) {
    assert(bvvar_tag(table, va) == BVTAG_XOR || bvvar_tag(table, va) == BVTAG_OR);
    a0 = table->def[va].bop[0];
    a1 = table->def[va].bop[1];
    switch (a_shape) {
    case AIG_POS_XOR:
    case AIG_NEG_XOR:
      // nothing for now
      break;
    case AIG_POS_OR: 
      /*
       * (or (or a0 a1) a0)  --> (or a0 a1)
       * (or (or a0 a1) a1)  --> (or a0 a1)
       * (or (or a0 a1) ~a0) --> true
       * (or (or a0 a1) ~a1) --> true
       */
      if (b == a0 || b == a1) return a;  
      if (opposite_bits(b, a0) || opposite_bits(b, a1)) return true_bit;
      break;
    case AIG_NEG_OR:
      /*
       * (or ~(or a0 a1) ~a0) --> ~a0
       * (or ~(or a0 a1) ~a1) --> ~a1
       */
      if (opposite_bits(b, a0) || opposite_bits(b, a1)) return b;
      break;
    default:
      assert(false);
      break;
    }
  }
  
  /*
   * Symmetric rules: a + shape and children of b
   */
  b_shape = shape_of_bit(table, b);
  vb = var_of_bit(b);
  if (b_shape != AIG_ATOM) {
    assert(bvvar_tag(table, vb) == BVTAG_XOR || bvvar_tag(table, vb) == BVTAG_OR);
    b0 = table->def[vb].bop[0];
    b1 = table->def[vb].bop[1];
    switch (b_shape) {
    case AIG_POS_XOR:
    case AIG_NEG_XOR:
      break;
    case AIG_POS_OR:
      /*
       * (or b0 (or b0 b1))  --> (or b0 b1)
       * (or b1 (or b0 b1))  --> (or b0 b1)
       * (or ~b0 (or b0 b1)) --> true
       * (or ~b1 (or b0 b1)) --> true
       */
      if (a == b0 || a == b1) return b;  
      if (opposite_bits(a, b0) || opposite_bits(a, b1)) return true_bit;
      break;
    case AIG_NEG_OR:
      /*
       * (or ~b0 ~(or b0 b1)) --> ~b0
       * (or ~b1 ~(or b0 b1)) --> ~b1
       */
      if (opposite_bits(a, b0) || opposite_bits(a, b1)) return a;
      break;
    default:
      assert(false);
      break;
    }
  }

  /*
   * Children of a + children of b
   */
  if (a_shape != AIG_ATOM && b_shape != AIG_ATOM) {
    assert(a0 == table->def[va].bop[0] && 
           a1 == table->def[va].bop[1] && 
	   b0 == table->def[vb].bop[0] && 
	   b1 == table->def[vb].bop[1]);

    switch (combine_shapes(a_shape, b_shape)) {
    case AIG_POS_OR_POS_OR:
      /*
       * (or (or a0 a1) (or ~a0 b1)) --> true
       * (or (or a0 a1) (or b0 ~a0)) --> true
       * (or (or a0 a1) (or ~a1 b1)) --> true
       * (or (or a0 a1) (or b0 ~a1)) --> true
       */
      if (opposite_bits(a0, b0) || opposite_bits(a0, b1) ||
	  opposite_bits(a1, b0) || opposite_bits(a1, b1)) 
	return true_bit;
      break;

    case AIG_POS_OR_NEG_OR:
      /*
       * (or (or a0 a1) ~(or ~a0 b1))  --> (or a0 a1)
       * (or (or a0 a1) ~(or b0 ~a0))  --> (or a0 a1)
       * (or (or a0 a1) ~(or ~a1 b1))  --> (or a0 a1)
       * (or (or a0 a1) ~(or b0 ~a1))  --> (or a0 a1)
       */
      if (opposite_bits(a0, b0) || opposite_bits(a0, b1) ||
	  opposite_bits(a1, b0) || opposite_bits(a1, b1)) 
	return a;
      break;

    case AIG_NEG_OR_POS_OR:
      /*
       * (or ~(or ~b0 a1) (or b0 b1))  --> (or b0 b1)
       * (or ~(or a0 ~b0) (or b0 b1))  --> (or b0 b1)
       * (or ~(or ~b1 a1) (or b0 b1))  --> (or b0 b1)
       * (or ~(or a0 ~b1) (or b0 b1))  --> (or b0 b1)
       */
      if (opposite_bits(a0, b0) || opposite_bits(a0, b1) ||
	  opposite_bits(a1, b0) || opposite_bits(a1, b1)) 
	return b;
      break;

    case AIG_POS_OR_NEG_XOR:
      /*
       * We use the equality ~(xor b0 b1) == (xor ~b0 b1) and fall through
       */
      b0 ^= 1; // flip sign bit
    case AIG_POS_OR_POS_XOR:
      /*
       * (or (or a0 a1) (xor a0 a1))   --> (or a0 a1)
       * (or (or a0 a1) (xor ~a0 a1))  --> true
       * (or (or a0 a1) (xor a0 ~a1))  --> true
       * (or (or a0 a1) (xor ~a0 ~a1)) --> (or a0 a1)
       */
      if ((opposite_bits(a0, b0) && a1 == b1) || (a0 == b0 && opposite_bits(a1, b1)))
	return true_bit;
      if ((a0 == b0 && a1 == b1) || (opposite_bits(a0, b0) && opposite_bits(a1, b1)))
	return a;
      break;

    case AIG_NEG_XOR_POS_OR:
      /*
       * Rewrite ~(xor a0 a1) to (xor ~a0 a1) and fall through
       */
      a0 ^= 1; // flip sign bit
    case AIG_POS_XOR_POS_OR:
      /*
       * (or (xor b0 b1) (or b0 b1))   --> (or b0 b1)
       * (or (xor ~b0 b1) (or b0 b1))  --> true
       * (or (xor b0 ~b1) (or b0 b1))  --> true
       * (or (xor ~b0 ~b1) (or b0 b1)) --> (or b0 b1)
       */
      if ((opposite_bits(a0, b0) && a1 == b1) || (a0 == b0 && opposite_bits(a1, b1)))
	return true_bit;
      if ((a0 == b0 && a1 == b1) || (opposite_bits(a0, b0) && opposite_bits(a1, b1)))
	return b;
      break;

    case AIG_NEG_OR_NEG_OR:
      /*
       * (or ~(or a0 a1) ~(or ~a0 a1))  --> ~a1
       * (or ~(or a0 a1) ~(or a0 ~a1))  --> ~a0
       *
       * (or ~(or a0 a1) ~(or ~a0 ~a1)) --> ~(xor a0 a1)
       */
      if (opposite_bits(a0, b0) && a1 == b1) 
	return bit_not(a1);
      if (a0 == b0 && opposite_bits(a1, b1))
	return bit_not(a0);
      break;

    case AIG_NEG_OR_NEG_XOR:
      /*
       * Rewrite ~(xor b0 b1) to (xor ~b0 b1) and fall through
       */
      b0 ^= 1;
    case AIG_NEG_OR_POS_XOR:
      /*
       * (or ~(or a0 a1) (xor ~a0 a1))  --> (xor ~a0 a1)
       * (or ~(or a0 a1) (xor a0 ~a1))  --> (xor a0 ~a1)
       */
      if ((opposite_bits(a0, b0) && a1 == b1) || (a0 == b0 && opposite_bits(a1, b1)))
	return b;
      break;

    case AIG_NEG_XOR_NEG_OR:
      /*
       * Rewrite ~(xor a0 a1) to (xor ~a0 b1) and fall through
       */
      a0 ^= 1;
    case AIG_POS_XOR_NEG_OR:
      /*
       * (or (xor a0 a1) ~(or ~a0 a1))  --> (xor a0 a1)
       * (or (xor a0 a1) ~(or a0 ~a1))  --> (xor a0 a1)
       */
      if ((opposite_bits(a0, b0) && a1 == b1) || (a0 == b0 && opposite_bits(a1, b1)))
	return a;      
      break;

    case AIG_POS_XOR_POS_XOR:
    case AIG_NEG_XOR_NEG_XOR:
    case AIG_POS_XOR_NEG_XOR:
    case AIG_NEG_XOR_POS_XOR:
      // nothing
      break;
    }
  }
  
  return get_or(table, a, b);
}


/*
 * Build (OR a b): try the most basic simplifications
 * then call the full simplify function
 */
static bit_t mk_bit_or(bv_vartable_t *table, bit_t a, bit_t b) {
  /*
   * (or a true) --> true
   * (or true b) --> true
   * (or a ~a)   --> true
   *
   * (or a false) --> a
   * (or false b) --> b
   * (or a a)     --> a
   */
  if (a == true_bit) return true_bit;
  if (b == true_bit) return true_bit;
  if (a == false_bit) return b;
  if (b == false_bit) return a;
  if (a == b) return a;
  if (a == bit_not(b)) return true_bit;

  //  return get_or(table, a, b);
  return simplify_bit_or(table, a, b);
}




/*
 * Local simplification rules for (XOR a b)
 */
static bit_t simplify_bit_xor(bv_vartable_t *table, bit_t a, bit_t b) {
  thvar_t va, vb;
  bit_t a0, a1;
  bit_t b0, b1;
  aig_shape_t a_shape, b_shape;
  uint32_t sign;

  // make a and b positive, keep sign
  sign = sign_of_bit(a) ^ sign_of_bit(b);
  a &= ~1;
  b &= ~1;

  // Stop GCC warning
  a0 = null_bit;
  a1 = null_bit;
  b0 = null_bit;
  b1 = null_bit;

  // a's shape + b
  a_shape = shape_of_bit(table, a);
  va = node_of_bit(a);
  if (a_shape != AIG_ATOM) {
    assert(a_shape == AIG_POS_OR || a_shape == AIG_POS_XOR);
    a0 = table->def[va].bop[0];
    a1 = table->def[va].bop[1];
    if (a_shape == AIG_POS_XOR) {
      /*
       * (xor (xor a0 a1) a0)  --> a1
       * (xor (xor a0 a1) a1)  --> a0
       * (xor (xor a0 a1) ~a0) --> ~a1
       * (xor (xor a0 a1) ~a1) --> ~a0
       */
      if (b == a0) return sign ^ a1;
      if (b == a1) return sign ^ a0;
    }
  }

  // b's shape + a
  b_shape = shape_of_bit(table, b);
  vb = var_of_bit(b);
  if (b_shape != AIG_ATOM) {
    assert(b_shape == AIG_POS_OR || b_shape == AIG_POS_XOR);
    b0 = table->def[vb].bop[0];
    b1 = table->def[vb].bop[1];
    if (b_shape == AIG_POS_XOR) {
      /*
       * (xor b0 (xor b0 b1))  --> b1
       * (xor b1 (xor b0 b1))  --> b0
       * (xor ~b0 (xor b0 b1)) --> ~b1
       * (xor ~b1 (xor b0 b1)) --> ~b0
       */
      if (a == b0) return sign ^ b1;
      if (a == b1) return sign ^ b0;
    }
  }


  if (a_shape != AIG_ATOM && b_shape != AIG_ATOM) {
    assert(a0 == table->def[va].bop[0] && 
	   a1 == table->def[va].bop[1] && 
	   b0 == table->def[vb].bop[0] &&
	   b1 == table->def[vb].bop[1]);

    if (combine_shapes(a_shape, b_shape) == AIG_POS_OR_POS_OR ) {
      /*
       * (xor (or a0 a1) (or ~a0 a1))  --> ~a1
       * (xor (or a0 a1) (or a0 ~a1))  --> ~a0
       */
      if (opposite_bits(a0, b0) && a1 == b1) return sign ^ bit_not(a1);
      if (a0 == b0 && opposite_bits(a1, b1)) return sign ^ bit_not(a0);
    }
  }

  return sign ^ get_xor(table, a, b);
}


/*
 * Build (XOR a b): basic simplification rules
 */
static bit_t mk_bit_xor(bv_vartable_t *table, bit_t a, bit_t b) {
  /*
   * (xor true b)  --> ~b
   * (xor a true)  --> ~a
   * (xor false b) --> b
   * (xor a false) --> a
   * (xor a a)     --> false
   * (xor a ~a)    --> true
   */
  if (a == true_bit) return bit_not(b);
  if (b == true_bit) return bit_not(a);
  if (a == false_bit) return b;
  if (b == false_bit) return a;
  if (a == b) return false_bit;
  if (a == bit_not(b)) return true_bit;

  return simplify_bit_xor(table, a, b);
}


/*
 * Build (bit x)
 * - convert to a constant if x == true_bit or false_bit
 */
static thvar_t convert_bit_to_bv(bv_vartable_t *table, bit_t x) {
  if (x == true_bit) return get_small_const(table, 1, 1);
  if (x == false_bit) return get_small_const(table, 1, 0);

  return get_bit(table, x);
}


/*
 * Check whether all bits a[0] ... a[n-1] are constant
 */
static bool bitarray_is_constant(uint32_t n, bit_t *a) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (var_of_bit(a[i]) != constant_node) {
      return false;
    }
  }
  return true;
}

/*
 * Convert constant array a[0] ... a[n-1] to a 64bit unsigned integer
 * - a[0] = lowest-order bit of the result
 * - a[n-1] = highest-order bit of the result
 */
static uint64_t bitarray_to_uint64(uint32_t n, bit_t *a) {
  uint64_t c;

  assert(1 <= n && n <= 64);

  c = 0;
  while (n > 0) {
    n --;
    assert(a[n] == true_bit || a[n] == false_bit);
    c = (c << 1) | bit_const_value(a[n]);
  }
  return c;
}

/*
 * Convert constant array a[0] ... a[n-1] to a bit-vector constant
 * - the result is stored into c
 */
static void bitarray_to_bvconstant(uint32_t n, bit_t *a, bvconstant_t *c) {
  uint32_t i, k;

  assert(n > 64);
  k = (n + 31) >> 5;

  bvconstant_set_bitsize(c, n);
  bvconst_clear(c->data, k);
  for (i=0; i<n; i++) {
    assert(a[i] == true_bit || a[i] == false_bit);
    if (a[i] == true_bit) {
      bvconst_set_bit(c->data, i);
    }
  }
}


/*
 * Build (bitarray a[0] ... a[n-1])
 * - convert to a constant if all bits are true or false
 */
static thvar_t convert_bitarray_to_bv(bv_solver_t *solver, uint32_t n, bit_t *a) {
  bv_vartable_t *vtbl;
  thvar_t y;
  uint64_t c;

  vtbl = &solver->vtbl;
  if (bitarray_is_constant(n, a)) {
    if (n <= 64) {
      c = bitarray_to_uint64(n, a);
      y = get_small_const(vtbl, n, c);
    } else {
      bitarray_to_bvconstant(n, a, &solver->aux1);
      y = get_big_const(vtbl, n, solver->aux1.data);
    }
  } else {
    y = get_bit_array(vtbl, n, a);
  }

  return y;
}



/*
 * Convert variable node x to a bit_select
 * - bv_map = renaming of bit-vector variables
 */
static bit_t bv_solver_map_var_node(bv_solver_t *solver, node_t x, itable_t *bv_map) {
  bv_vartable_t *vtbl;
  node_table_t *nodes;  
  int32_t u, k;
  thvar_t y;

  nodes = solver->nodes;
  u = bv_var_of_node(nodes, x);  // u := bit-vector variable for x in the external tables
  k = bv_var_manager_get_index_of_node(solver->bv_manager, u, pos_bit(x)); // index of x in vector u
  y = itable_get(bv_map, u);   // y := what u is renamed to internally
  
  /*
   * Build select(k, y):
   * - if y is a constant return bit k of y
   * - if y is (bitarray ... b_k ...) return b_k
   * - otherwise, build a new select node
   */
  vtbl = &solver->vtbl;
  assert(valid_bvvar(vtbl, y) && 0 <= k && k < bvvar_bitsize(vtbl, y));

  switch (bvvar_tag(vtbl, y)) {
  case BVTAG_SMALL_CONST:
    if (tst_bit64(vtbl->def[y].ival, k)) {
      return true_bit;
    } else {
      return false_bit;
    }

  case BVTAG_BIG_CONST:
    if (bvconst_tst_bit(vtbl->def[y].pval, k)) {
      return true_bit;
    } else {
      return false_bit;
    }

  case BVTAG_BIT_ARRAY:
    return vtbl->def[y].bit[k];

  default:
    return pos_bit(get_select(vtbl, k, y));
  }
}

/*
 * Convert external bit a to an internal bit
 * - bv_map = variable renaming 
 */
static bit_t bv_solver_map_bit(bv_solver_t *solver, bit_t a, itable_t *bv_map);  


/*
 * Internalize node x to a bit y
 * - x must be a valid node in solver->nodes
 * - bv_map: variable renaming: all variable reachables from
 *   node x must have a mapping in bv_map 
 * - store the mapping [x --> y] into the internal node_map
 */
static bit_t bv_solver_map_node(bv_solver_t *solver, node_t x, itable_t *bv_map) {
  node_table_t *nodes;  
  bit_t y, z;

  nodes = solver->nodes;
  assert(good_node(nodes, x));

  y = itable_get(&solver->node_map, x);
  if (y == nil) {
    // x not internalized yet
    switch (node_kind(nodes, x)) {
    case CONSTANT_NODE:
      y = var_of_bit(true_bit);
      break;

    case VARIABLE_NODE:
      y = bv_solver_map_var_node(solver, x, bv_map);
      break;

    case OR_NODE:
      y = bv_solver_map_bit(solver, left_child_of_node(nodes, x), bv_map);
      z = bv_solver_map_bit(solver, right_child_of_node(nodes, x), bv_map);
      y = mk_bit_or(&solver->vtbl, y, z);
      break;

    case XOR_NODE:
      y = bv_solver_map_bit(solver, left_child_of_node(nodes, x), bv_map);
      z = bv_solver_map_bit(solver, right_child_of_node(nodes, x), bv_map);
      y = mk_bit_xor(&solver->vtbl, y, z);
      break;

    default:
      assert(false);
      break;
    }

    // store mapping [x --> y] in node_map
    itable_map(&solver->node_map, x, y);
  }
  
  return y;
}


/*
 * Convert bit to bit
 */
static bit_t bv_solver_map_bit(bv_solver_t *solver, bit_t a, itable_t *bv_map) {
  bit_t y;

  // y := internalize node of a
  y = bv_solver_map_node(solver, var_of_bit(a), bv_map);

  // if a has positive sign, return y otherwise return not(a)
  return y ^ sign_of_bit(a);
}



/*
 * Convert a bit array
 * - bv_map = variable substitution
 * - all variables of p must occur in bv_map (and be mapped to a valid
 *   internal variable)
 */
static thvar_t bv_solver_map_bitarray(bv_solver_t *solver, bvlogic_expr_t *p, itable_t *bv_map) {
  ivector_t *v;
  uint32_t i, n;
  bit_t x;
  thvar_t y;

  n = p->nbits;
  assert(n > 0);

  if (n == 1) {
    x = bv_solver_map_bit(solver, p->bit[0], bv_map);
    y = convert_bit_to_bv(&solver->vtbl, x);
  } else {
    v = &solver->aux_vector;
    assert(v->size == 0);

    for (i=0; i<n; i++) {
      x = bv_solver_map_bit(solver, p->bit[i], bv_map);
      ivector_push(v, x);
    }

    assert(v->size == n);
    y = convert_bitarray_to_bv(solver, n, v->data);
    ivector_reset(v);
  }

  return y;
}



/*****************************************************
 *  MAPPING OF PSEUDO LITERAL (ARRAYS) TO CONSTANTS  *
 ****************************************************/

/*
 * Pseudo literal for a one-bit bit-vector constant 
 * - c = constant value (should be either 0 or 1)
 */
static inline literal_t map_bit1_const(uint64_t c) {
  if (c == 0) {
    return false_literal;
  } else {
    assert(c == 1);
    return true_literal;
  }
}


/*
 * Array of pseudo literals for an n-bit constant (with n <= 64)
 * - c = constant value
 */
static literal_t *map_small_const(uint64_t c, uint32_t n) {
  literal_t *a;
  uint32_t i;

  assert(1 < n && n <= 64);
  a = (literal_t *) safe_malloc(n * sizeof(literal_t));

  for (i=0; i<n; i++) {
    if ((c & 1) == 0) {
      a[i] = false_literal;
    } else {
      a[i] = true_literal;
    }
    c >>= 1;
  }
  return a;
}


/*
 * Same thing for n > 64
 * - c = constant as an array of 32-bit words
 */
static literal_t *map_big_const(uint32_t *c, uint32_t n) {
  literal_t *a;
  uint32_t i;

  assert(n > 64);
  a = (literal_t *) safe_malloc(n * sizeof(literal_t));

  for (i=0; i<n; i++) {
    if (bvconst_tst_bit(c, i)) {
      a[i] = true_literal;
    } else {
      a[i] = false_literal;
    }
  }

  return a;
}





/*********************************
 *  EQUALITY/DISEQUALITY CHECKS  *
 ********************************/

/*
 * Check whether x and y are known to be equal 
 * (i.e., x == y or they are in the same equivalence class)
 */
static bool bv_solver_check_eq(bv_solver_t *solver, thvar_t x, thvar_t y) {
  assert(bvvar_bitsize(&solver->vtbl, x) == bvvar_bitsize(&solver->vtbl, y));

  x = bv_partition_get_root(&solver->partition, x);
  y = bv_partition_get_root(&solver->partition, y);
  return x == y;
}


/*
 * Check whether bit arrays a and b of size n must differ:
 * - i.e., there's an index i such that a[i] = not b[i]
 */
static bool diseq_bitarrays(bit_t *a, bit_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (opposite_bits(a[i], b[i])) {
      return true;
    }
  }
  return false;
}


/*
 * Check whether bit array a and small constant c must differ
 * - n = number of bits in a and c
 */
static bool diseq_bitarray_small_const(bit_t *a, uint64_t c, uint32_t n) {
  uint32_t i;

  assert(n <= 64);

  /*
   * HACK: we use the fact that true_bit = 0 and false_bit = 1
   * So (bit i of c) == a[i] implies a != c
   */
  assert(true_bit == 0 && false_bit == 1);
  
  for (i=0; i<n; i++) {
    if (((int32_t) (c & 1)) == a[i]) {
      return true;
    }
    c >>= 1;
  }

  return false;
}


/*
 * Check whether bit array a and large constant c must differ
 * - n = number of bits of a and c
 */
static bool diseq_bitarray_big_const(bit_t *a, uint32_t *c, uint32_t n) {
  uint32_t i;

  // Same HACK as above
  assert(true_bit == 0 && false_bit == 1);

  for (i=0; i<n; i++) {
    if (bvconst_tst_bit(c, i) == a[i]) {
      return true;
    }
  }
  
  return false;
}




 
/*
 * Check whether x is different from constant c
 * - depth = recursion limit. 
 *
 * There's nothing to prevent cycles in the substitutions/partition
 * tables. To stop infinite recursion, we return false if depth = 0.
 */
static bool diseq_var_small_const(bv_solver_t *solver, thvar_t x, uint64_t c, uint32_t depth) {
  bv_vartable_t *vtbl;
  thvar_t t, u;
  uint32_t n;

  if (depth > 0) {
    vtbl = &solver->vtbl;
    n = bvvar_bitsize(vtbl, x);
    assert(n <= 64 && (c & ~mask64(n)) == 0);

    // replace x by its root if any
    x = bv_partition_get_root(&solver->partition, x);

    switch (bvvar_tag(vtbl, x)) {
    case BVTAG_SMALL_CONST:
      assert((vtbl->def[x].ival & ~mask64(n)) == 0);
      return vtbl->def[x].ival != c;

    case BVTAG_BIT_ARRAY:
      return diseq_bitarray_small_const(vtbl->def[x].bit, c, n);

    case BVTAG_ADD:
      // x is (add t u)
      t = vtbl->def[x].op[0];
      u = vtbl->def[x].op[1];
      if (bvvar_is_small_const(vtbl, t)) {
	// (add t u) /= c iff u /= (c - t)
	c -= vtbl->def[t].ival;
	c &= mask64(n);
	return diseq_var_small_const(solver, u, c, depth-1);
      }
      if (bvvar_is_small_const(vtbl, u)) {
	// (add t u) /= c iff t /= (c - u)
	c -= vtbl->def[u].ival;
	c &= mask64(n);
	return diseq_var_small_const(solver, t, c, depth-1);
      }
      break;
    
    case BVTAG_SUB:
      // x is (sub t u)
      t = vtbl->def[x].op[0];
      u = vtbl->def[x].op[1];
      if (bvvar_is_small_const(vtbl, t)) {
	// (sub t u) /= c iff u /= (t - c)
	c = vtbl->def[t].ival - c;
	c &= mask64(n);
	return diseq_var_small_const(solver, u, c, depth-1);
      }
      if (bvvar_is_small_const(vtbl, u)) {
	// (sub t u) /= c iff t /= (c + u)
	c += vtbl->def[u].ival;
	c &= mask64(n);
	return diseq_var_small_const(solver, t, c, depth-1);
      }
      break;

    case BVTAG_NEG:
      // (neg t) != c iff t != -c
      t = vtbl->def[x].op[0];
      c = -c;
      c &= mask64(n);
      return diseq_var_small_const(solver, t, c, depth-1);

    default:
      break;
    }
  }

  return false;
}


static bool diseq_var_big_const(bv_solver_t *solver, thvar_t x, uint32_t *c) {
  bv_vartable_t *vtbl;
  uint32_t n;
  uint32_t w;

  vtbl = &solver->vtbl;
  n = bvvar_bitsize(vtbl, x);
  assert(n > 64);

  // replace x by its root if any
  x = bv_partition_get_root(&solver->partition, x);

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_BIG_CONST:
    w = (n + 31) >> 5;
    return bvconst_neq(vtbl->def[x].pval, c, w);

  case BVTAG_BIT_ARRAY:
    return diseq_bitarray_big_const(vtbl->def[x].bit, c, n);

  default:
    return false;
  }
}





/*
 * Check whether x and y are distinct (partial check)
 * - depth = limit on recursion depth (to prevent loops)
 */
static bool bv_solver_check_diseq_recur(bv_solver_t *solver, thvar_t x, thvar_t y, uint32_t depth);

/*
 * Check whether x and y differ when x = (bvadd t u) and y = (bvadd v w)
 * Rules:
 *  (bvadd t u) /= (bvadd t w) iff u /= w
 *  (bvadd t u) /= (bvadd v t) iff u /= v
 *  (bvadd t u) /= (bvadd v u) iff t /= v
 *  (bvadd t u) /= (bvadd u w) iff t /= w
 */
static bool diseq_bvadd(bv_solver_t *solver, thvar_t x, thvar_t y, uint32_t depth) {
  bv_vartable_t *vtbl;
  thvar_t t, u, v, w;

  assert(depth > 0);
  
  vtbl = &solver->vtbl;
  assert(bvvar_tag(vtbl, x) == BVTAG_ADD && bvvar_tag(vtbl, y) == BVTAG_ADD);

  t = vtbl->def[x].op[0];
  u = vtbl->def[x].op[1];
  v = vtbl->def[y].op[0];
  w = vtbl->def[y].op[1];

  if (t == v) return bv_solver_check_diseq_recur(solver, u, w, depth-1);
  if (t == w) return bv_solver_check_diseq_recur(solver, u, v, depth-1);
  if (u == v) return bv_solver_check_diseq_recur(solver, t, w, depth-1);
  if (u == w) return bv_solver_check_diseq_recur(solver, t, v, depth-1);

  return false;
}



/*
 * Check whether x and y differ when x = (bvsub t u) and y = (bvsub v w)
 * Rules:
 *  (bvsub t u) /= (bvsub t w) iff u /= w
 *  (bvsub t u) /= (bvsub v u) iff v /= t
 */
static bool diseq_bvsub(bv_solver_t *solver, thvar_t x, thvar_t y, uint32_t depth) {
  bv_vartable_t *vtbl;
  thvar_t t, u, v, w;

  assert(depth > 0);

  vtbl = &solver->vtbl;
  assert(bvvar_tag(vtbl, x) == BVTAG_SUB && bvvar_tag(vtbl, y) == BVTAG_SUB);

  t = vtbl->def[x].op[0];
  u = vtbl->def[x].op[1];
  v = vtbl->def[y].op[0];
  w = vtbl->def[y].op[1];

  if (t == v) return bv_solver_check_diseq_recur(solver, u, w, depth-1);
  if (u == w) return bv_solver_check_diseq_recur(solver, t, v, depth-1);

  return false;
}


/*
 * (bvneg u) /= (bvneg v) iff u /= v
 */
static bool diseq_bvneg(bv_solver_t *solver, thvar_t x, thvar_t y, uint32_t depth) {
  bv_vartable_t *vtbl;

  assert(depth > 0);

  vtbl = &solver->vtbl;
  assert(bvvar_tag(vtbl, x) == BVTAG_NEG && bvvar_tag(vtbl, y) == BVTAG_NEG);
  return bv_solver_check_diseq_recur(solver, vtbl->def[x].op[0], vtbl->def[y].op[0], depth-1);
}



/*
 * Check whether x and y are known to be distinct.
 * - right now, this deals with simple cases
 * - depth = recursion limit. If depth == 0, the function returns false
 */
static bool bv_solver_check_diseq_recur(bv_solver_t *solver, thvar_t x, thvar_t y, uint32_t depth) {
  bv_vartable_t *vtbl;
  bvvar_tag_t xtag, ytag;
  uint32_t n;

  if (depth > 0) {
    vtbl = &solver->vtbl;
    n = bvvar_bitsize(vtbl, x);
    assert(bvvar_bitsize(vtbl, y) == n);

    /*
     * Replace x and y by their class root if any
     * NOTE: not sure this actually helps.
     */
    x = bv_partition_get_root(&solver->partition, x);
    y = bv_partition_get_root(&solver->partition, y);
    
    xtag = bvvar_tag(vtbl, x);
    ytag = bvvar_tag(vtbl, y);

    /*
     * Comparison with small or big constants
     */
    if (xtag == BVTAG_SMALL_CONST) {
      return diseq_var_small_const(solver, y, vtbl->def[x].ival, depth);
      
    } else if (ytag == BVTAG_SMALL_CONST) {
      return diseq_var_small_const(solver, x, vtbl->def[y].ival, depth);

    } else if (xtag == BVTAG_BIG_CONST) {
      return diseq_var_big_const(solver, y, vtbl->def[x].pval);

    } else if (ytag == BVTAG_BIG_CONST) {
      return diseq_var_big_const(solver, x, vtbl->def[y].pval);

    } else if (xtag == ytag) {
      /*
       * homogeneous comparison: x and y have the same tag
       * neither is a constant
       */
      switch (xtag) {
      case BVTAG_BIT:
	return opposite_bits(vtbl->def[x].bval, vtbl->def[y].bval);
      case BVTAG_BIT_ARRAY:
	return diseq_bitarrays(vtbl->def[x].bit, vtbl->def[y].bit, n);
      case BVTAG_ADD:
	return diseq_bvadd(solver, x, y, depth);
      case BVTAG_SUB:
	return diseq_bvsub(solver, x, y, depth);
      case BVTAG_NEG:
	return diseq_bvneg(solver, x, y, depth);
      default:
	break;
      }
    }
  } 

  return false;

}



/*
 * Top-level: use depth = 4
 */
static bool bv_solver_check_diseq(bv_solver_t *solver, thvar_t x, thvar_t y) {
  return bv_solver_check_diseq_recur(solver, x, y, 4);
}




/************************************* 
 *  SIMPLIFICATION OF EQUALITY ATOM  *
 ************************************/

/*
 * Given two bitvector variables x and y, we can try to find 
 * x' and y' such that (bveq x y) <==> (bveq x' y') and x' and y'
 * are simpler than x and y.
 *
 * For this, we apply rules similar to what we use in check_diseq:
 *   (bveq (bvadd x y) (bvadd x z)) <==> (bveq y z)
 *   (bveq (bvsub x y) (bvsub x z)) <==> (bveq y z)
 *   (bveq (bvsub x y) (bvsub z y)) <==> (bveq x z)
 *   (bveq (bvneg x) (bvneg y)) <==> (bveq x y)
 * 
 * Rules to deal with constants:
 *   (bveq (bvadd x a) b) <==> (bveq x (bvsub b a))
 *   (bveq (bvsub x a) b) <==> (bveq x (bvadd a b))
 *   (bveq (bvsub a x) b) <==> (bveq x (bvsub a b))
 *   (bveq (bvneg x) a) <==> (bveq x (bvneg a))
 * where a and b are constants.
 */

/*
 * Rewrite equality (x == c) to (x' == c') where x' is simpler than x
 * - on input x is stored in *vx and c is in *vc
 * - on exit x' is stored in *vx and c' is in *vc
 */
static void simplify_eq_var_small_const(bv_solver_t *solver, thvar_t *vx, uint64_t *vc) {
  bv_vartable_t *vtbl;
  thvar_t x, t, u;
  uint64_t c;
  uint32_t n, depth;
  bool changed;

  depth = 4; // to prevent infinite loop
  x = *vx; 
  c = *vc;
  vtbl = &solver->vtbl;
  n = bvvar_bitsize(vtbl, x);
  assert(n <= 64 && (c & ~mask64(n)) == 0);

  do {

    changed = false;
    x = bv_partition_get_root(&solver->partition, x);

    switch (bvvar_tag(vtbl, x)) {
    case BVTAG_ADD:
      // x is (add t u)
      t = vtbl->def[x].op[0];
      u = vtbl->def[x].op[1];
      if (bvvar_is_small_const(vtbl, t)) {
	// (add t u) == c iff u == (c - t)
	c -= vtbl->def[t].ival;
	x = u;
	changed = true;
      } else if (bvvar_is_small_const(vtbl, u)) {
	// (add t u) == c iff t == (c - u)
	c -= vtbl->def[u].ival;
	x = t;
	changed = true;
      }
      break;

    case BVTAG_SUB:
      // x is (sub t u)
      t = vtbl->def[x].op[0];
      u = vtbl->def[x].op[1];
      if (bvvar_is_small_const(vtbl, t)) {
	// (sub t u) == c iff u == (t - c)
	c = vtbl->def[t].ival - c;
	x = u;
	changed = true;
      } else if (bvvar_is_small_const(vtbl, u)) {
	// (sub t u) == c iff t == (c + u)
	c += vtbl->def[u].ival;
	x = t;
	changed = true;
      }
      break;

    case BVTAG_NEG:
      // (neg t) == c iff t == -c
      c = - c;
      x = vtbl->def[x].op[0];
      changed = true;
      break;

    default:
      break;
    }

    depth --;
  } while (depth > 0 && changed);

  *vx = x;
  *vc = c & mask64(n);
}


/*
 * Simplify (x == y) to (x' == y') when x and y are (bvadd ..)
 * - on input *vx = x and *vy = y
 * - on exit, x' is copied into *vx and y' is copied into *vy
 * - return true if a simplification was applied
 * - return false otherwise (i.e., x and y are not changed)
 */
static bool simplify_eq_bvadd(bv_solver_t *solver, thvar_t *vx, thvar_t *vy) {
  bv_vartable_t *vtbl;
  thvar_t x, y, t, u, v, w;
  bool changed;

  vtbl = &solver->vtbl;
  assert(bvvar_tag(vtbl, *vx) == BVTAG_ADD && bvvar_tag(vtbl, *vy) == BVTAG_ADD);

  x = *vx;
  t = vtbl->def[x].op[0];
  u = vtbl->def[x].op[1];
  y = *vy;
  v = vtbl->def[y].op[0];
  w = vtbl->def[y].op[1];

  changed = false;

  // x is (add t u)
  // y is (add v w)
  if (t == v) {
    *vx = u;
    *vy = w;
    changed = true;
  } else if (t == w) {
    *vx = u;
    *vy = v;
    changed = true;
  } else if (u == v) {
    *vx = t;
    *vy = w;
    changed = true;
  } else if (u == w) {
    *vx = t;
    *vy = v;
    changed = true;
  }

  return changed;
}


/*
 * Simplify (x == y) to (x' == y') when both x and y are (bvsub ...)
 * - on input *vx = x and *vy = y
 * - on exit, x' is copied into *vx and y' is copied into *vy
 * - return true if a simplification was applied
 * - return false if nothing changed
 */
static bool simplify_eq_bvsub(bv_solver_t *solver, thvar_t *vx, thvar_t *vy) {
  bv_vartable_t *vtbl;
  thvar_t x, y, t, u, v, w;
  bool changed;

  vtbl = &solver->vtbl;
  assert(bvvar_tag(vtbl, *vx) == BVTAG_SUB && bvvar_tag(vtbl, *vy) == BVTAG_SUB);

  x = *vx;
  t = vtbl->def[x].op[0];
  u = vtbl->def[x].op[1];
  y = *vy;
  v = vtbl->def[y].op[0];
  w = vtbl->def[y].op[1];

  changed = false;

  // x is (sub t u)
  // y is (sub v w)
  if (t == v) {
    *vx = u;
    *vy = w;
    changed = true;
  } else if (u == w) {
    *vx = t;
    *vy = v;
    changed = true;
  }

  return changed;
}


/*
 * Simplify (x == y) to (x' == y') when both x and y are (bvneg ..)
 * - on input *vx = x and *vy = y
 * - on exit, x' is copied into *vx and y' is copied into *vy
 * - the simplification is always applied
 */
static void simplify_eq_bvneg(bv_solver_t *solver, thvar_t *vx, thvar_t *vy) {
  bv_vartable_t *vtbl;

  vtbl = &solver->vtbl;
  assert(bvvar_tag(vtbl, *vx) == BVTAG_NEG && bvvar_tag(vtbl, *vy) == BVTAG_NEG);
  *vx = vtbl->def[*vx].op[0];
  *vy = vtbl->def[*vy].op[0];
}


/*
 * Create a new bitvector constant on the fly
 * - if the constant is created after bitblasting
 *   we attach an array of pseudo literals to the new constant
 * - n = bit size
 * - c = constant value
 */
static thvar_t get_small_const2(bv_solver_t *solver, uint32_t n, uint64_t c) {
  bv_vartable_t *vtbl;
  thvar_t x;

  vtbl = &solver->vtbl;
  x = get_small_const(vtbl, n, c);
  assert(vtbl->bit_size[x] == n);
  if (solver->bit_blasted && !bvvar_is_mapped(vtbl, x)) {
    if (n == 1) {
      // assign pseudo-literal to x
      vtbl->map[x].lit = map_bit1_const(c);
    } else {
      // assign pseudo-literal array
      vtbl->map[x].array = map_small_const(c, n); 
    }
  }

  return x;
}


/*
 * Search for x' and y' such that (bveq x' y') is the simplified
 * form of (bveq x y).
 *
 * This should be called after 'check_diseq' and 'check_eq'.
 * - on input x and y must be stored in *vx and *vy
 * - on exit x' and y' are stored in *vx and *vy
 */
static void bv_solver_simplify_eq(bv_solver_t *solver, thvar_t *vx, thvar_t *vy) {
  bv_vartable_t *vtbl;
  bvvar_tag_t xtag, ytag;
  thvar_t x, y, z;
  uint32_t n, depth;
  uint64_t c;
  bool iterate;

  depth = 4; // put a bound to prevent infinite loop
  vtbl = &solver->vtbl;
  x = *vx;
  y = *vy;
  n = bvvar_bitsize(vtbl, x);
  assert(n == bvvar_bitsize(vtbl, y));

#if TRACE
  printf("---> bv simplify (bveq u_%"PRId32" u_%"PRId32")\n", x, y);
  printf("     ");
  print_bvsolver_vardef(stdout, solver, x);
  printf("     ");
  print_bvsolver_vardef(stdout, solver, y);
#endif

  do {
    // replace x and y by their root
    x = bv_partition_get_root(&solver->partition, x);
    y = bv_partition_get_root(&solver->partition, y);

    // flag: if true we'll keep iterating
    iterate = false;

    xtag = bvvar_tag(vtbl, x);
    ytag = bvvar_tag(vtbl, y);

    if (xtag == BVTAG_SMALL_CONST) {
      c = vtbl->def[x].ival;
      z = y;
      simplify_eq_var_small_const(solver, &z, &c);
      if (z != y) {
	x = get_small_const2(solver, n, c);
	y = z;
      }

    } else if (ytag == BVTAG_SMALL_CONST) {
      c = vtbl->def[y].ival;
      z = x;
      simplify_eq_var_small_const(solver, &z, &c);
      if (z != x) {
	x = z;
	y = get_small_const2(solver, n, c);
      }
      
    } else if (xtag == ytag) {
      switch (xtag) {
      case BVTAG_ADD:
	iterate = simplify_eq_bvadd(solver, &x, &y);
	break;

      case BVTAG_SUB:
	iterate = simplify_eq_bvsub(solver, &x, &y);
	break;

      case BVTAG_NEG:
	simplify_eq_bvneg(solver, &x, &y);
	iterate = true;
	break;

      default:
	break;
      }
    }

    depth --;
  } while (depth > 0 && iterate);

  // done: copy the result
  *vx = x;
  *vy = y;

#if TRACE
  printf("---> simplified to (bveq u_%"PRId32" u_%"PRId32")\n", x, y);
  printf("     ");
  print_bvsolver_vardef(stdout, solver, x);
  printf("     ");
  print_bvsolver_vardef(stdout, solver, y);
#endif
}




/*
 * More simplifications for (bveq x y):
 * (bveq (ite c a b) a) ---> c if a must differ from b
 * (bveq (ite c a b) b) ---> not c if must differ from b
 */

/*
 * Try the rules on ite = (ite c a b) and u
 * - return c or (not c) is one of these rules apply
 * - return null_literal ohterwise
 */
static literal_t check_simplify_eq_ite(bv_solver_t *solver, bv_ite_t *ite, thvar_t u) {
  if (bv_solver_check_eq(solver, ite->left, u) &&
      bv_solver_check_diseq(solver, ite->right, u)) {
    // (a == u) and (b != u) so (bveq (ite c a b) u) ---> c
    return ite->cond;
  }
  if (bv_solver_check_eq(solver, ite->right, u) &&
      bv_solver_check_diseq(solver, ite->left, u)) {
    return not(ite->cond);
  }
  return null_literal;
}

static literal_t bv_solver_simplify_eq_ite(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  literal_t c;

  c = null_literal;
  vtbl = &solver->vtbl;  
  if (bvvar_tag(vtbl, x) == BVTAG_ITE) {
    c = check_simplify_eq_ite(solver, vtbl->def[x].ite, y);
    if (c != null_literal) return c;
  }

  if (bvvar_tag(vtbl, y) == BVTAG_ITE) {
    c = check_simplify_eq_ite(solver, vtbl->def[y].ite, x);
  }

  return c;
}




/**************************
 *  BOOLEAN PROPAGATION   *
 *************************/

/*
 * Return the internal queue.
 * - allocate and initialize it if needed
 * - make sure the 'true' variable has value true in the queue
 */
static bv_prop_queue_t *bv_solver_get_queue(bv_solver_t *solver) {
  bv_prop_queue_t *tmp;

  tmp = solver->queue;
  if (tmp == NULL) {
    tmp = (bv_prop_queue_t *) safe_malloc(sizeof(bv_prop_queue_t));
    init_bv_prop_queue(tmp);
    bv_prop_queue_assign(tmp, constant_node, VAL_TRUE);
    solver->queue = tmp;
  }

  return tmp;
}


/*
 * Record that bit b is true
 * - attach the correct truth-value to var_of(b) 
 * - and add var_of(b) to the propagation queue.
 * - if var_of(b) already has a truth-assignmemt, check for conflict
 */
static void bv_solver_propagate_true_bit(bv_solver_t *solver, bit_t b) {
  bv_vartable_t *vtbl;
  bv_prop_queue_t *queue;
  thvar_t x;
  bval_t v1, v0;
 
  vtbl = &solver->vtbl;
  assert(valid_bit(vtbl, b));

  x = var_of_bit(b);
  v1 = VAL_TRUE;
  if (is_neg(b)) {
    v1 = VAL_FALSE;
  }

  // v1 is the propagated truth value for x
  // v0 = current truth value
  queue = bv_solver_get_queue(solver);
  v0 = bv_prop_queue_get_val(queue, x);
  switch (v0) {
  case VAL_TRUE:
  case VAL_FALSE:
    if (v0 != v1) {
      // conflict
      add_empty_clause(solver->core);
      queue->unsat = true;
#if TRACE
      printf("---> bv_solver: boolean propagation: ");
      print_bvsolver_var(stdout, x);
      printf(" := ");
      print_bval(stdout, v1);
      printf("\n");
      printf("---> CONFLICT\n");
      fflush(stdout);
#endif

    }
    break;

  case VAL_UNDEF:
    bv_prop_queue_assign(queue, x, v1);
    bv_prop_queue_push(queue, x);

#if TRACE
    printf("---> bv_solver: boolean propagation: ");
    print_bvsolver_var(stdout, x);
    printf(" := ");
    print_bval(stdout, v1);
    printf("\n");
    fflush(stdout);
#endif
    break;
  }
}


/*
 * Record that b is false
 */
static inline void bv_solver_propagate_false_bit(bv_solver_t *solver, bit_t b) {
  bv_solver_propagate_true_bit(solver, not(b));
}


/*
 * Check for propagation after (x == y)
 * when y is a small constant
 */
static void check_bit_prop_small_const(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bv_ite_t *ite;
  uint64_t vy;
  uint32_t i, n;
  bit_t b;

  vtbl = &solver->vtbl;

  assert(bvvar_tag(vtbl, y) == BVTAG_SMALL_CONST && 
	 bvvar_bitsize(vtbl, x) == bvvar_bitsize(vtbl, y));

  vy = vtbl->def[y].ival;

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_BIT:
    b = vtbl->def[x].bval;
    assert(vy <= 1);
    if (vy == 0) {
      b = not(b);
    }
    bv_solver_propagate_true_bit(solver, b);
    break;

  case BVTAG_BIT_ARRAY:
    n = bvvar_bitsize(vtbl, x);
    for (i=0; i<n; i++) {
      b = vtbl->def[x].bit[i];
      if (! tst_bit64(vy, i)) { // bit i of vy is 0
	b = not(b); // b := 0
      }
      bv_solver_propagate_true_bit(solver, b);
    }
    break;

  case BVTAG_ITE:    
    ite = vtbl->def[x].ite;
    /*
     * (ite p left right) == yy has just been asserted
     * if left can't be equal to vy, then p must be false.
     * if right can't be equal to vy, then p must be true.
     * 
     */
    assert(solver->base_level == solver->decision_level);
    if (diseq_var_small_const(solver, ite->left, vy, 4)) {  // 4 = recursion limit
      add_unit_clause(solver->core, not(ite->cond)); // p := false
#if TRACE
      printf("---> bv_solver: implied literal ");
      print_literal(stdout, not(ite->cond));
      printf("\n");
#endif
    }
    if (diseq_var_small_const(solver, ite->right, vy, 4)) {  // 4 = recursion limit
      add_unit_clause(solver->core, ite->cond);  // p := true
#if TRACE
      printf("---> bv_solver: implied literal ");
      print_literal(stdout, ite->cond);
      printf("\n");
#endif
    }
    break;

  default:
    break;
  }
}



/*
 * Check for propagation after (x == y)
 * when y is a bit constant
 */
static void check_bit_prop_big_const(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bv_ite_t *ite;  
  uint32_t *vy;
  uint32_t i, n;
  bit_t b;

  vtbl = &solver->vtbl;

  assert(bvvar_tag(vtbl, y) == BVTAG_BIG_CONST && 
	 bvvar_bitsize(vtbl, x) == bvvar_bitsize(vtbl, y));

  vy = vtbl->def[y].pval;

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_BIT_ARRAY:
    n = bvvar_bitsize(vtbl, x);
    for (i=0; i<n; i++) {
      b = vtbl->def[x].bit[i];
      if (! bvconst_tst_bit(vy, i)) {
	b = not(b);
      }
      bv_solver_propagate_true_bit(solver, b);
    }
    break;

  case BVTAG_ITE:
    ite = vtbl->def[x].ite;
    /*
     * (ite p left right) == yy has just been asserted
     * if left can't be equal to vy, then p must be false.
     * if right can't be equal to vy, then p must be true.
     * 
     */
    assert(solver->base_level == solver->decision_level);
    if (diseq_var_big_const(solver, ite->left, vy)) {
      add_unit_clause(solver->core, not(ite->cond)); // p := false
#if TRACE
      printf("---> bv_solver: implied literal ");
      print_literal(stdout, not(ite->cond));
      printf("\n");
#endif
    }
    if (diseq_var_big_const(solver, ite->right, vy)) {
      add_unit_clause(solver->core, ite->cond);  // p := true
#if TRACE
      printf("---> bv_solver: implied literal ");
      print_literal(stdout, ite->cond);
      printf("\n");
#endif
    }
    break;

  default:
    break;
  }
  
}


/*
 * Check whether the top-level equality (x == y) can trigger
 * propagation. If so add the propagated bits into the queue.
 */
static void check_bit_propagation(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvvar_tag_t xtag, ytag;

  assert(bv_partition_get_root(&solver->partition, x) == 
	 bv_partition_get_root(&solver->partition, y));

  vtbl = &solver->vtbl;
  xtag = bvvar_tag(vtbl, x);
  ytag = bvvar_tag(vtbl, y);

  if (xtag == BVTAG_SMALL_CONST) {
    check_bit_prop_small_const(solver, y, x);
  } else if (xtag == BVTAG_BIG_CONST) {
    check_bit_prop_big_const(solver, y, x);
  } else if (ytag == BVTAG_SMALL_CONST) {
    check_bit_prop_small_const(solver, x, y);
  } else if (ytag == BVTAG_BIG_CONST) {
    check_bit_prop_big_const(solver, x, y);
  }  
}





/*
 * Get the truth value of bit i of variable x
 * - return VAL_UNDEF if the value is unknown
 */
static bval_t get_bit_value(bv_solver_t *solver, thvar_t x, uint32_t i) {
  bv_vartable_t *vtbl;
  bval_t v;

  x = bv_partition_get_root(&solver->partition, x);
  vtbl = &solver->vtbl;
  assert(valid_bvvar(vtbl, x) && i < bvvar_bitsize(vtbl, x));

  v = VAL_UNDEF;

  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_SMALL_CONST:
    v = VAL_FALSE;
    if (tst_bit64(vtbl->def[x].ival, i)) {
      v = VAL_TRUE;
    }
    break;

  case BVTAG_BIG_CONST:
    v = VAL_FALSE;
    if (bvconst_tst_bit(vtbl->def[x].pval, i)) {
      v = VAL_TRUE;
    }
    break;

  case BVTAG_BIT_ARRAY:
    v = bv_prop_queue_get_bit_val(solver->queue, vtbl->def[x].bit[i]);
    break;

  case BVTAG_BIT:
    assert(i == 0);
    v =  bv_prop_queue_get_bit_val(solver->queue, vtbl->def[x].bval);
    break;

  default:
    break;
  }

  return v;
}


/*
 * Check whether we can propagate c or not c, when 
 * bit i of (ite c left right) is set to v = true or false. 
 */
static void check_ite_bit_prop(bv_solver_t *solver, bv_ite_t *ite, uint32_t i, bval_t v) {
  bval_t v0;

  assert(v != VAL_UNDEF);

  v0 = get_bit_value(solver, ite->left, i);
  if (v0 != v && v0 != VAL_UNDEF) {
    // c must be false
    add_unit_clause(solver->core, not(ite->cond));
#if TRACE
    printf("---> bv_solver: implied literal ");
    print_literal(stdout, not(ite->cond));
    printf("\n");
#endif
  }

  v0 = get_bit_value(solver, ite->right, i);
  if (v0 != v && v0 != VAL_UNDEF) {
    // c must be true
    add_unit_clause(solver->core, ite->cond);
#if TRACE
    printf("---> bv_solver: implied literal ");
    print_literal(stdout, ite->cond);
    printf("\n");
#endif
  }
}


/*
 * Process the propagation queue
 * - return false if a conflict is found 
 * - return true otherwise
 */
static bool process_bv_prop_queue(bv_solver_t *solver) {
  bv_vartable_t *vtbl;
  bv_prop_queue_t *queue;
  int_queue_t *q;
  thvar_t x, y;
  uint32_t i;
  bval_t vx;

  assert(solver->queue != NULL);
  vtbl = &solver->vtbl;
  queue = solver->queue;
  q = &queue->queue;

  while (! int_queue_is_empty(q)) {
    x = int_queue_pop(q);
    vx = bv_prop_queue_get_val(queue, x);
    assert(vx != VAL_UNDEF && valid_bitvar(vtbl, x));

    switch (bvvar_tag(vtbl, x)) {
    case BVTAG_TRUE:
      assert(false);
      break;

    case BVTAG_SELECT:
      y = vtbl->def[x].sel.var;
      if (bvvar_tag(vtbl, y) == BVTAG_ITE) {
	i = vtbl->def[x].sel.idx;
	check_ite_bit_prop(solver, vtbl->def[y].ite, i, vx);
      }
      break;

    case BVTAG_OR:
      if (vx == VAL_FALSE) {
	bv_solver_propagate_false_bit(solver, vtbl->def[x].bop[0]);
	bv_solver_propagate_false_bit(solver, vtbl->def[x].bop[1]);
      }
      break;

    default:
      break;
    }
  }

  return !queue->unsat;
}







/****************
 *  EQUALITIES  *
 ***************/


/*
 * Return the root of x's class.
 * If x is not in the partition table, create a singleton class and return x
 * If x is a constant, it's given maximal rank
 */
static thvar_t bv_solver_get_root(bv_solver_t *solver, thvar_t x) {
  bvvar_tag_t xtag;
  thvar_t r;

  r = bv_partition_find_root(&solver->partition, x);
  if (r != null_thvar) {
    return r;
  }

  xtag = bvvar_tag(&solver->vtbl, x);
  if (xtag == BVTAG_SMALL_CONST || xtag == BVTAG_BIG_CONST) {
    bv_partition_add_root(&solver->partition, x);
  } else {
    bv_partition_add(&solver->partition, x);
  }

  assert(bv_partition_find_root(&solver->partition, x) == x);
  return x;
}


/*
 * Merge the classes of x and y
 * - add x and y to the partition table if they're not in the table already
 * - constants are given maximal rank so they stay root of their class
 * - x and y must not be in the same class
 */
static void bv_solver_merge(bv_solver_t *solver, thvar_t x, thvar_t y) {
  x = bv_solver_get_root(solver, x);
  y = bv_solver_get_root(solver, y);
  merge_bv_classes(&solver->partition, x, y);

#if TRACE
  printf("---> bv: merge u_%"PRId32" u_%"PRId32"\n", x, y);
#endif

  check_bit_propagation(solver, x, y);
}


/*
 * Assert (x == y) as an axiom
 * - record a conflict if it's known that x != y
 * - do nothing if x and y are already equal
 * - otherwise merge the classes of x and y
 * Return false if there's a conflict, true otherwise.
 */
static bool process_eq_axiom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  assert(solver->decision_level == solver->base_level);

  if (bv_solver_check_diseq(solver, x, y)) {
    add_empty_clause(solver->core); // Conflict
    return false;
  } else if (! bv_solver_check_eq(solver, x, y)) {
    bv_solver_merge(solver, x, y);
  }
  return true;
}



/*
 * Check whether axiom (x != y) can be cheaply turned into an equality
 * - for now, we check whether both x and y are bitvectors of size 1
 *   and whether x or y is a constant (i.e. 0b0 or 0b1)
 */
static bool diseq_axiom_convertible_to_eq(bv_solver_t *solver, thvar_t x, thvar_t y) {
  assert(bvvar_bitsize(&solver->vtbl, x) == bvvar_bitsize(&solver->vtbl, y));

  if (bvvar_bitsize(&solver->vtbl, x) == 1) {
    x = bv_partition_get_root(&solver->partition, x);
    y = bv_partition_get_root(&solver->partition, y);
    return bvvar_is_small_const(&solver->vtbl, x) || bvvar_is_small_const(&solver->vtbl, y);
  }
  return false;
}


/*
 * Build the complementary constant of x
 * - x must be either 0b0 or 0b1
 * - the complementary is 0b1 or 0b0
 */
static thvar_t get_bv1complement(bv_vartable_t *table, thvar_t x) {
  uint64_t i;

  assert(bvvar_bitsize(table, x) == 1 && bvvar_is_small_const(table, x));
  i = table->def[x].ival;
  assert(i == 0 || i == 1);
  return get_small_const(table, 1, 1-i);
}


/*
 * Check whether x is 0b0 (x must have bit-size 1)
 */
static inline bool thvar_is_bv1false(bv_vartable_t *table, thvar_t x) {
  assert(bvvar_bitsize(table, x) == 1);
  return bvvar_is_small_const(table, x) && table->def[x].ival == 0;
}



/*
 * Turn axiom (x != y) into an equality then process the equality.
 * - record a conflict if (x == y) holds
 * - return false if there's a conflict, true otherwise
 */
static bool convert_diseq_axiom_to_eq(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  bvvar_tag_t xtag, ytag;

  vtbl = &solver->vtbl;
  assert(bvvar_bitsize(vtbl, x) == 1 && bvvar_bitsize(vtbl, y) == 1);
  
  x = bv_partition_get_root(&solver->partition, x);
  y = bv_partition_get_root(&solver->partition, y);

  if (x == y) { 
    add_empty_clause(solver->core); // conflict
    return false;
  } else {
    xtag = bvvar_tag(vtbl, x);
    ytag = bvvar_tag(vtbl, y);

    if (xtag == ytag) {
      assert(xtag == BVTAG_SMALL_CONST && x != y);
      // redundant constraint (x != y) already true
    } else if (xtag == BVTAG_SMALL_CONST) {
      // rewrite (y != x) to (y = complement of x)
      bv_solver_merge(solver, y, get_bv1complement(vtbl, x));
    } else {
      assert(ytag == BVTAG_SMALL_CONST);
      // rewrite (x != y) to (x = (complement of y))
      bv_solver_merge(solver, x, get_bv1complement(vtbl, y));
    }
  }

  return true;
}




/******************
 *  INEQUALITIES  *
 *****************/

/*
 * Compute a lower or upper bound on a bitarray a
 * - n = number of bits in a. n must be no more than 64
 * - for n> 64, lower/upper bound functions exist in bvlogic_expr
 */
static uint64_t bitarray_upper_bound_unsigned64(bit_t *a, uint32_t n) {
  uint64_t c;
  uint32_t i;

  assert(0 < n && n <= 64);
  c = mask64(n);    // all bits equal to 1
  for (i=0; i<n; i++) {
    if (a[i] == false_bit) { // 
      c = clr_bit64(c, i);
    }
  }
  return c;
}

static uint64_t bitarray_lower_bound_unsigned64(bit_t *a, uint32_t n) {
  uint64_t c;
  uint32_t i;

  assert(0 < n && n <= 64);
  c = 0;    // all bits equal to 0
  for (i=0; i<n; i++) {
    if (a[i] == true_bit) { 
      c = set_bit64(c, i);
    }
  }
  return c;
}


static uint64_t bitarray_upper_bound_signed64(bit_t *a, uint32_t n) {
  uint64_t c;
  uint32_t i;

  assert(0 < n && n <= 64);
  c = mask64(n);   // all bit equal to 1
  for (i=0; i<n-1; i++) {
    if (a[i] == false_bit) {
      c = clr_bit64(c, i);
    }
  }

  // test the sign bit
  if (a[i] != true_bit) { // i.e. sign bit may be 0
    c = clr_bit64(c, i);
  }

  return c;
}


static uint64_t bitarray_lower_bound_signed64(bit_t *a, uint32_t n) {
  uint64_t c;
  uint32_t i;

  assert(0 < n && n <= 64);
  c = 0;

  for (i=0; i<n-1; i++) {
    if (a[i] == true_bit) {
      c = set_bit64(c, i);
    }
  }

  // sign bit
  if (a[i] != false_bit) { // sign bit may be 1
    c = set_bit64(c, i);
  }

  return c;
}



/*
 * Lower/upper bound computation for a bitvariable x
 * - for bitsize n <= 64, the bound is returned as a 64bit unsigned number
 *   (normalized modulo 2^n)
 * - for bitsize n > 64, the bound is copied into a bvconstant_t buffer v
 */
static uint64_t bvvar_upper_bound_unsigned64(bv_solver_t *solver, thvar_t x, uint32_t n);
static uint64_t bvvar_lower_bound_unsigned64(bv_solver_t *solver, thvar_t x, uint32_t n);
static uint64_t bvvar_upper_bound_signed64(bv_solver_t *solver, thvar_t x, uint32_t n);
static uint64_t bvvar_lower_bound_signed64(bv_solver_t *solver, thvar_t x, uint32_t n);

static void bvvar_upper_bound_unsigned(bv_solver_t *solver, thvar_t x, uint32_t n, bvconstant_t *v);
static void bvvar_lower_bound_unsigned(bv_solver_t *solver, thvar_t x, uint32_t n, bvconstant_t *v);
static void bvvar_upper_bound_signed(bv_solver_t *solver, thvar_t x, uint32_t n, bvconstant_t *v);
static void bvvar_lower_bound_signed(bv_solver_t *solver, thvar_t x, uint32_t n, bvconstant_t *v);



/*
 * BOUNDS FOR BVADD
 */

/*
 * Compute and cache the lower and upper bounds on x = (bvadd y z)
 * - n = bitsize of x (n <= 64)
 * - x is interpreted as an unsigned integer
 */
static bvbound_t *bvadd_bounds_unsigned64(bv_solver_t *solver, thvar_t x, uint32_t n) {
  bv_vartable_t *vtbl;
  bvbound_t *b;
  thvar_t y, z;
  uint64_t ly, uy, lz, uz, lx, ux;

  assert(bvvar_tag(&solver->vtbl, x) == BVTAG_ADD &&
	 bvvar_bitsize(&solver->vtbl, x) == n && 
	 0 < n && n <= 64);

  b = get_cached_bvbound(solver, x, BVBOUND_UNSIGNED);
  if (b == NULL) {
    vtbl = &solver->vtbl;
    y = vtbl->def[x].op[0];
    z = vtbl->def[x].op[1];

    ly = bvvar_lower_bound_unsigned64(solver, y, n);
    uy = bvvar_upper_bound_unsigned64(solver, y, n);
    lz = bvvar_lower_bound_unsigned64(solver, z, n);
    uz = bvvar_upper_bound_unsigned64(solver, z, n);

    lx = (ly + lz) & mask64(n);   // lx = (ly + lz) mod 2^n
    ux = (uy + uz) & mask64(n);   // ux = (uy + uz) mod 2^n

    /*
     * We have x = (y + z) mod 2^n so the bounds
     * lx <= x <= ux are valid unless there's an overflow 
     * on ux and no overflow on lx.
     * - overflow on ux is detected by (ux < uy)
     * - no overflow on lx is (lx >= ly)
     */
    if (ly <= lx && ux < uy) {
      lx = 0;
      ux = mask64(n);
    }

    b = add_bvbound64_to_cache(solver, x, BVBOUND_UNSIGNED, lx, ux);
  }

  return b;
}


/*
 * Underflow and overflow detection for a = b + c mod 2^n
 * - a, b, c are 2's complement n-bits integer
 * - there's underflow if (b < 0) and (c < 0) and (a >= 0)
 * - there's overflow  if (b >= 0) and (c >= 0) and (a < 0)
 */
static inline bool add_underflow64(uint64_t a, uint64_t b, uint64_t c, uint32_t n) {
  assert(a == ((b + c) & mask64(n)));
  return is_neg64(b, n) && is_neg64(c, n) && is_pos64(a, n);
}

static inline bool add_overflow64(uint64_t a, uint64_t b, uint64_t c, uint32_t n) {
  assert(a == ((b + c) & mask64(n)));
  return is_pos64(b, n) && is_pos64(c, n) && is_neg64(a, n);
}


/*
 * Bounds on x = (bvadd y z)
 * - n = bitsize of x (n <= 64)
 * - x is interpreted as a signed 2's-complement integer
 */
static bvbound_t *bvadd_bounds_signed64(bv_solver_t *solver, thvar_t x, uint32_t n) {
  bv_vartable_t *vtbl;
  bvbound_t *b;
  thvar_t y, z;
  uint64_t ly, uy, lz, uz, lx, ux;

  assert(bvvar_tag(&solver->vtbl, x) == BVTAG_ADD &&
	 bvvar_bitsize(&solver->vtbl, x) == n && 
	 0 < n && n <= 64);

  b = get_cached_bvbound(solver, x, BVBOUND_SIGNED);
  if (b == NULL) {
    vtbl = &solver->vtbl;
    y = vtbl->def[x].op[0];
    z = vtbl->def[x].op[1];

    ly = bvvar_lower_bound_signed64(solver, y, n);
    uy = bvvar_upper_bound_signed64(solver, y, n);
    lz = bvvar_lower_bound_signed64(solver, z, n);
    uz = bvvar_upper_bound_signed64(solver, z, n);

    lx = (ly + lz) & mask64(n);   // lx = (ly + lz) mod 2^n
    ux = (uy + uz) & mask64(n);   // ux = (uy + uz) mod 2^n

    /*
     * x is (y + z) mod 2^n
     * We have lx <= x <= ux unless
     * 1) there's an underflow on lx and not on ux
     * 2) there's an overflow on ux and not on lx
     */
    if ((add_underflow64(lx, ly, lz, n) && ! add_underflow64(ux, uy, uz, n)) 
        || (add_overflow64(ux, uy, uz, n) && ! add_overflow64(lx, ly, lz, n))) {
      lx = min_signed64(n);
      ux = max_signed64(n);
    }

    b = add_bvbound64_to_cache(solver, x, BVBOUND_SIGNED, lx, ux);
  }

  return b;  
}





/*
 * BOUNDS FOR BVSUB
 */

/*
 * Compute and cache the lower and upper bounds on x = (bvsub y z)
 * - n = bitsize of x (n <= 64)
 * - x is interpreted as an unsigned integer
 */
static bvbound_t *bvsub_bounds_unsigned64(bv_solver_t *solver, thvar_t x, uint32_t n) {
  bv_vartable_t *vtbl;
  bvbound_t *b;
  thvar_t y, z;
  uint64_t ly, uy, lz, uz, lx, ux;

  assert(bvvar_tag(&solver->vtbl, x) == BVTAG_SUB &&
	 bvvar_bitsize(&solver->vtbl, x) == n && 
	 0 < n && n <= 64);

  b = get_cached_bvbound(solver, x, BVBOUND_UNSIGNED);
  if (b == NULL) {
    vtbl = &solver->vtbl;
    y = vtbl->def[x].op[0];
    z = vtbl->def[x].op[1];

    ly = bvvar_lower_bound_unsigned64(solver, y, n);
    uy = bvvar_upper_bound_unsigned64(solver, y, n);
    lz = bvvar_lower_bound_unsigned64(solver, z, n);
    uz = bvvar_upper_bound_unsigned64(solver, z, n);

    // bounds on y and z must be normalized modulo 2^n
    assert(ly == (ly & mask64(n)) && uy == (uy & mask64(n)) &&
	   lz == (lz & mask64(n)) && uz == (uz & mask64(n)));

    lx = (ly - uz) & mask64(n);   // lx = (ly - uz) mod 2^n
    ux = (uy - lz) & mask64(n);   // ux = (uy - lz) mod 2^n

    /*
     * We have x = (y - z) mod 2^n so the bounds
     * lx <= x <= ux are valid unless there's 
     * underflow on lx (i.e., ly < uz) and not on ux (i.e., uy >= lz)
     */
    if (ly < uz && uy >= lz) {
      lx = 0;
      ux = mask64(n);
    }

    b = add_bvbound64_to_cache(solver, x, BVBOUND_UNSIGNED, lx, ux);
  }

  return b;
}








/*
 * Lower and upper bound on a bitvariable x
 * - n = number of bits in x, must be no more than 64
 */
static uint64_t bvvar_upper_bound_unsigned64(bv_solver_t *solver, thvar_t x, uint32_t n) {
  bv_vartable_t *vtbl;
  bvbound_t *b;

  assert(0 < n && n <= 64);

  vtbl = &solver->vtbl;
  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_SMALL_CONST: 
    return vtbl->def[x].ival;
  case BVTAG_BIT_ARRAY:
    return bitarray_upper_bound_unsigned64(vtbl->def[x].bit, n);
  case BVTAG_BIT:
    assert(vtbl->def[x].bval != false_bit);
    return (uint64_t) 1;
  case BVTAG_ADD:
    b = bvadd_bounds_unsigned64(solver, x, n);
    return bvbound_upper64(b);
  case BVTAG_SUB:
    b = bvsub_bounds_unsigned64(solver, x, n);
    return bvbound_upper64(b);
  default:
    return mask64(n);
  }
}

static uint64_t bvvar_lower_bound_unsigned64(bv_solver_t *solver, thvar_t x, uint32_t n) {
  bv_vartable_t *vtbl;
  bvbound_t *b;

  assert(0 < n && n<= 64);

  vtbl = &solver->vtbl;
  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_SMALL_CONST: 
    return vtbl->def[x].ival;
  case BVTAG_BIT_ARRAY:
    return bitarray_lower_bound_unsigned64(vtbl->def[x].bit, n);
  case BVTAG_BIT:
    assert(vtbl->def[x].bval != true_bit);
    return (uint64_t) 0;
  case BVTAG_ADD:
    b = bvadd_bounds_unsigned64(solver, x, n);
    return bvbound_lower64(b);
  case BVTAG_SUB:
    b = bvsub_bounds_unsigned64(solver, x, n);
    return bvbound_lower64(b);
  default:
    return 0;
  }
}

static uint64_t bvvar_upper_bound_signed64(bv_solver_t *solver, thvar_t x, uint32_t n) {
  bv_vartable_t *vtbl;
  bvbound_t *b;

  assert(0 < n && n<= 64);

  vtbl = &solver->vtbl;
  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_SMALL_CONST: 
    return vtbl->def[x].ival;
  case BVTAG_BIT_ARRAY:
    return bitarray_upper_bound_signed64(vtbl->def[x].bit, n);
  case BVTAG_BIT:
    assert(vtbl->def[x].bval != true_bit); 
    return (uint64_t) 0;
  case BVTAG_ADD:
    b = bvadd_bounds_signed64(solver, x, n);
    return bvbound_upper64(b);
  default:
    return max_signed64(n);
  }
}

static uint64_t bvvar_lower_bound_signed64(bv_solver_t *solver, thvar_t x, uint32_t n) {
  bv_vartable_t *vtbl;
  bvbound_t *b;

  assert(0 < n && n<= 64);

  vtbl = &solver->vtbl;
  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_SMALL_CONST: 
    return vtbl->def[x].ival;
  case BVTAG_BIT_ARRAY:
    return bitarray_lower_bound_signed64(vtbl->def[x].bit, n);
  case BVTAG_BIT:
    assert(vtbl->def[x].bval != false_bit);
    return (uint64_t) 1; // i.e. -1
  case BVTAG_ADD:
    b = bvadd_bounds_signed64(solver, x, n);
    return bvbound_lower64(b);
  default:
    return min_signed64(n); 
  }
}



/*
 * Lower and upper bound on a bitvariable x
 * - n = number of bits in x, must be more than 64
 * - the result is stored in buffer v.
 */
static void bvvar_upper_bound_unsigned(bv_solver_t *solver, thvar_t x, uint32_t n, bvconstant_t *v) {
  bv_vartable_t *vtbl;

  assert(n > 64);

  vtbl = &solver->vtbl;
  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_BIG_CONST:
    bvconstant_copy(v, n, vtbl->def[x].pval);
    break;
  case BVTAG_BIT_ARRAY:
    bitarray_upper_bound_unsigned(n, vtbl->def[x].bit, v);
    break;
  default:
    bvconstant_set_all_one(v, n);
    break;
  }
}

static void bvvar_lower_bound_unsigned(bv_solver_t *solver, thvar_t x, uint32_t n, bvconstant_t *v) {
  bv_vartable_t *vtbl;

  assert(n > 64);

  vtbl = &solver->vtbl;
  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_BIG_CONST: 
    bvconstant_copy(v, n, vtbl->def[x].pval);
    break;
  case BVTAG_BIT_ARRAY:
    bitarray_lower_bound_unsigned(n, vtbl->def[x].bit, v);
    break;
  default:
    bvconstant_set_all_zero(v, n);;
    break;
  }
}

static void bvvar_upper_bound_signed(bv_solver_t *solver, thvar_t x, uint32_t n, bvconstant_t *v) {
  bv_vartable_t *vtbl;

  assert(n > 64);

  vtbl = &solver->vtbl;
  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_BIG_CONST: 
    bvconstant_copy(v, n, vtbl->def[x].pval);
    break;
  case BVTAG_BIT_ARRAY:
    bitarray_upper_bound_signed(n, vtbl->def[x].bit, v);
    break;
  default:
    bvconstant_set_all_one(v, n);
    bvconst_clr_bit(v->data, n-1);
    break;
  }
}

static void bvvar_lower_bound_signed(bv_solver_t *solver, thvar_t x, uint32_t n, bvconstant_t *v) {
  bv_vartable_t *vtbl;

  assert(n > 64);

  vtbl = &solver->vtbl;
  switch (bvvar_tag(vtbl, x)) {
  case BVTAG_BIG_CONST: 
    bvconstant_copy(v, n, vtbl->def[x].pval);
    break;
  case BVTAG_BIT_ARRAY:
    bitarray_lower_bound_signed(n, vtbl->def[x].bit, v);
    break;
  default:
    bvconstant_set_all_zero(v, n);
    bvconst_set_bit(v->data, n-1);
    break;
  }
}


/*
 * Comparison codes used below
 */
enum {
  CODE_TRUE = 1,
  CODE_FALSE = -1,
  CODE_UNKNOWN = 0,
};


/*
 * Check whether (bvuge x y) is known to be true or false
 * - returned code: 0 means don't know
 *                  1 means known to be true
 *                 -1 means known to be false
 */
static int32_t bv_solver_check_uge(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  uint32_t n;
  uint64_t a, b;
  bvconstant_t *va, *vb;

  vtbl = &solver->vtbl;
  n = bvvar_bitsize(vtbl, x);
  assert(bvvar_bitsize(vtbl, y) == n);

  /*
   * Replace x and y by their class root if any
   * NOTE: not sure this actually helps.
   */
  x = bv_partition_get_root(&solver->partition, x);
  y = bv_partition_get_root(&solver->partition, y);


  if (x == y) {
    return CODE_TRUE;

  } else if (n <= 64) {

    a = bvvar_lower_bound_unsigned64(solver, x, n); // (x >= a)
    b = bvvar_upper_bound_unsigned64(solver, y, n); // (b >= y)
    if (a >= b) {
      return CODE_TRUE;
    }

    a = bvvar_upper_bound_unsigned64(solver, x, n); // (x <= a)
    b = bvvar_lower_bound_unsigned64(solver, y, n); // (b <= y) 
    if (a < b) {
      return CODE_FALSE;
    }

  } else {

    va = &solver->aux1;
    vb = &solver->aux2;

    bvvar_lower_bound_unsigned(solver, x, n, va); // (x >= va)
    bvvar_upper_bound_unsigned(solver, y, n, vb); // (vb >= y);
    if (bvconst_ge(va->data, vb->data, n)) {
      // va >= vb
      return CODE_TRUE;
    }

    bvvar_upper_bound_unsigned(solver, x, n, va); // (x <= va);
    bvvar_lower_bound_unsigned(solver, y, n, vb); // (vb <= y);
    if (bvconst_lt(va->data, vb->data, n)) {
      // va < vb
      return CODE_FALSE;
    }

  }

  return CODE_UNKNOWN;
}


/*
 * Check whether (bvsge x y) is known to be true or false
 * - returned code: 0 means don't know
 *                  1 means known to be true
 *                 -1 means known to be false
 */
static int32_t bv_solver_check_sge(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  uint32_t n;
  uint64_t a, b;
  bvconstant_t *va, *vb;

  vtbl = &solver->vtbl;
  n = bvvar_bitsize(vtbl, x);
  assert(bvvar_bitsize(vtbl, y) == n);


  /*
   * Replace x and y by their class root if any
   * NOTE: not sure this actually helps.
   */
  x = bv_partition_get_root(&solver->partition, x);
  y = bv_partition_get_root(&solver->partition, y);


  if (x == y) {
    return CODE_TRUE;

  } else if (n <= 64) {

    a = bvvar_lower_bound_signed64(solver, x, n); // (x >= a)
    b = bvvar_upper_bound_signed64(solver, y, n); // (b >= y)
    if (signed64_ge(a, b, n)) {
      return CODE_TRUE;
    }

    a = bvvar_upper_bound_signed64(solver, x, n); // (x <= a)
    b = bvvar_lower_bound_signed64(solver, y, n); // (b <= y) 
    if (signed64_gt(b, a, n)) {
      // b > a ==> x < y
      return CODE_FALSE;
    }

  } else {

    va = &solver->aux1;
    vb = &solver->aux2;

    bvvar_lower_bound_signed(solver, x, n, va); // (x >= va)
    bvvar_upper_bound_signed(solver, y, n, vb); // (vb >= y);
    if (bvconst_sge(va->data, vb->data, n)) {
      // va >= vb
      return CODE_TRUE;
    }

    bvvar_upper_bound_signed(solver, x, n, va); // (x <= va);
    bvvar_lower_bound_signed(solver, y, n, vb); // (vb <= y);
    if (bvconst_slt(va->data, vb->data, n)) {
      // va < vb
      return CODE_FALSE;
    }

  }  

  return CODE_UNKNOWN;

}



/*
 * Check atom atm asserted at the base level
 * - return false if there's a conflict (and record the conflict in the core)
 */
static bool check_toplevel_atom(bv_solver_t *solver, bvatm_t *atm) {
  literal_t l;
  bval_t v;
  int32_t i;

  assert(solver->decision_level == solver->base_level);

  l = atm->lit;
  v = literal_base_value(solver->core, l);
  
  switch (bvatm_tag(atm)) {
  case BVEQ_ATM:
    if ((v == VAL_TRUE && bv_solver_check_diseq(solver, atm->left, atm->right)) ||
	(v == VAL_FALSE && bv_solver_check_eq(solver, atm->left, atm->right))) {
      goto conflict;
    }
    break;
  case BVUGE_ATM:
    i = bv_solver_check_uge(solver, atm->left, atm->right);
    if ((v == VAL_TRUE && i == CODE_FALSE) || (v == VAL_FALSE && i == CODE_TRUE)) {
      goto conflict;
    }
    break;
  case BVSGE_ATM:
    i = bv_solver_check_sge(solver, atm->left, atm->right);
    if ((v == VAL_TRUE && i == CODE_FALSE) || (v == VAL_FALSE && i == CODE_TRUE)) {
      goto conflict;
    }
    break;
  default:
    break;
  }
  return true;

 conflict:
  add_empty_clause(solver->core);
  return false;
}




/********************************
 *  MAPPING TO PSEUDO LITERALS  *
 *******************************/

/*
 * Allocate and initialize the remap table
 */
static void bv_solver_prepare_remap(bv_solver_t *solver) {
  remap_table_t *tbl;

  assert(solver->remap == NULL);
  tbl = (remap_table_t *) safe_malloc(sizeof(remap_table_t));
  init_remap_table(tbl);
  solver->remap = tbl;
}



/*
 * Given i = sel->idx and x = sel->var, extract the i-th 
 * element of map[x] 
 * - map[x] must be non NULL
 */
static literal_t map_select(bv_vartable_t *vtbl, bv_select_t *sel) {
  literal_t *a;
  literal_t l;
  thvar_t x;  

  x = sel->var;
  if (bvvar_bitsize(vtbl, x) == 1) {
    assert(sel->idx == 0);
    l = vtbl->map[x].lit;
  } else {
    assert(sel->idx < bvvar_bitsize(vtbl, x));
    a = vtbl->map[x].array;
    assert(a != NULL);
    l = a[sel->idx];
  }
  assert(l != null_literal);

  return l;
}


/*
 * Return the pseudo literal mapped to bit b.
 * b must be mapped to a non-null literal.
 */
static literal_t get_map_of_bit(bv_vartable_t *vtbl, remap_table_t *rmap, bit_t b) {
  literal_t l;
  thvar_t x;

  assert(valid_bit(vtbl, b));
  x = var_of_bit(b);
  l = vtbl->map[x].lit;
  assert(l != null_literal);
  return l ^ sign_of_bit(b);
}


/*
 * Construct an array [l_0 ... l_{n-1}] where l_i is mapped to bit a[i]
 */
static literal_t *get_map_of_bitarray(bv_vartable_t *vtbl, remap_table_t *rmap, bit_t *a, uint32_t n) {
  literal_t *b;
  uint32_t i;

  b = (literal_t *) safe_malloc(n * sizeof(literal_t));
  for (i=0; i<n; i++) {
    b[i] = get_map_of_bit(vtbl, rmap, a[i]);
  }

  return b;
}


/*
 * Assign a pseudo literal or array of pseudo literals to variable x
 */
static void bv_solver_pseudo_map_variable(bv_solver_t *solver, thvar_t x) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  uint32_t i, n;

  rmap = solver->remap;
  vtbl = &solver->vtbl;

  if (! bvvar_is_mapped(vtbl, x)) {
    n = bvvar_bitsize(vtbl, x);
    switch (bvvar_tag(vtbl, x)) {
    case BVTAG_SMALL_CONST:
      if (n == 1) {
	vtbl->map[x].lit = map_bit1_const(vtbl->def[x].ival);
      } else {
	vtbl->map[x].array = map_small_const(vtbl->def[x].ival, n);
      }
      break;

    case BVTAG_BIG_CONST:
      vtbl->map[x].array = map_big_const(vtbl->def[x].pval, n);
      break;

    case BVTAG_TRUE:
      vtbl->map[x].lit = true_literal;
      break;

    case BVTAG_SELECT:
      // x is (select y i): map y first
      bv_solver_pseudo_map_variable(solver, vtbl->def[x].sel.var);
      vtbl->map[x].lit = map_select(vtbl, &vtbl->def[x].sel);
      break;

    case BVTAG_XOR:
    case BVTAG_OR:
      // We don't go inside OR or XOR but x itself occurs as part 
      // of (BIT ..) or (BIT_ARRAY ...) so we assign a fresh literal to x
      vtbl->map[x].lit = remap_table_fresh_lit(rmap);
      break;

    case BVTAG_BIT:
      // x is (BIT b): map x and b to the same pseudo literal
      bv_solver_pseudo_map_variable(solver, var_of_bit(vtbl->def[x].bval));
      vtbl->map[x].lit = get_map_of_bit(vtbl, rmap, vtbl->def[x].bval);
      break;

    case BVTAG_BIT_ARRAY:
      // x is (BITARRAY b0 ... b_{n-1})
      for (i=0; i<n; i++) {
	bv_solver_pseudo_map_variable(solver, var_of_bit(vtbl->def[x].bit[i]));
      }
      vtbl->map[x].array = get_map_of_bitarray(vtbl, rmap, vtbl->def[x].bit, n);
      break;

    default:
      // map[x] = an array of fresh pseudo literals
      assert(n > 0);
      if (n == 1) {
	vtbl->map[x].lit = remap_table_fresh_lit(rmap);
      } else {
	vtbl->map[x].array = remap_table_fresh_array(rmap, n);
      }
      break;
    }    
  }
}




/*
 * Return the pseudo literal mapped to bit b.
 * b must be mapped to something.
 */
static literal_t find_map_of_bit(bv_vartable_t *vtbl, bit_t b) {
  literal_t l;

  assert(valid_bit(vtbl, b));
  l = vtbl->map[var_of_bit(b)].lit;
  assert(l != null_literal);
  // l is map[x]. so map(pos(x)) = l, map(neg(x)) = not(l); 
  return l ^ sign_of_bit(b);
}


/*
 * Merge l and map(b) if possible.
 * Return true if the merge is possible.
 * Return false, if l and map(b) are opposite literals (so they can't be merged).
 */
static bool merge_map_bit(remap_table_t *rmap, bv_vartable_t *vtbl, literal_t l, bit_t b) {
  literal_t lb;

  lb = find_map_of_bit(vtbl, b);
  l = remap_table_find_root(rmap, l);
  lb = remap_table_find_root(rmap, lb);
  if (remap_table_mergeable(rmap, l, lb)) {
    remap_table_merge(rmap, l, lb);
  } else if (l != lb) {
    assert(l == not(lb));
    return false;
  }

  return true;
}


/*
 * Attempt to merge a[i] and map(b[i]) for i = 0,...,n-1
 * Return false if that fails.
 * Return true otherwise.
 */
static bool merge_map_bitarray(remap_table_t *rmap, bv_vartable_t *vtbl,
			       literal_t *a, bit_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (!merge_map_bit(rmap, vtbl, a[i], b[i])) {
      return false;
    }
  }
  return true;
}






/*
 * Assign pseudo literals to all variables
 * - return false if a conflict is detected (i.e., the map of x 
 *   and root[x] cannote be merged, for a non-root variable x).
 * - return true otherwise
 */
static bool bv_solver_build_pseudo_maps(bv_solver_t *solver) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  uint32_t i, n, j, k;
  thvar_t x;

  rmap = solver->remap;
  assert(rmap != NULL);
  vtbl = &solver->vtbl;

  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (bv_is_replaced(&solver->partition, i)) {
      /*
       * i is not a root: map it to the same thing as its root
       */
      x = bv_partition_find_root(&solver->partition, i);
      assert(x != i && x != null_thvar && bvvar_bitsize(vtbl, x) == bvvar_bitsize(vtbl, i));

      bv_solver_pseudo_map_variable(solver, x);      
      k = bvvar_bitsize(vtbl, i);
      if (k <= 1) {
	assert(vtbl->map[x].lit != null_literal);
	vtbl->map[i].lit = vtbl->map[x].lit;
      } else {
	assert(vtbl->map[x].array != NULL);
	vtbl->map[i].array = vtbl->map[x].array;
      }


      switch (bvvar_tag(vtbl, i)) {
      case BVTAG_BIT:
	/*
	 * i is (BIT b): make sure i and b are mapped to the same 
	 * pseudo literal. If that's not possible, the system is unsat
	 */
	bv_solver_pseudo_map_variable(solver, var_of_bit(vtbl->def[i].bval));
	if (!merge_map_bit(rmap, vtbl, vtbl->map[i].lit, vtbl->def[i].bval)) {
	  goto unsat_detected;
	}
	break;

      case BVTAG_BIT_ARRAY:
	/*
	 * i is (BITARRAY b_0 ... b_{k-1}): make sure 
	 * the array map[i].lit is the same as [map(b0) ... map(b_{k-1})]
	 */
	for (j=0; j<k; j++) {
	  bv_solver_pseudo_map_variable(solver, var_of_bit(vtbl->def[i].bit[j]));
	}
	if (!merge_map_bitarray(rmap, vtbl, vtbl->map[i].array, vtbl->def[i].bit, k)) {
	  goto unsat_detected;
	}
	break;

      default: // do nothing
	break;
      }

      
    } else {
      // i is root: compute its map
      bv_solver_pseudo_map_variable(solver, i);
    }
  }

  // no conflict detected
  return true;

 unsat_detected:
  return false;
}



/*
 * Attempt to merge l0 and l1
 * - return false if a conflict is detected
 */
static bool merge_pseudo_lits(remap_table_t *rmap, literal_t l0, literal_t l1) {
  l0 = remap_table_find_root(rmap, l0);
  l1 = remap_table_find_root(rmap, l1);
  if (remap_table_mergeable(rmap, l0, l1)) {
    remap_table_merge(rmap, l0, l1);
  } else if (l0 != l1) {
    return false;
  }
  return true;
}

/*
 * Propagate the assignments to the bit-variables
 */
static bool bv_solver_propagate_truth_assignment(bv_solver_t *solver) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  bv_prop_queue_t *queue;
  uint32_t i, n;
  literal_t l0;

  queue = solver->queue;
  if (queue != NULL) {
    vtbl = &solver->vtbl;
    rmap = solver->remap;

    n = queue->nvars;
    for (i=0; i<n; i++) {
      switch (bv_prop_queue_get_val(queue, i)) {
      case VAL_TRUE:
	assert(bvvar_bitsize(vtbl, i) == 0);
	l0 = vtbl->map[i].lit;
	if (l0 != null_literal) {
	  if (! merge_pseudo_lits(rmap, l0, true_literal)) {
	    return false;
	  }
	} else {
	  vtbl->map[i].lit = true_literal;
	}
	break;

      case VAL_FALSE:
	assert(bvvar_bitsize(vtbl, i) == 0);
	l0 = vtbl->map[i].lit;
	if (l0 != null_literal) {
	  if (! merge_pseudo_lits(rmap, l0, false_literal)) {
	    return false;
	  }
	} else {
	  vtbl->map[i].lit = false_literal;
	}
	break;

      case VAL_UNDEF:
	break;
      }
    }
  }
  return true;
}


/*
 * Cleanup the array maps before reset or deletion
 * - reset_bv_vartable and delete_bv_vartable free map[x].array 
 *   for all variables x.
 * - propagate maps ensure map[x].array and map[root(x)].array
 *   are equal.
 * - to avoid double-frees, we reset map[x].array to NULL for any
 *   x that's not a root.
 */
static void clean_array_maps(bv_solver_t *solver) {
  bv_vartable_t *vtbl;
  uint32_t i, n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (bv_is_replaced(&solver->partition, i) && bvvar_bitsize(vtbl, i) >= 2) {
      vtbl->map[i].array = NULL;
    }
  }
}








/********************
 *   BIT-BLASTING   *
 *******************/

/*
 * Allocate and initialize bit-blaster and bit-solver
 */
static void bv_solver_prepare_blasting(bv_solver_t *solver) {
  bit_blaster_t *b;

  assert(solver->blaster == NULL);

  b = (bit_blaster_t *) safe_malloc(sizeof(bit_blaster_t));
  init_bit_blaster(b, true, solver->core, solver->remap);
  solver->blaster = b;
}


/*
 * Collect the array of literals mapped to x into vector v
 * - these are the "real-literals" from the bit solver (some of them may be 
 *   null_literal)
 * - x must not be a bit variable
 */
static void collect_var_literals(bv_solver_t *solver, thvar_t x, ivector_t *v) {
  remap_table_t *rmap;
  bv_vartable_t *vtbl;
  literal_t *a;
  uint32_t i, n;
  literal_t l0;

  assert(solver->remap != NULL);

  rmap = solver->remap;
  vtbl = &solver->vtbl;
  ivector_reset(v);

  n = bvvar_bitsize(vtbl, x);
  if (n == 1) { 
    l0 = vtbl->map[x].lit; // pseudo literal
    assert(l0 != null_literal);
    ivector_push(v, remap_table_find(rmap, l0));
  } else {
    assert(n > 1);
    a = vtbl->map[x].array; // array of pseudo literals
    assert(a != NULL);
    for (i=0; i<n; i++) {
      l0 = a[i];
      assert(l0 != null_literal);
      ivector_push(v, remap_table_find(rmap, l0));
    }
  }
}




/*
 * RECURSIVE BIT-BLASTING FUNCTIONS
 *
 * 1) for a bit-vector variable x (i.e., bitsize(x) is positive)
 *    - if x is marked do nothing.
 *    - otherwise create literals for x and add clauses in the 
 *      core to encode the definition of x, then mark x.
 *
 * 2) for a bit variable x (i.e., bitsize(x) = 0), 
 *    - if x is marked, return the literal l corresponding to x
 *      in the bit solver
 *    - otherwise convert x to a literal l in the core,
 *      add clauses that encode the definition of x, and mark x.
 */
static void bv_solver_bitblast_variable(bv_solver_t *solver, thvar_t x);
static literal_t bv_solver_bitblast_bitvar(bv_solver_t *solver, thvar_t x);



/*
 * Convert bit b to a concrete literal
 */
static literal_t bv_solver_bitblast_bit(bv_solver_t *solver, bit_t b) {
  assert(valid_bit(&solver->vtbl, b));
  return bv_solver_bitblast_bitvar(solver, var_of_bit(b)) ^ sign_of_bit(b);
}



/*
 * Flatten then construct clauses encoding the definition of x when 
 * x is an XOR variable.
 * - l0 must be the pseudo-literal mapped to x
 * - a side effect is to assign a real literal to l0 if there isn't one 
 *   already
 *
 * Return the real literal assigned to l0.
 *
 * Flattening is bounded to make sure we don't blow up here.
 * This is probably not a big deal for XOR.
 */
#define XOR_FLATTEN_MAX 10

static literal_t flatten_xor_definition(bv_solver_t *solver, thvar_t x, literal_t l0) {
  bv_vartable_t *vtbl;
  int32_t queue[XOR_FLATTEN_MAX];
  uint32_t i, n;
  bit_t b, b0, b1;
  literal_t l;

  vtbl = &solver->vtbl;
  assert(valid_bitvar(vtbl, x) && bvvar_tag(vtbl, x) == BVTAG_XOR && 
	 vtbl->map[x].lit == l0 && l0 != null_literal);

  b0 = vtbl->def[x].bop[0];
  b1 = vtbl->def[x].bop[1];
  queue[0] = b0;
  queue[1] = b1;
  i = 0;
  n = 2;
  while (i < n && n < XOR_FLATTEN_MAX) {
    b = queue[i];
    x = var_of_bit(b);
    /*
     * We flatten if x has no pseudo literal attached and is of the 
     * form (XOR b0 b1).
     *
     * b is then either (XOR b0 b1) or not (XOR b0 b1)
     * - in the first case, we replace b by b0 in queue and add b1 at the end of the queue
     * - in the second case, we use "b == not (XOR b0 b1) == (XOR (not b0) b1)"
     *   so we replace b by (not b0) in the queue and add b1 at the end.
     *
     * Note: this is just a precaution to make the function more robust.
     * With the current implementation, the children of (XOR ..) are all positive
     * so any element in the queue has positive polarity.
     */
    if (vtbl->map[x].lit == null_literal && bvvar_tag(vtbl, x) == BVTAG_XOR) {
      b0 = vtbl->def[x].bop[0];
      b1 = vtbl->def[x].bop[1];
      queue[i] = b0 ^ sign_of_bit(b);
      queue[n] = b1;
      n ++;
    } else {
      i ++;
    }
  }

  // compute the internalization of all bits in queue[0 ... n-1]
  for (i=0; i<n; i++) {
    queue[i] = bv_solver_bitblast_bit(solver, queue[i]);
  }


  l = remap_table_find(solver->remap, l0);
  if (l == null_literal) {
    // construct l = (xor queue[0] ... queue[n-1])
    // then assign l to l0
    l = bit_blaster_make_xor(solver->blaster, n, queue);
    assert(l != null_literal);
    remap_table_assign(solver->remap, l0, l);
  } else {
    // assert l = (xor queue[0] ... queue[n-1])
    bit_blaster_xor_gate(solver->blaster, n, queue, l);
  }

  return l;
}




/*
 * Flatten then constructs clauses encoding the defintion of x where x 
 * an OR bit-variable
 * - l0 must be the pseudo literal mapped to x (and l0 must be non-null)
 * - as a side effect, the function assign a real literal to x if there 
 *   isn't one yet.
 * 
 * Return the real literal assigned to l0 (and x).
 *
 * We attempt to eliminate intermediate OR variables (via flattening).
 * There's a hard-coded bound on flattening to make sure we don't blow up.
 *
 * TODO: it could improve performance to flatten as much as possible, but this
 * would require a more complicated implementation. Deeply nested (OR ..) are 
 * not uncommon in the SMT lib benchmarks.
 */
#define OR_FLATTEN_MAX 50

static literal_t flatten_or_definition(bv_solver_t *solver, thvar_t x, literal_t l0) {
  bv_vartable_t *vtbl;
  int32_t queue[OR_FLATTEN_MAX];
  uint32_t i, n;
  bit_t b, b0, b1;
  literal_t l;

  vtbl = &solver->vtbl;
  assert(valid_bitvar(vtbl, x) && bvvar_tag(vtbl, x) == BVTAG_OR && 
	 vtbl->map[x].lit == l0 && l0 != null_literal);

  b0 = vtbl->def[x].bop[0];
  b1 = vtbl->def[x].bop[1];
  queue[0] = b0;
  queue[1] = b1;
  i = 0;
  n = 2;
  while (i < n && n < OR_FLATTEN_MAX) {
    b = queue[i];
    x = var_of_bit(b);
    /*
     * If b has positive polarity and x is of the form (OR b0 b1) then
     * we have b == (OR b0 b1) so we can replace b by the pair b0, b1
     * in the queue. We do this if x has no pseudo literal attached,
     * (since then b itself is probably useful).
     */
    if (bit_is_pos(b) && vtbl->map[x].lit == null_literal && bvvar_tag(vtbl, x) == BVTAG_OR) {
      //    if (bit_is_pos(b) && bvvar_tag(vtbl, x) == BVTAG_OR) {
      b0 = vtbl->def[x].bop[0];
      b1 = vtbl->def[x].bop[1];
      queue[i] = b0;
      queue[n] = b1;
      n ++;
    } else {
      i ++;
    }
  }

  // compute the internalization of all bits in queue[0 ... n-1]
  for (i=0; i<n; i++) {
    queue[i] = bv_solver_bitblast_bit(solver, queue[i]);
  }


  // Find the concrete literal mapped to x
  l = remap_table_find(solver->remap, l0);
  if (l == null_literal) {
    // construct l = (OR queue[0] ... queue[n-1])
    // then assign l to l0
    l = bit_blaster_make_or(solver->blaster, n, queue);
    assert(l != null_literal);
    remap_table_assign(solver->remap, l0, l);
  } else {
    // assert l = (or queue[0] ... queue[n-1])
    bit_blaster_or_gate(solver->blaster, n, queue, l);
  }

  return l;
}


/*
 * Convert bit variable x to a literal
 * - if x is not mapped to a non-null pseudo literal l0 then one is created
 * - if x is marked, just return the bit_vector literal assigned to l0
 * - otherwise, convert x to a literal and add constraints encoding the
 *   definition of x.
 */
static literal_t bv_solver_bitblast_bitvar(bv_solver_t *solver, thvar_t x) { 
  remap_table_t *rmap;
  bv_vartable_t *vtbl;
  literal_t l0, l;
  thvar_t y;
  uint32_t i;

  rmap = solver->remap;
  vtbl = &solver->vtbl;

  assert(rmap != NULL && valid_bitvar(vtbl, x));
  l0 = vtbl->map[x].lit;   // pseudo literal for x

  if (! bvvar_is_marked(vtbl, x)) {
    /*
     * the definition of x has not been translated to the 
     * bit_solver yet.      
     * The pseudo-literal l0 may be null_literal (if x occurs in
     * a deep or/xor or if x is (select y i))
     */
    switch (bvvar_tag(vtbl, x)) {
    case BVTAG_TRUE: // nothing to do
      l = true_literal;
      assert(remap_table_find(rmap, l0) == true_literal);
      break;

    case BVTAG_SELECT:
      /*
       * x is (bit i y) for a bit-vector variable y
       */
      y = vtbl->def[x].sel.var;
      if (l0 == null_literal) {
	// assign pseudo literal i of y to x
	i = vtbl->def[x].sel.idx;
	if (bvvar_bitsize(vtbl, y) == 1) {
	  assert(i == 0);
	  l0 = vtbl->map[y].lit;
	} else {
	  assert(vtbl->map[y].array != NULL);
	  l0 = vtbl->map[y].array[i];
	}
	assert(l0 != null_literal);
	vtbl->map[x].lit = l0;
      }
      /*
       * Optimization if y is unininterpreted: we try to assign
       * literals only to the bits of y that are used somewhere.
       */
      if (bvvar_is_uninterpreted(vtbl, y)) {
	l = remap_table_find(rmap, l0);
	if (l == null_literal) {
	  l = bit_blaster_fresh_literal(solver->blaster);
	  remap_table_assign(rmap, l0, l);
	}
      } else {
	// general case: bitblast variable y
	// as a side effect this will assign a concrete literal to l0
	bv_solver_bitblast_variable(solver, y);	
	l = remap_table_find(rmap, l0);
	assert(l != null_literal);
      }
      break;

    case BVTAG_XOR:
      /*
       * if l != null, assert l = x after flattening the xor 
       * if l == null, compute l1 = x after flattening
       * then store l1 as the concrete literal for l0
       */
      if (l0 == null_literal) {
	l0 = remap_table_fresh_lit(rmap);
	vtbl->map[x].lit = l0;
      }
      l = flatten_xor_definition(solver, x, l0);
      break;

    case BVTAG_OR:
      /*
       * if l != null, assert l = x after flattening the xor 
       * if l == null, compute l1 = x after flattening
       * then store l1 as the concrete literal for l0
       */
      if (l0 == null_literal) {
	l0 = remap_table_fresh_lit(rmap);
	vtbl->map[x].lit = l0;
      }
      l = flatten_or_definition(solver, x, l0);
      break;

    default:
      assert(false);
      l = null_literal; // Stop GCC warning
      break;
    }

    bvvar_set_mark(vtbl, x);

  } else {
    // a real literal must be already mapped to l0
    assert(l0 != null_literal);
    l = remap_table_find(rmap, l0);
  }
 
  assert(l != null_literal);

  return l;
}



/*
 * Assert (u == (op a b)) for one of the binary operators op
 * - a, b must be fully-defined arrays of n literals
 * - u must be an array of n pseudo literals
 */
static void bit_blaster_make_bvop(bit_blaster_t *blaster, bvvar_tag_t op, literal_t *a, literal_t *b, 
				  literal_t *u, uint32_t n) {
  switch (op) {
  case BVTAG_ADD:
    bit_blaster_make_bvadd(blaster, a, b, u, n);
    break;
  case BVTAG_SUB:
    bit_blaster_make_bvsub(blaster, a, b, u, n);
    break;
  case BVTAG_MUL:
    bit_blaster_make_bvmul(blaster, a, b, u, n);
    //    bit_blaster_make_bvmul2(blaster, a, b, u, n); // not good
    break;

  case BVTAG_SMOD:
    fprintf(stderr, "\nBitvector SMOD not supported\n");
    abort();
    break;

  case BVTAG_SHL:
    bit_blaster_make_shift_left(blaster, a, b, u, n);
    break;
  case BVTAG_LSHR:
    bit_blaster_make_lshift_right(blaster, a, b, u, n);
    break;
  case BVTAG_ASHR:
    bit_blaster_make_ashift_right(blaster, a, b, u, n);
    break;
 
  default:
    assert(false);    
  }
}



/*
 * Assert (u == (op a b)) for a division/remainder term (op x y)
 * - a and b must be arrays of n literals
 * - u must be an array of n pseudo-literals
 * Check whether the associate term z = (op' x y) exists and if so
 * apply the bit-blasting operation to z too.
 */
static void bit_blaster_make_bvdivop(bv_solver_t *solver, bvvar_tag_t op, thvar_t x, thvar_t y,
				     literal_t *a, literal_t *b, literal_t *u, uint32_t n) {
  bv_vartable_t *vtbl;
  literal_t *v;
  literal_t aux;
  thvar_t z;  

  vtbl = &solver->vtbl;
  v = NULL;

  switch (op) {
  case BVTAG_UDIV:
    z = find_urem(vtbl, x, y);
    if (z != null_thvar) {
      if (n == 1) {
	aux = vtbl->map[z].lit;
	assert(aux != null_literal);
	v = &aux;
      } else {
	v = vtbl->map[z].array;
      }
    }
    bit_blaster_make_udivision(solver->blaster, a, b, u, v, n);
    break;

  case BVTAG_UREM:
    z = find_udiv(vtbl, x, y);
    if (z != null_thvar) {
      if (n == 1) {
	aux = vtbl->map[z].lit;
	assert(aux != null_literal);
	v = &aux;
      } else {
	v = vtbl->map[z].array;
      }
    }
    bit_blaster_make_udivision(solver->blaster, a, b, v, u, n);    
    break;

  case BVTAG_SDIV:
    z = find_srem(vtbl, x, y);
    if (z != null_thvar) {
      if (n == 1) {
	aux = vtbl->map[z].lit;
	assert(aux != null_literal);
	v = &aux;
      } else {
	v = vtbl->map[z].array;
      }
    }
    bit_blaster_make_sdivision(solver->blaster, a, b, u, v, n);
    break;

  case BVTAG_SREM:
    z = find_sdiv(vtbl, x, y);
    if (z != null_thvar) {
      if (n == 1) {
	aux = vtbl->map[z].lit;
	assert(aux != null_literal);
	v = &aux;
      } else {
	v = vtbl->map[z].array;
      }
    }
    bit_blaster_make_sdivision(solver->blaster, a, b, v, u, n);
    break;

  default:
    assert(false);
    abort();
  }
}

/*
 * Convert bitvector variable x to literals in the bit solver
 * - x must be mapped to a non-null pseudo literal a[0]
 *   or to a non-NULL array of pseudo literals a[0,.... n-1]
 * - if x is marked, do nothing
 * - otherwise, create or find the real literals assigned
 *   to a[0], ..., a[n-1] then assert clauses encoding 
 *   the definition of x in the bit solver.
 */
static void bv_solver_bitblast_variable(bv_solver_t *solver, thvar_t x) {
  remap_table_t *rmap;
  bv_vartable_t *vtbl;
  ivector_t *a, *b;
  literal_t *u;
  bvvar_tag_t op;
  uint32_t i, n;
  literal_t l, aux;

  rmap = solver->remap;
  vtbl = &solver->vtbl;

  assert(rmap != NULL && valid_bvvar(vtbl, x) && bvvar_bitsize(vtbl, x) > 0);

  if (! bvvar_is_marked(vtbl, x)) {
    /*
     * The definition of x has not been translated yet
     */

    // u := array of pseudo literals currently mapped to x
    n = bvvar_bitsize(vtbl, x);
    if (n == 1) {
      aux = vtbl->map[x].lit;
      assert(aux != null_literal);
      u = &aux;
    } else {
      u = vtbl->map[x].array;
    }

    op = bvvar_tag(vtbl, x);

    switch (op) {
      // nothing to do: the constants are bit-blasted when
      // pseudo-literal maps are constructed.
    case BVTAG_SMALL_CONST:      
    case BVTAG_BIG_CONST:
      break;

    case BVTAG_VAR:
      // complete u with fresh literals
      for (i=0; i<n; i++) {
	l = remap_table_find(rmap, u[i]);
	if (l == null_literal) {
	  l = bit_blaster_fresh_literal(solver->blaster);
	  remap_table_assign(rmap, u[i], l);
	}
      }
      break;
    
    case BVTAG_BIT:
      // convert the bit: u[0] should be assigned a real literal as a result
      l = bv_solver_bitblast_bit(solver, vtbl->def[x].bval);
      assert(l != null_literal && remap_table_find(rmap, u[0]) == l);
      break;

    case BVTAG_BIT_ARRAY:
      for (i=0; i<n; i++) {
	l = bv_solver_bitblast_bit(solver, vtbl->def[x].bit[i]);
	assert(l != null_literal && remap_table_find(rmap, u[i]) == l);
      }
      break;

    case BVTAG_ADD:
    case BVTAG_SUB:
    case BVTAG_MUL:
    case BVTAG_SMOD:
    case BVTAG_SHL:
    case BVTAG_LSHR:
    case BVTAG_ASHR:
      // process the operands then assert u = (op a b)
      bv_solver_bitblast_variable(solver, vtbl->def[x].op[0]);
      bv_solver_bitblast_variable(solver, vtbl->def[x].op[1]);
      a = &solver->a_vector;
      b = &solver->b_vector;
      collect_var_literals(solver, vtbl->def[x].op[0], a);
      collect_var_literals(solver, vtbl->def[x].op[1], b);
      assert(a->size == n && b->size == n);
      bit_blaster_make_bvop(solver->blaster, op, a->data, b->data, u, n);
      break;

    case BVTAG_UDIV:
    case BVTAG_UREM:
    case BVTAG_SDIV:
    case BVTAG_SREM:
      // need special treatment
      bv_solver_bitblast_variable(solver, vtbl->def[x].op[0]);
      bv_solver_bitblast_variable(solver, vtbl->def[x].op[1]);
      a = &solver->a_vector;
      b = &solver->b_vector;
      collect_var_literals(solver, vtbl->def[x].op[0], a);
      collect_var_literals(solver, vtbl->def[x].op[1], b);
      assert(a->size == n && b->size == n);
      bit_blaster_make_bvdivop(solver, op, vtbl->def[x].op[0],
			       vtbl->def[x].op[1], a->data, b->data, u, n);
      break;

    case BVTAG_NEG:
      // process the operand then assert u = (neg a)
      bv_solver_bitblast_variable(solver, vtbl->def[x].op[0]);
      a = &solver->a_vector;
      collect_var_literals(solver, vtbl->def[x].op[0], a);
      assert(a->size == n);
      bit_blaster_make_bvneg(solver->blaster, a->data, u, n);
      break;

    case BVTAG_ITE:
      // process the operands then assert u = (ite c a b)
      l = vtbl->def[x].ite->cond;
      assert(l != null_literal);
#if TRACE
      if (l == true_literal || l == false_literal) {
	if (l == true_literal) {
	  printf("---> condition in ite is true\n");
	} else {
	  printf("---> condition in ite is false\n");
	}
	print_bvsolver_vardef(stdout, solver, x);
	print_bvsolver_vardef(stdout, solver, vtbl->def[x].ite->left);
	print_bvsolver_vardef(stdout, solver, vtbl->def[x].ite->right);
	fflush(stdout);
      }
#endif
      /*
       * TODO: improve this if l == true_literal or l == false_literal
       */
      bv_solver_bitblast_variable(solver, vtbl->def[x].ite->left);
      bv_solver_bitblast_variable(solver, vtbl->def[x].ite->right);
      a = &solver->a_vector;
      b = &solver->b_vector;
      collect_var_literals(solver, vtbl->def[x].ite->left, a);
      collect_var_literals(solver, vtbl->def[x].ite->right, b);
      assert(a->size == n && b->size == n);
      bit_blaster_make_bvmux(solver->blaster, l, a->data, b->data, u, n);
      break;

    default:
      assert(false);
      break;
    }

    // mark x
    bvvar_set_mark(vtbl, x);
  }
}


/*
 * Preprocess an atom p := (bveq x y) where y is either 0b0 or 0b1
 * For p := (bveq x 0b1), we attempt to map x to p 
 * For p := (bveq x 0b0), we attempt to map x to not(p)
 * (this may fail if x is already mapped to a non-null literal).
 */
static void bv_solver_preprocess_bveq(bv_solver_t *solver, literal_t p, thvar_t x, thvar_t y) {
  remap_table_t *rmap;
  bv_vartable_t *vtbl;
  literal_t l0, l;

  rmap = solver->remap;
  vtbl = &solver->vtbl;
  
  assert(bvvar_bitsize(vtbl, x) == 1 && bvvar_bitsize(vtbl, y) == 1 &&
	 bvvar_is_small_const(vtbl, y));

  assert(vtbl->def[y].ival == 0 || vtbl->def[y].ival == 1);
  
  if (vtbl->def[y].ival == 0) {
    p = not(p);
  }

  /*
   * Attempt to map p as literal for x
   */
  l0 = vtbl->map[x].lit; // pseudo literal for x
  assert(l0 != null_literal);
  l = remap_table_find(rmap, l0);
  if (l == null_literal) {
    // assign p to x (i.e., to l0)
    remap_table_assign(rmap, l0, p);
  } else if (l == true_literal) {
    // p := true
    add_unit_clause(solver->core, p);
  } else if (l == false_literal) {
    // p must be false
    add_unit_clause(solver->core, not(p));
  }
}



/*
 * Try to avoid bit-blasting for atom i of the form (bvuge x y).
 * - search for j = (bvuge y x) and k = (bveq x y)
 * - if both exists, add a constraint that encodes
 *   (bvuge x y) <==> (bveq x y) and (not (bvuge y x))
 * - to break the symmetry, we try this trick only if x > y
 * 
 * Return true if this succeeds.
 * Return false otherwise.
 */
static bool bv_solver_bvuge_var_def(bv_solver_t *solver, int32_t x, int32_t y, int32_t i) {
  bv_atomtable_t *atbl;
  int32_t j, k;
  literal_t ge_xy, eq_xy, ge_yx;

  if (x > y) {
    atbl = &solver->atbl;

    assert(atbl->data[i].left == x && atbl->data[i].right == y && 
	   bvatm_tag(atbl->data + i) == BVUGE_ATM);

    j = find_bvuge_atom(&solver->atbl, y, x);
    if (j >= 0) {
      k = find_bveq_atom(&solver->atbl, x, y);
      if (k >= 0) {
	assert(j != i && j != k && k != i);

	// success
	ge_xy = atbl->data[i].lit;
	eq_xy = atbl->data[k].lit;
	ge_yx = atbl->data[j].lit;

	// assert ge_xy = (or eq_xy (not ge_yx))
	bit_blaster_or2_gate(solver->blaster, eq_xy, not(ge_yx), ge_xy);
	return true;
      }
    }    
  }

  return false;
}


/*
 * Same thing for signed comparisons
 * - i is (bvsge x y)
 */
static bool bv_solver_bvsge_var_def(bv_solver_t *solver, int32_t x, int32_t y, int32_t i) {
  bv_atomtable_t *atbl;
  int32_t j, k;
  literal_t ge_xy, eq_xy, ge_yx;

  if (x > y) {
    atbl = &solver->atbl;

    assert(atbl->data[i].left == x && atbl->data[i].right == y && 
	   bvatm_tag(atbl->data + i) == BVSGE_ATM);

    j = find_bvsge_atom(&solver->atbl, y, x);
    if (j >= 0) {
      k = find_bveq_atom(&solver->atbl, x, y);
      if (k >= 0) {
	assert(j != i && j != k && k != i);

	// success
	ge_xy = atbl->data[i].lit;
	eq_xy = atbl->data[k].lit;
	ge_yx = atbl->data[j].lit;

	// assert ge_xy = (or eq_xy (not ge_yx))
	bit_blaster_or2_gate(solver->blaster, eq_xy, not(ge_yx), ge_xy);
	return true;
      }
    }    
  }

  return false;
}






/*
 * Process and bit-blast all the atoms
 */
static void bv_solver_bitblast_all_atoms(bv_solver_t *solver) {
  bv_atomtable_t *atbl;
  bv_vartable_t *vtbl;
  ivector_t *a, *b;
  thvar_t x, y;
  uint32_t i, n;
  literal_t l;

  vtbl = &solver->vtbl;
  atbl = &solver->atbl;
  n = atbl->natoms;
  a = &solver->a_vector;
  b = &solver->b_vector;


  /*
   * First pass: pre-process all atoms of the form (bveq x 0b1) or (bveq x 0b0)
   */
  for (i=0; i<n; i++) {
    l = atbl->data[i].lit;
    assert(l != null_literal);
    x = atbl->data[i].left;
    y = atbl->data[i].right;

    if (bvatm_tag(atbl->data + i) == BVEQ_ATM && bvvar_bitsize(vtbl, x) == 1) {
      assert(bvvar_bitsize(vtbl, y) == 1);
      if (bvvar_is_small_const(vtbl, x)) {
	bv_solver_preprocess_bveq(solver, l, y, x);
      } else if (bvvar_is_small_const(vtbl, y)){
	bv_solver_preprocess_bveq(solver, l, x, y);
      }
    }
  }

  /*
   * Second pass: bitblasting
   */
  for (i=0; i<n; i++) {
    l = atbl->data[i].lit;
    assert(l != null_literal);
    x = atbl->data[i].left;
    y = atbl->data[i].right;

    /*
     * Process operands x and y
     */
    bv_solver_bitblast_variable(solver, x);
    bv_solver_bitblast_variable(solver, y);
    collect_var_literals(solver, x, a);
    collect_var_literals(solver, y, b);
    assert(a->size == b->size && a->size > 0);

    /*
     * Add the constraint (l == atom...)
     */
    switch (bvatm_tag(atbl->data + i)) {
    case BVEQ_ATM:
      bit_blaster_make_bveq2(solver->blaster, a->data, b->data, l, a->size);
      break;

    case BVUGE_ATM:
      // Try variant definition. If that fails, bitblast.
      if (! bv_solver_bvuge_var_def(solver, x, y, i)) {
	bit_blaster_make_bvuge2(solver->blaster, a->data, b->data, l, a->size);
      }
      break;

    case BVSGE_ATM:
      // Try variant definition. If that fails, bitblast.
      if (! bv_solver_bvsge_var_def(solver, x, y, i)) {
	bit_blaster_make_bvsge2(solver->blaster, a->data, b->data, l, a->size);
      }
      break;

    default:
      assert(false);
      abort();
    }
  }
  
}


/*
 * Process all variables that are not reachable from the atoms
 * but are useful none-the-less:
 * - if x is not a root variable and it's mapped to y, then
 *   we must bitblast x (and y too) to record the constraint
 *   x == y into the core.
 * - if x is attached to an egraph term, then it may be useful
 *   too so we must map x to an array of literals too.
 */
static void bv_solver_bitblast_variables(bv_solver_t *solver) {
  bv_vartable_t *vtbl;
  uint32_t i, n;
  thvar_t y;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (!bvvar_is_marked(vtbl, i)) {
      // i has not beem processed yet:
      if (bv_is_replaced(&solver->partition, i)) {
	/*
	 * i has a root variable y. Process the root y
	 * if it's not marked, then bitblast i.
	 */
	y = bv_partition_find_root(&solver->partition, i);
	assert(y != null_thvar && y != i);
	if (! bvvar_is_marked(vtbl, y)) {
	  bv_solver_bitblast_variable(solver, y);
	}
	bv_solver_bitblast_variable(solver, i);

      } else if (bvvar_has_eterm(&solver->vtbl, i)) {
	bv_solver_bitblast_variable(solver, i);
      }
    }
  }
}



/*
 * TEMPORARY COUNTERS
 */
static uint32_t num_eq_axioms = 0;
static uint32_t num_extra_eq_axioms = 0;
static uint32_t num_diseq_axioms = 0;
static uint32_t num_ge_axioms = 0;
static uint32_t num_sge_axioms = 0;



/*
 * Full bit-blasting:
 * - return true if no conflict is found 
 * - return false otherwise
 */
static bool bv_solver_bitblast(bv_solver_t *solver) {
  bool feasible;
#if TRACE
  double start, end;
#endif

  assert(! solver->bit_blasted);

#if TRACE
  printf("---> Starting conversion to bitblaster\n");
  printf("---> toplevel eq axioms: %"PRIu32"\n", num_eq_axioms);
  printf("---> toplevel diseq axioms: %"PRIu32"\n", num_diseq_axioms);
  printf("---> toplevel ge axioms: %"PRIu32"\n", num_ge_axioms);
  printf("---> toplevel sge axioms: %"PRIu32"\n", num_sge_axioms);
  printf("---> propagated eqs: %"PRIu32"\n", num_extra_eq_axioms);
  printf("---> atoms: %"PRIu32"\n", solver->atbl.natoms);
  printf("---> variables: %"PRIu32"\n", solver->vtbl.nvars);
  fflush(stdout);
  start = get_cpu_time();
#endif
  
  bv_solver_prepare_remap(solver);
  feasible = bv_solver_build_pseudo_maps(solver);
  if (! feasible) goto unsat;
  feasible = bv_solver_propagate_truth_assignment(solver);
  if (! feasible) goto unsat;

#if DUMP
  bv_solver_dump_state(solver, "yices_bvsolver1.dmp");
#endif

  bv_solver_prepare_blasting(solver);
  bv_solver_bitblast_all_atoms(solver);
  bv_solver_bitblast_variables(solver);

  solver->bit_blasted = true;

#if TRACE
  end = get_cpu_time();
  printf("---> no conflict after bitblasting: CPU time = %.4f s\n\n", time_diff(end, start));
#endif

#if DUMP
  bv_solver_dump_state(solver, "yices_bvsolver2.dmp");
#endif

  return true;

 unsat:

#if TRACE
  end = get_cpu_time();
  printf("---> unsat after bitblasting or check. Search time = %.4f s\n\n", time_diff(end, start));
  fflush(stdout);
#endif

  return false;
}








/*********************
 *  INTERNALIZATION  *
 ********************/

/*
 * These functions are used by the context to create atoms and variables
 * in the bit-vector solver. We export them for testing. They are normally
 * called via the bvsolver_interface_t descriptor.
 */

/*
 * Create a new variable of n bits
 */
thvar_t bv_solver_create_var(bv_solver_t *solver, uint32_t n) {
#if TRACE
  printf("---> bv: create_var (%"PRIu32" bits)\n", n);
#endif
  return make_var(&solver->vtbl, n);
}

/*
 * Create a variable equal to constant c
 */
thvar_t bv_solver_create_const(bv_solver_t *solver, bvconst_term_t *c) {
  uint32_t n;
  uint64_t aux;

#if TRACE
  printf("---> bv: create_const (%"PRIu32" bits)\n", c->nbits);
#endif

  n = c->nbits;
  if (n <= 64) {
    if (n <= 32) {
      aux = (uint64_t) c->bits[0];
    } else {
      aux = (((uint64_t) c->bits[1])<< 32) | c->bits[0];
    }
    assert(n == 64 || aux < (((uint64_t) 1)<<n)); // i.e. aux is normalized
    return get_small_const(&solver->vtbl, n, aux);
  } else {
    return get_big_const(&solver->vtbl, n, c->bits);
  }
}


/*
 * Internalize the bvarith expression p
 * - bv_map = store variable renaming. For every variable x of p,
 *   itable_get(bv_map, x) is the theory variable v that corresponds to x
 *   in the solver.
 */
thvar_t bv_solver_create_bvpoly(bv_solver_t *solver, bvarith_expr_t *p, itable_t *bv_map) {
#if TRACE
  printf("---> bv: create_poly (%"PRIu32" bits, %"PRIu32" vars)\n", p->size, solver->vtbl.nvars);
#endif
  return bv_solver_map_poly(solver, p, bv_map);
}


/*
 * Internalize the bit array b
 * - bv_map = variable renaming as above
 */
thvar_t bv_solver_create_bvlogic(bv_solver_t *solver, bvlogic_expr_t *b, itable_t *bv_map) {
#if TRACE
  printf("---> bv: create_bvlogic (%"PRIu32" bits)\n", b->nbits);
#endif
  return bv_solver_map_bitarray(solver, b, bv_map);
}


/*
 * Internalize the binary operation (op x y)
 */
thvar_t bv_solver_create_bvop(bv_solver_t *solver, bvop_t op, thvar_t x, thvar_t y) {
#if TRACE
  printf("---> bv: create_bvop (%"PRIu32" u_%"PRId32" u_%"PRId32")\n", op, x, y);
#endif
  switch (op) {
  case BVOP_DIV: 
    return map_udiv(solver, x, y);
  case BVOP_REM:
    return map_urem(solver, x, y);
  case BVOP_SDIV:
    return map_sdiv(solver, x, y);
  case BVOP_SREM:
    return map_srem(solver, x, y);
  case BVOP_SMOD:
    return map_smod(solver, x, y);

  case BVOP_SHL:
    return get_shl(&solver->vtbl, x, y);
  case BVOP_LSHR:
    return get_lshr(&solver->vtbl, x, y);
  case BVOP_ASHR:
    return get_ashr(&solver->vtbl, x, y);

  default:
    if (solver->env != NULL) {
      longjmp(*solver->env, INTERNAL_ERROR);
    }
    abort();
  }
}

/*
 * Internalize the if-then-else term (ite c x y)
 * - c is a literal in the core
 * - x and y are two previously created theory variables
 */
thvar_t bv_solver_create_ite(bv_solver_t *solver, literal_t c, thvar_t x, thvar_t y) {
  assert(c != true_literal && c != false_literal);
  return get_ite(&solver->vtbl, c, x, y);
}


/*
 * Attach egraph term t to variable x
 */
void bv_solver_attach_eterm(bv_solver_t *solver, thvar_t x, eterm_t t) {
  attach_eterm_to_bvvar(&solver->vtbl, x, t);
}


/*
 * Get the egraph term attached to x 
 * - return null_eterm if x has no term attached
 */
eterm_t bv_solver_eterm_of_var(bv_solver_t *solver, thvar_t x) {
  return bvvar_get_eterm(&solver->vtbl, x);
}



/*
 * Create atom (ge x y), i.e., (x <= y) with x and y interpreted
 * as unsigned n-bits integers
 */
literal_t bv_solver_create_ge_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_atomtable_t *atbl;
  uint32_t n;
  int32_t i;
  literal_t l;
  bvar_t v;

#if TRACE
  printf("---> bv: create_atom (ge u_%"PRId32" u_%"PRId32")\n", x, y);
#endif

  switch (bv_solver_check_uge(solver, x, y)) {
  case CODE_FALSE:
#if TRACE
    printf("---> false\n");
#endif
    return false_literal;

  case CODE_TRUE:
#if TRACE
    printf("---> false\n");
#endif
    return true_literal;

  case CODE_UNKNOWN:
    atbl = &solver->atbl;
    n = atbl->natoms;
    i = get_bvuge_atom(atbl, x, y);
    l = atbl->data[i].lit;
    if (l == null_literal) {
      assert(atbl->natoms > n);
      // new atom
      v = create_boolean_variable(solver->core);
      attach_atom_to_bvar(solver->core, v, bvatom_idx2tagged_ptr(i));
      l = pos_lit(v);
      atbl->data[i].lit = l;
    }
    return l;

  default:
    assert(false);
    abort();
  }
}


/*
 * Atom (sge x y), i.e., (x <= y) with x and y interpreted as 
 * signed integers (in 2's-complement representation)
 */
literal_t bv_solver_create_sge_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_atomtable_t *atbl;
  uint32_t n;
  int32_t i;
  literal_t l;
  bvar_t v;

#if TRACE
  printf("---> bv: create_atom (sge u_%"PRId32" u_%"PRId32")\n", x, y);
#endif

  switch (bv_solver_check_sge(solver, x, y)) {
  case CODE_FALSE:
    return false_literal;

  case CODE_TRUE:
    return true_literal;

  case CODE_UNKNOWN:
    atbl = &solver->atbl;
    n = atbl->natoms;
    i = get_bvsge_atom(atbl, x, y);
    l = atbl->data[i].lit;
    if (l == null_literal) {
      assert(atbl->natoms > n);
      // new atom
      v = create_boolean_variable(solver->core);
      attach_atom_to_bvar(solver->core, v, bvatom_idx2tagged_ptr(i));
      l = pos_lit(v);
      atbl->data[i].lit = l;
    }
    return l;
  
  default:
    assert(false);
    abort();
  }
}




/********************
 *  EQUALITY ATOMS  *
 *******************/

/*
 * Get atom (eq x y) in the atom table
 * - create it if it does not exist
 * - attach the atom to a boolean variable in the core
 * - return the literal representing the atom
 */
static literal_t bv_solver_make_eq_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_atomtable_t *atbl;
  ivector_t *a, *b;
  uint32_t n;
  int32_t i;
  literal_t l, l0;
  bvar_t v;

  atbl = &solver->atbl;
  n = atbl->natoms;
  i = get_bveq_atom(atbl, x, y);
  l = atbl->data[i].lit;
  if (var_of(l) == null_bvar) {
    /*
     * New atom
     */
    assert(atbl->natoms > n);

    if (solver->bit_blasted) {
      /*
       * Atom created after bit-blasting
       */
      // bitbast x and y
      a = &solver->a_vector;
      b = &solver->b_vector;
      bv_solver_bitblast_variable(solver, x);
      bv_solver_bitblast_variable(solver, y);
      collect_var_literals(solver, x, a);
      collect_var_literals(solver, y, b);
      assert(a->size == b->size && a->size > 0);

      // create l = (bveq a b)
      l = bit_blaster_make_bveq(solver->blaster, a->data, b->data, a->size);
      atbl->data[i].lit = l;

      // We must attach the atom to the core as this is used
      // to figure out how to generate explanations.
      v = var_of(l);
      if (bvar_has_atom(solver->core, v)) {
	// we need a fresh literal
	v = create_boolean_variable(solver->core);
	l0 = pos_lit(v);
	atbl->data[i].lit = l0;
	// assert (l == l0) in the core
	bit_blaster_eq(solver->blaster, l, l0);
	l = l0;
      }
      attach_atom_to_bvar(solver->core, v, bvatom_idx2tagged_ptr(i));
      // TEST
      //      set_bvar_polarity(solver->core, v, true);

#if TRACE
      printf("---> bv: on_the_fly_atom ");
      print_literal(stdout, l);
      printf(" := (eq u_%"PRId32" u_%"PRId32")\n", x, y);
#endif


    } else {
      /*
       * before bit-blasting: assign a fresh
       * variable to the atom.
       */
      v = create_boolean_variable(solver->core);
      l = pos_lit(v);
      atbl->data[i].lit = l;
      attach_atom_to_bvar(solver->core, v, bvatom_idx2tagged_ptr(i));

#if TRACE
      printf("---> bv: new atom ");
      print_literal(stdout, l);
      printf(" := (eq u_%"PRId32" u_%"PRId32")\n", x, y);
#endif

    }
  }

  return l;
}


/*
 * Create atom (eq x y) and return the corresponding core literal
 * Check whether (eq x y) simplifies to true or false.
 * Rewrite atoms of the form (eq x 0b0) to not (eq x 0b1).
 */
literal_t bv_solver_create_eq_atom(bv_solver_t *solver, thvar_t x, thvar_t y) {  
  bv_vartable_t *vtbl;
  literal_t eq;

#if TRACE
  printf("---> bv: create_atom (eq u_%"PRId32" u_%"PRId32")\n", x, y);
#endif

  if (bv_solver_check_eq(solver, x, y)) {
    return true_literal;
  }

  if (bv_solver_check_diseq(solver, x, y)) {
    return false_literal;
  }


  // try eq + ite simplifications
  eq = bv_solver_simplify_eq_ite(solver, x, y);
  if (eq != null_literal) {
    return eq;
  }

  vtbl = &solver->vtbl;
  if (bvvar_bitsize(vtbl, x) == 1) {
    assert(bvvar_bitsize(vtbl, y) == 1);

    if (thvar_is_bv1false(vtbl, x)) {
      // rewrite (bveq 0b0 y) to (not (bveq 0b1 y))
      x = get_small_const(vtbl, 1, 1); // x = 0b1

      // BUG fix: if 0b1 was just created, it's not mapped to 
      // a pseudo literal and bv_solver_make_eq_atom will crash
      if (solver->bit_blasted && vtbl->map[x].lit == null_literal) {
	vtbl->map[x].lit = true_literal;
      }
      return not(bv_solver_make_eq_atom(solver, x, y));
    }

    if (thvar_is_bv1false(vtbl, y)) {
      // rewrite (bveq x 0b0) to (not (bveq x 0b1))
      y = get_small_const(vtbl, 1, 1); // y = 0b1
      if (solver->bit_blasted && vtbl->map[y].lit == null_literal) {
	vtbl->map[y].lit = true_literal;
      }
      return not(bv_solver_make_eq_atom(solver, x, y));
    }
  }

  // try simplification then construct the atom
  bv_solver_simplify_eq(solver, &x, &y);
  return bv_solver_make_eq_atom(solver, x, y);
}



/***********************************
 *  TOP-LEVEL ASSERTIONS (AXIOMS)  *
 **********************************/

/*
 * Assert the top-level equality (x == y) or disequality (x != y)
 * - tt = true: equality
 * - tt = false: disequality
 */
void bv_solver_assert_eq_axiom(bv_solver_t *solver, thvar_t x, thvar_t y, bool tt) {
  bv_atomtable_t *atbl;
  uint32_t n;
  int32_t i;
  literal_t l;

  if (tt) {

#if TRACE
    printf("---> bv: assert_axiom (eq u_%"PRId32" u_%"PRId32")\n", x, y);
#endif
    process_eq_axiom(solver, x, y);
    num_eq_axioms ++;

  } else if (diseq_axiom_convertible_to_eq(solver, x, y)) {

#if TRACE
    printf("---> bv: assert_axiom (not (eq u_%"PRId32" u_%"PRId32"))\n", x, y);
    printf("     converted to eq\n");
#endif
    convert_diseq_axiom_to_eq(solver, x, y);
    num_eq_axioms ++;

  } else {

#if TRACE
    printf("---> bv: assert_axiom (not (eq u_%"PRId32" u_%"PRId32"))\n", x, y);
#endif

    if (bv_solver_check_eq(solver, x, y)) {
      add_empty_clause(solver->core); // Conflict
    } else if (! bv_solver_check_diseq(solver, x, y)) {
      /*
       * Add the atom to the table
       */
      atbl = &solver->atbl;
      n = atbl->natoms;
      i = get_bveq_atom(atbl, x, y);
      l = atbl->data[i].lit;
      if (l == null_literal) {
	assert(atbl->natoms > n);
	// new atom: mark it as false
	atbl->data[i].lit = false_literal;
      } else {
	// existing atom: assert not(l)
	add_unit_clause(solver->core, not(l));
      }
    }
    num_diseq_axioms ++;
  }
}


/*
 * Build pos_lit(v) or neg_lit(v), depending on tt
 */
static inline literal_t make_lit(bvar_t v, bool tt) {
  return tt ? pos_lit(v) : neg_lit(v);
}


/*
 * Add the axiom (bvuge x y) or its negation
 * - if tt, assert (x >= y), otherwise assert(x < y)
 * - record a conflict if this assertion is known to be false
 * - do nothing if this assertion is already konwn to be true
 * - otherwise, add atom (uge x y) to the atom table
 *   mark is as an axiom by setting its boolean var to null
 *   record in atom->lit whether it's asserted true or false
 */
void bv_solver_assert_ge_axiom(bv_solver_t *solver, thvar_t x, thvar_t y, bool tt) {
  bv_atomtable_t *atbl;
  uint32_t n;
  int32_t i;
  literal_t l;

  i = bv_solver_check_uge(solver, x, y);
  if (i == CODE_UNKNOWN) {
    /*
     * Create an atom and assert it as true or false
     */
    atbl = &solver->atbl;
    n = atbl->natoms;
    i = get_bvuge_atom(atbl, x, y);
    l = atbl->data[i].lit;
    if (l == null_literal) {
      assert(atbl->natoms > n);
      // new atom: mark it as true or false
      atbl->data[i].lit = make_lit(bool_const, tt);

    } else if (tt) {
      add_unit_clause(solver->core, l);
    } else {
      add_unit_clause(solver->core, not(l));
    }

  } else if ((tt && i == CODE_FALSE) || (!tt && i == CODE_TRUE)) {
    // Conflict
    add_empty_clause(solver->core);
  }

  num_ge_axioms ++;
}



/*
 * Add the axiom (bvsge x y) or its negation
 * - if tt, assert (x >= y), otherwise assert(x < y)
 * - record a conflict if this assertion is known to be false
 * - do nothing if this assertion is already konwn to be true
 * - otherwise, add atom (uge x y) to the atom table
 *   mark is as an axiom by setting its boolean var to null
 *   record in atom->lit whether it's asserted true or false
 */
void bv_solver_assert_sge_axiom(bv_solver_t *solver, thvar_t x, thvar_t y, bool tt) {
  bv_atomtable_t *atbl;
  uint32_t n;
  int32_t i;
  literal_t l;
  
  i = bv_solver_check_sge(solver, x, y);
  if (i == CODE_UNKNOWN) {
    /*
     * Create the atom and mark it as true/false axiom
     */
    atbl = &solver->atbl;
    n = atbl->natoms;
    i = get_bvsge_atom(atbl, x, y);
    l = atbl->data[i].lit;
    if (l == null_literal) {
      assert(atbl->natoms > n);
      // new atom
      atbl->data[i].lit = make_lit(bool_const, tt);

    } else if (tt) {
      add_unit_clause(solver->core, l);
    } else {
      add_unit_clause(solver->core, not(l));
    }

  } else if ((tt && i == CODE_FALSE) || (!tt && i == CODE_TRUE)) {
    // Conflict
    add_empty_clause(solver->core);
  }

  num_sge_axioms ++;
}





/**********************
 *  CACHE AND LEMMAS  *
 *********************/

/*
 * Return the cache:
 * - allocate and initialize it if needed
 */
static cache_t *bv_solver_get_cache(bv_solver_t *solver) {
  cache_t *c;

  c = solver->cache;
  if (c == NULL) {
    c = (cache_t *) safe_malloc(sizeof(cache_t));
    // initialize then synchronize the cache with 
    // the current push/pop level
    init_cache(c);
    cache_set_level(c, solver->base_level);
    solver->cache = c;
  }

  return c;
}


/*
 * Create the lemma (eq t1 t2) <=> (bveq x1 x2)
 * - x1 and x2 must be distinct theory variables
 * - t1 and t2 are the corresponding egraph terms
 */
static void bv_solver_bvequiv_lemma(bv_solver_t *solver, thvar_t x1, thvar_t x2) {
  cache_t *cache;
  cache_elem_t *e;
  thvar_t aux;
  literal_t l, eq;
  eterm_t t1, t2;

  assert(solver->egraph != NULL && x1 != x2);

  // normalize: we want x1 < x2
  if (x2 < x1) {
    aux = x1; x1 = x2; x2 = aux;
  }

#if TRACE
  t1 = bvvar_get_eterm(&solver->vtbl, x1);
  t2 = bvvar_get_eterm(&solver->vtbl, x2);
  printf("---> bvequiv lemma:\n");
  printf("     x1 = ");
  print_bvsolver_var(stdout, x1);
  printf(", t1 = ");
  print_eterm_id(stdout, t1);
  printf("\n");
  printf("     x2 = ");
  print_bvsolver_var(stdout, x2);
  printf(", t2 = ");
  print_eterm_id(stdout, t2);
  printf("\n");
#endif

  cache = bv_solver_get_cache(solver);
  e = cache_get(cache, BVEQUIV_LEMMA, x1, x2);
  if (e->flag == NEW_CACHE_ELEM) {
    // create the lemma
    e->flag = ACTIVE_BV_LEMMA;

    l = bv_solver_create_eq_atom(solver, x1, x2);

    t1 = bvvar_get_eterm(&solver->vtbl, x1);
    t2 = bvvar_get_eterm(&solver->vtbl, x2);
    assert(t1 != null_eterm && t2 != null_eterm);
    eq = egraph_make_simple_eq(solver->egraph, pos_occ(t1), pos_occ(t2));

    // two clauses: (l => eq) and (eq => l)
    add_binary_clause(solver->core, not(l), eq);
    add_binary_clause(solver->core, l, not(eq));

#if TRACE
    printf("---> bvequiv lemma:\n");
    printf("     x1 = ");
    print_bvsolver_var(stdout, x1);
    printf(", t1 = ");
    print_eterm_id(stdout, t1);
    printf("\n");
    printf("     x2 = ");
    print_bvsolver_var(stdout, x2);
    printf(", t2 = ");
    print_eterm_id(stdout, t2);
    printf("\n");
    printf("     (bveq x1 x2) = ");
    print_literal(stdout, l);
    printf("\n");
    printf("     (eq t1 t2) = ");
    print_literal(stdout, eq);
    printf("\n");
    printf("     ");
    print_bvsolver_vardef(stdout, solver, x1);
    printf("     ");
    print_bvsolver_vardef(stdout, solver, x2);
    printf("     ");
    print_eterm_def(stdout, solver->egraph, t1);
    printf("     ");
    print_eterm_def(stdout, solver->egraph, t2);
    printf("     ");
    print_literal(stdout, eq);
    printf(" := ");
    print_egraph_atom_of_literal(stdout, solver->egraph, eq);
    printf("\n\n");
#endif

  }
}




/***********************************************************
 *  EQUALITIES AND DISEQUALITIES RECEIVED FROM THE EGRAPH  *
 **********************************************************/

/*
 * Process equality (x1 == x2) received from the egraph
 * - create the lemma (eq t1 t2) <=> (bveq x1 x2)
 *   where t1 and t2 are the egraph terms for x1 and x2, respectively.
 * - if there's a conflict, it will be handled by smt_core when the lemma
 *   is processed.
 */
static void bv_solver_process_egraph_eq(bv_solver_t *solver, thvar_t x1, thvar_t x2) {
#if TRACE
  printf("\n---> bv: process_egraph_eq u_%"PRId32" u_%"PRId32" [dlevel = %"PRIu32"]\n", x1, x2, solver->decision_level);
  printf("     ");
  print_bvsolver_vardef(stdout, solver, x1);
  printf("     ");
  print_bvsolver_vardef(stdout, solver, x2);
#endif

  bv_solver_bvequiv_lemma(solver, x1, x2);
}



/*
 * Process all assertions in the egraph queue
 * - we do nothing for disequalities or distinct 
 * - disequalities are handled lazily in reconcile_model
 */
static void bv_solver_process_egraph_assertions(bv_solver_t *solver) {
  eassertion_t *a, *end;

  a = eassertion_queue_start(&solver->egraph_queue);
  end = eassertion_queue_end(&solver->egraph_queue);

  while (a < end) {
    switch (eassertion_get_kind(a)) {
    case EGRAPH_VAR_EQ:
      bv_solver_process_egraph_eq(solver, a->var[0], a->var[1]);
      break;
    case EGRAPH_VAR_DISEQ:
    case EGRAPH_VAR_DISTINCT:
      break;

    default:
      assert(false);
      break;
    }
    a = eassertion_next(a);
  }

  reset_eassertion_queue(&solver->egraph_queue);
}



/*
 * Create a variable after bit-blasting (e.g., a skolem constant created
 * by the egraph + array solver).
 */
thvar_t bv_solver_create_on_the_fly_var(bv_solver_t *solver, uint32_t n) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  thvar_t x;

#if TRACE
  printf("---> bv: create_var (%"PRIu32" bits)\n", n);
#endif

  vtbl = &solver->vtbl;
  x = make_var(vtbl, n);
  if (solver->bit_blasted) {
    rmap = solver->remap;
    assert(n == bvvar_bitsize(vtbl, x) && rmap != NULL);

    // attach a fresh array of pseudo-literals to x
    if (n == 1) {
      vtbl->map[x].lit = remap_table_fresh_lit(rmap);
    } else {
      vtbl->map[x].array = remap_table_fresh_array(rmap, n);
    }

    // assign real literals to x
    bv_solver_bitblast_variable(solver, x);
  }

  return x;
}


/****************
 *  STATISTICS  *
 ***************/

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






/********************************
 *  FULL SOLVER INITIALIZATION  *
 *******************************/

/*
 * Initialize a bit-vector solver
 * - core = the attached smt core
 * - egraph = the attached egraph (or NULL)
 * - vm = bit-vector variable manager for all input
 * - tbl = node table for the XOR/OR graph
 */
void init_bv_solver(bv_solver_t *solver, smt_core_t *core, egraph_t *egraph, 
		    bv_var_manager_t *vm, node_table_t *tbl) {

  thvar_t x;

  solver->core = core;
  solver->egraph = egraph;

  solver->base_level = 0;
  solver->decision_level = 0;
  solver->bv_manager = vm;
  solver->nodes = tbl;

  init_bv_vartable(&solver->vtbl);
  init_bv_atomtable(&solver->atbl);
  init_itable(&solver->node_map, 0);    // use default size
  init_bv_partition(&solver->partition);

  solver->bounds = NULL;
  solver->queue = NULL;
  solver->cache = NULL;
  solver->blaster = NULL;
  solver->remap = NULL;
  solver->bit_blasted = false;

  init_eassertion_queue(&solver->egraph_queue);

  init_bv_trail(&solver->trail_stack);

  init_bvpoly_buffer(&solver->buffer);
  init_vpbuffer(&solver->prod_buffer, 4);
  init_ivector(&solver->aux_vector, 0);
  init_bvconstant(&solver->aux1);
  init_bvconstant(&solver->aux2);
  init_ivector(&solver->a_vector, 0);
  init_ivector(&solver->b_vector, 0);

  // create the constant
  x = make_bit_true(&solver->vtbl);
  assert(x == constant_node);

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
  // to avoid double-frees: we clear map[x].array if x is not a root
  clean_array_maps(solver);
  delete_bv_vartable(&solver->vtbl);
  delete_bv_atomtable(&solver->atbl);
  delete_itable(&solver->node_map);
  delete_bv_partition(&solver->partition);

  if (solver->bounds != NULL) {
    delete_bvbound_cache(solver->bounds);
    safe_free(solver->bounds);
    solver->bounds = NULL;
  }

  if (solver->queue != NULL) {
    delete_bv_prop_queue(solver->queue);
    safe_free(solver->queue);
    solver->queue = NULL;
  }

  if (solver->cache != NULL) {
    delete_cache(solver->cache);
    safe_free(solver->cache);
    solver->cache = NULL;
  }

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
  delete_vpbuffer(&solver->prod_buffer);
  delete_ivector(&solver->aux_vector);
  delete_bvconstant(&solver->aux1);
  delete_bvconstant(&solver->aux2);
  delete_ivector(&solver->a_vector);
  delete_ivector(&solver->b_vector);

  delete_used_vals(&solver->used_vals);
}





/***********************
 *  CONTROL FUNCTIONS  *
 **********************/

/*
 * The core or egraph invokes these functions via the smt or ctrl interface
 * descriptors. We export them for testing.
 */

/*
 * Signal a new round of assertions (before start_search):
 * - do nothing for now
 */
void bv_solver_start_internalization(bv_solver_t *solver) {
}


/*
 * Prepare for search after internalization
 * - bitblast the constraints
 * - initialize the bit_solver
 * - if a conflict is detected add the empty clause
 *   in the core.
 */
void bv_solver_start_search(bv_solver_t *solver) {
  bool feasible;

  if (! solver->bit_blasted) {
    feasible = bv_solver_bitblast(solver);
    if (! feasible) {
      add_empty_clause(solver->core);
    }
  }
}


/*
 * Assert atom attached to literal l
 * This function is called when l is assigned to true by the core
 * - atom is the arithmetic atom attached to a boolean variable v = var_of(l)
 * - if l is positive (i.e., pos_lit(v)), assert the atom
 * - if l is negative (i.e., neg_lit(v)), assert its negation
 * Return false if that causes a conflict, true otherwise.
 */
bool bv_solver_assert_atom(bv_solver_t *solver, void *atom, literal_t l) {
  bvatm_t *atm;
  int32_t id;

  id = bvatom_tagged_ptr2idx(atom);
  assert(0 <= id && id < solver->atbl.natoms);
  atm = solver->atbl.data + id;
  assert(bvatm_bvar(atm) == var_of(l));

  if (!solver->bit_blasted) {
    /*
     * start_search has not been called yet
     * so this must be part of 'base_propagate'
     */
    assert(solver->decision_level == solver->base_level);

    /*
     * atm can be treated as an axiom: if it's (bveq x y)
     * we try to merge x and y
     */
    if (bvatm_is_eq(atm)) {
      if (is_pos(l)) {
	num_extra_eq_axioms ++;
	return process_eq_axiom(solver, atm->left, atm->right);
      } else if (diseq_axiom_convertible_to_eq(solver, atm->left, atm->right)) {
	num_extra_eq_axioms ++;
	return convert_diseq_axiom_to_eq(solver, atm->left, atm->right);
      }
    }

    // default: check whether there's a trivial unsat
    return check_toplevel_atom(solver, atm);

  } else {
    /*
     * After bit-blasting, there's nothing to do
     */
    return true;
  }

}

/*
 * Perform one round of propagation:
 * - return true if no conflict was detected
 * - return false if a conflict was detected, in that case the conflict
 *   clause is stored in the core
 */
bool bv_solver_propagate(bv_solver_t *solver) {
  if (!solver->bit_blasted && solver->queue != NULL) {
    /*
     * Before bit-blasting: try local propagation
     */
    return process_bv_prop_queue(solver);
  } else if (eassertion_queue_is_nonempty(&solver->egraph_queue)) {
    /*
     * After bit-blasting: process the egraph queue.
     * This may create lemmas but does not cause a conflict.
     */
    bv_solver_process_egraph_assertions(solver);    
  }

  // default: no conflict
  return true;
}


/*
 * Support for theory-branching heuristic
 * - evaluate atom attached to l in the current simplex assignment
 * - the result is either l or (not l)
 * - if atom is true, return pos_lit(var_of(l))
 * - if atom is false, return neg_lit(var_of(l))
 */
literal_t bv_solver_select_polarity(bv_solver_t *solver, void *atom, literal_t l) {
  return l;
}


/*
 * Final check: nothing to do
 */
fcheck_code_t bv_solver_final_check(bv_solver_t *solver) {
#if TRACE
  printf("---> bv: final check\n");
  fflush(stdout);
#endif
  return FCHECK_SAT;
}


/*
 * Start a new decision level
 */
void bv_solver_increase_decision_level(bv_solver_t *solver) {
  uint32_t k;

  k = solver->decision_level + 1;
  solver->decision_level = k;

#if DUMP
  if (solver->core->stats.decisions == 1) {
    bv_solver_dump_state(solver, "yices_bvsolver3.dmp");
  }
#endif
}


/*
 * Backtrack to back_level
 */
void bv_solver_backtrack(bv_solver_t *solver, uint32_t back_level) {
  assert(solver->base_level <= back_level && back_level < solver->decision_level);
  reset_eassertion_queue(&solver->egraph_queue);
  solver->decision_level = back_level;
}


/*
 * Push/pop/reset
 */
void bv_solver_push(bv_solver_t *solver) {
  uint32_t nv, na;

  nv = solver->vtbl.nvars;
  na = solver->atbl.natoms;
  bv_trail_save(&solver->trail_stack, nv, na);

  if (solver->cache != NULL) {
    cache_push(solver->cache);
  }

  solver->base_level ++;
  bv_solver_increase_decision_level(solver);

  itable_push(&solver->node_map);
  bv_partition_push(&solver->partition);
}

void bv_solver_pop(bv_solver_t *solver) {
  bv_trail_t *top;

  assert(solver->base_level > 0 && solver->base_level == solver->decision_level);

  solver->base_level --;
  bv_solver_backtrack(solver, solver->base_level);

  top = bv_trail_top(&solver->trail_stack);
  bv_vartable_remove_vars(&solver->vtbl, top->nvars);
  bv_atomtable_remove_atoms(&solver->atbl, top->natoms);

  bv_trail_pop(&solver->trail_stack);

  if (solver->cache != NULL) {
    cache_pop(solver->cache);
  }

  itable_pop(&solver->node_map);
  bv_partition_pop(&solver->partition);

  // the constant should still be present
  assert(solver->vtbl.nvars > constant_node && 
	 bvvar_tag(&solver->vtbl, constant_node) == BVTAG_TRUE);
}


void bv_solver_reset(bv_solver_t *solver) {
  thvar_t x;

  solver->base_level = 0;
  solver->decision_level = 0;

  clean_array_maps(solver);
  reset_bv_vartable(&solver->vtbl);
  reset_bv_atomtable(&solver->atbl);
  reset_itable(&solver->node_map);
  reset_bv_partition(&solver->partition);

  solver->bit_blasted = false;

  if (solver->bounds != NULL) {
    delete_bvbound_cache(solver->bounds);
    safe_free(solver->bounds);
    solver->bounds = NULL;
  }

  if (solver->queue != NULL) {
    delete_bv_prop_queue(solver->queue);
    safe_free(solver->queue);
    solver->queue = NULL;
  }

  if (solver->cache != NULL) {
    delete_cache(solver->cache);
    safe_free(solver->cache);
    solver->cache = NULL;
  }

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
  vpbuffer_reset(&solver->prod_buffer);
  ivector_reset(&solver->aux_vector);
  ivector_reset(&solver->a_vector);
  ivector_reset(&solver->b_vector);

  // re-create the constant
  x = make_bit_true(&solver->vtbl);
  assert(x == constant_node);

  reset_used_vals(&solver->used_vals);
}






/*******************************
 *  INTERFACE WITH THE EGRAPH  *
 ******************************/

/*
 * Assertion (eq x1 x2) from the egraph:
 * - turn it into an axiom if possible
 * - otherwise, push the assertion into the queue
 */
void bv_solver_assert_var_eq(bv_solver_t *solver, thvar_t x1, thvar_t x2) {
  assert(bvvar_has_eterm(&solver->vtbl, x1) && bvvar_has_eterm(&solver->vtbl, x2));

#if TRACE
  printf("---> bvsolver: received egraph equality: ");
  print_bvsolver_var(stdout, x1);
  printf(" = ");
  print_bvsolver_var(stdout, x2);
  printf("\n");
#endif

  if (! solver->bit_blasted) {
    /*
     * Start search has not been called: we treat (bveq x1 x2) as an axiom
     */
    assert(solver->decision_level == solver->base_level);
    num_extra_eq_axioms ++;
    process_eq_axiom(solver, x1, x2);

  } else {
    /*
     * Push (eq x1 x2) into the egraph queue for future processing
     */
    eassertion_push_eq(&solver->egraph_queue, x1, x2);
  }
}


/*
 * Add the constraint (x1 != x2) propagated from the egraph as a axiom
 */
static void diseq_axiom_from_egraph(bv_solver_t *solver, thvar_t x1, thvar_t x2) {
  bv_atomtable_t *atbl;
  uint32_t n;
  int32_t i;
  literal_t l;

  assert(solver->decision_level == solver->base_level && !solver->bit_blasted);

  if (diseq_axiom_convertible_to_eq(solver, x1, x2)) {
    // rewrite (x1 != 0b0) to (x1 == 0b1) etc.
    convert_diseq_axiom_to_eq(solver, x1, x2);
    num_extra_eq_axioms ++;

  } else if (bv_solver_check_eq(solver, x1, x2)) {
    // conflict: mark the whole thing as unsat
    add_empty_clause(solver->core);

  } else if (!bv_solver_check_diseq(solver, x1, x2)) {
    /*
     * create the atom 
     */
    atbl = &solver->atbl;
    n = atbl->natoms;
    i = get_bveq_atom(atbl, x1, x2);
    l = atbl->data[i].lit;
    if (l == null_literal) {
      // new atom: mark it as false
      assert(atbl->natoms > n);
      atbl->data[i].lit = false_literal;
    } else {
      // the atom exists already: assert not(l)
      add_unit_clause(solver->core, not(l));
    }
    num_diseq_axioms ++;
  }
}



/*
 * Assert that x1 and x2 are distinct
 * - hint = egraph hint for the disequality
 */
void bv_solver_assert_var_diseq(bv_solver_t *solver, thvar_t x1, thvar_t x2, composite_t *hint) {
  assert(bvvar_has_eterm(&solver->vtbl, x1) && bvvar_has_eterm(&solver->vtbl, x2));
  
#if TRACE
  printf("---> bvsolver: received egraph disequality: ");
  print_bvsolver_var(stdout, x1);
  printf(" != ");
  print_bvsolver_var(stdout, x2);
  printf("\n");
#endif

  if (! solver->bit_blasted) {
    /*
     * Start search has not been called: we treat not (bveq x1 x2) as an axiom
     */
    assert(solver->decision_level == solver->base_level);
    diseq_axiom_from_egraph(solver, x1, x2);

  } else {
    /*
     * Push (diseq x1 x2) into the queue for future processing
     */
    eassertion_push_diseq(&solver->egraph_queue, x1, x2, hint);
  }
}


/*
 * Assert that a[0,...n-1] are all distinct 
 * - hint = hint for egraph explanation
 */
void bv_solver_assert_var_distinct(bv_solver_t *solver, uint32_t n, thvar_t *a, composite_t *hint) {
  thvar_t x, y;
  uint32_t i, j;

  if (! solver->bit_blasted) {
    /*
     * Process all pairwise disequalities as axioms
     */
    assert(solver->decision_level == solver->base_level);

    for (i=0; i<n; i++) {
      x = a[i];
      assert(bvvar_has_eterm(&solver->vtbl, x));
      for (j=i+1; j<n; j++) {
	y = a[j];
	diseq_axiom_from_egraph(solver, x, y);
      }
    }

  } else {
    /*
     * Add (distinct a[0] ... a[n-1]) to the egraph queue
     */
    eassertion_push_distinct(&solver->egraph_queue, n, a, hint);
  }
}



/*
 * Check whether x1 and x2 are distinct at the base level
 */
bool bv_solver_check_disequality(bv_solver_t *solver, thvar_t x1, thvar_t x2) {
  bv_vartable_t *vtbl;
  ivector_t *a, *b;
  literal_t aux;
  bool r;

  vtbl = &solver->vtbl;
  if (solver->bit_blasted && bvvar_is_marked(vtbl, x1) && bvvar_is_marked(vtbl, x2)) {
    // both x1 and x2 have been bitblasted
    a = &solver->a_vector;
    b = &solver->b_vector;
    collect_var_literals(solver, x1, a);
    collect_var_literals(solver, x2, b);
    assert(a->size == b->size && a->size > 0);
    aux = bit_blaster_eval_bveq(solver->blaster, a->size, a->data, b->data);

    r = (aux == false_literal); // false_literal means a != b
  } else {
    r = bv_solver_check_diseq(solver, x1, x2);
  }


#if TRACE
  printf("---> bv_solver: check_disequality(u_%"PRId32" u_%"PRId32"): result = ", x1, x2);
  if (r) {
    printf("true\n");
  } else {
    printf("false\n");
  }
  if (solver->bit_blasted) {
    printf("     after bitblasting\n");
  } else {
    printf("     before bitblasting\n");
  }
#endif

  return r;
}



/*
 * Check whether x1 and x2 are equal in the model 
 * - return false if x1 and x2 have different bitsize
 * - otherwise, check the literal values in the core
 */
static bool bv_solver_var_equal_in_model(bv_solver_t *solver, thvar_t x1, thvar_t x2) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  smt_core_t *core;
  literal_t s1, s2;
  literal_t l1, l2;  
  bval_t v1, v2;
  uint32_t i, n;

  assert(solver->bit_blasted);

  vtbl = &solver->vtbl;
  rmap = solver->remap;
  core = solver->core;

  n = bvvar_bitsize(vtbl, x1);
  if (n != bvvar_bitsize(vtbl, x2)) {
    return false;
  }

  if (n == 1) {
    s1 = vtbl->map[x1].lit;
    s2 = vtbl->map[x2].lit;
    l1 = remap_table_find(rmap, s1);
    l2 = remap_table_find(rmap, s2);
    assert(l1 != null_literal && l2 != null_literal);
    v1 = literal_value(core, l1);
    v2 = literal_value(core, l2);
    assert(v1 != VAL_UNDEF && v2 != VAL_UNDEF);
    return v1 == v2;

  } else {

    assert(vtbl->map[x1].array != NULL && vtbl->map[x2].array != NULL);

    for (i=0; i<n; i++) {
      s1 = vtbl->map[x1].array[i];
      s2 = vtbl->map[x2].array[i];
      l1 = remap_table_find(rmap, s1);
      l2 = remap_table_find(rmap, s2);
      assert(l1 != null_literal && l2 != null_literal);
      v1 = literal_value(core, l1);
      v2 = literal_value(core, l2);
      assert(v1 != VAL_UNDEF && v2 != VAL_UNDEF);
      if (v1 != v2) {
	return false;
      }
    }

    return true;
  }
}



/*
 * 32bit word of x's value formed of bits[k ... k+31]
 * - k must be smaller than x's bit size
 * - if k+31 >= bitsize, then the value is padded with 0s
 */
static uint32_t bvsolver_word_value_in_model(bv_solver_t *solver, thvar_t x, uint32_t k) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  smt_core_t *core;
  literal_t s, l;
  uint32_t i, n, c;

  assert(solver->bit_blasted);

  vtbl = &solver->vtbl;
  rmap = solver->remap;
  core = solver->core;

  n = bvvar_bitsize(vtbl, x);
  assert(k < n);

  c = 0;
  if (n == 1) {
    s = vtbl->map[x].lit;
    l = remap_table_find(rmap, s);
    assert(l != null_literal && literal_value(core, l) != VAL_UNDEF);
    if (literal_value(core, l) == VAL_TRUE) {
      c = 1;
    }   

  } else {

    assert(vtbl->map[x].array != NULL);

    if (k + 32 <= n) {
      n = k+32;
    }

    for (i=k; i<n; i++) {
      s = vtbl->map[x].array[i];
      l = remap_table_find(rmap, s);
      assert(l != null_literal && literal_value(core, l) != VAL_UNDEF);
      if (literal_value(core, l) == VAL_TRUE) {
	c |= 1; // set low-order bit
      }
      c <<= 1;
    }
  }

  return c;
}





/*
 * Hash function: if x and y have the same value then hash(x) == hash(y)
 * - this is based on Jensen's lookup3 code (public domain)
 */
#define rot(x,k) (((x)<<(k)) | ((x)>>(32-(k))))

#define mix(a,b,c) \
{ \
  a -= c;  a ^= rot(c, 4);  c += b; \
  b -= a;  b ^= rot(a, 6);  a += c; \
  c -= b;  c ^= rot(b, 8);  b += a; \
  a -= c;  a ^= rot(c,16);  c += b; \
  b -= a;  b ^= rot(a,19);  a += c; \
  c -= b;  c ^= rot(b, 4);  b += a; \
}

#define final(a,b,c) \
{ \
  c ^= b; c -= rot(b,14); \
  a ^= c; a -= rot(c,11); \
  b ^= a; b -= rot(a,25); \
  c ^= b; c -= rot(b,16); \
  a ^= c; a -= rot(c,4);  \
  b ^= a; b -= rot(a,14); \
  c ^= b; c -= rot(b,24); \
}

static uint32_t bvsolver_model_hash(bv_solver_t *solver, thvar_t x) {
  uint32_t k, n;
  uint32_t a, b, c;
  
  n = bvvar_bitsize(&solver->vtbl, x);
  k = 0;

  a = b = c = 0xdeadbeed + (n << 2);

  while (n > 96) { // more than 3 words
    a += bvsolver_word_value_in_model(solver, x, k);
    b += bvsolver_word_value_in_model(solver, x, k+32);
    c += bvsolver_word_value_in_model(solver, x, k+64);
    mix(a, b, c);
    n -= 96;
    k += 96;
  }

  // last three words
  assert(1 <= n && n <= 96);
  switch ((n+31) >> 5) {
  case 3: c += bvsolver_word_value_in_model(solver, x, k+64);
  case 2: b += bvsolver_word_value_in_model(solver, x, k+32);
  case 1: a += bvsolver_word_value_in_model(solver, x, k);
    final(a, b, c);
    break;
  default:
    assert(false);
    break;
  }

  return c;
}



/*
 * Check whether x is a root variable:
 * - x is root if it has an egraph term t and x is the theory
 *   variable in the class of t.
 */
static inline bool is_root_var(bv_solver_t *solver, thvar_t x) {
  egraph_t *egraph;
  eterm_t t;

  t = bvvar_get_eterm(&solver->vtbl, x);
  egraph = solver->egraph;
  return (t != null_eterm) && 
    (egraph_class_thvar(egraph, egraph_term_class(egraph, t)) == x);
}


/*
 * Find root variable for variable x
 * - we pick the theory variable in the egraph class of term of x
 */
static inline thvar_t root_var(bv_solver_t *solver, thvar_t x) {
  egraph_t *egraph;
  eterm_t t;

  assert(0 <= x && x < solver->vtbl.nvars);
  egraph = solver->egraph;
  t = solver->vtbl.eterm[x];
  return egraph_class_thvar(egraph, egraph_term_class(egraph, t));
}



#if 0

/*
 * Search for inconsistencies between the egraph and the bitvector model
 * - An inconsistency is a pair of bit-vector variables x and y
 *   such that x and y have the same value in the solver but 
 *   term_of(x) and term_of(y) are in different classes in the egraph.
 * - To resolve inconsistencies we add the lemma 
 *     (bveq x y) <=> (eq term_of(x) term_of(y))
 * - max_eq = bound on the number of lemma instances
 * - Return the number of instances created
 */
uint32_t bv_solver_reconcile_model(bv_solver_t *solver, uint32_t max_eq) {
  int_hclass_t hclass;
  int32_t i, x, n;
  uint32_t neq;
#if TRACE
  eterm_t t1, t2;
#endif

  assert(max_eq > 0);

#if TRACE
  printf("\n---> bv: reconcile model\n");
  fflush(stdout);
#endif

  neq = 0;

  /*
   * Check for conflicts between egraph and boolean assignment:
   * - two variables x and y are in the same class if both are root 
   *   variables and they have the same value in the bit assignment.
   * - i.e., the egraph model says that x != y but the 
   *   bitvector model says that x = y
   */
  init_int_hclass(&hclass, 0, solver, (iclass_hash_fun_t) bvsolver_model_hash,
		  (iclass_match_fun_t) bv_solver_var_equal_in_model);

  n = solver->vtbl.nvars;
  for (i=0; i<n; i++) {
    if (is_root_var(solver, i)) {
      x = int_hclass_get_rep(&hclass, i);
      if (x != i) {
	// x and i have the same value in the model
	// but are in different classes in the egraph
#if TRACE
	t1 = bvvar_get_eterm(&solver->vtbl, x);
	t2 = bvvar_get_eterm(&solver->vtbl, i);
	printf("---> lemma from conflict:\n");
	printf("     x1 = ");
	print_bvsolver_var(stdout, x);
	printf(", t1 = ");
	print_eterm_id(stdout, t1);
	printf("\n");
	printf("     x2 = ");
	print_bvsolver_var(stdout, i);
	printf(", t2 = ");
	print_eterm_id(stdout, t2);
	printf("\n");
#endif
	bv_solver_bvequiv_lemma(solver, x, i);
	neq ++;
	if (neq == max_eq) break;
      }
    }
  }

  delete_int_hclass(&hclass);

  return neq;
}

#endif


// TEST: NEW VERSION

/*
 * For testing: print the parent vectors of all variables in vector v
 */
static void show_parents_of_class(bv_solver_t *solver, int32_t *v) {
  uint32_t i, n;
  int32_t x;
  eterm_t t;

  n = ipv_size(v);
  assert(n >= 2);
  for (i=0; i<n; i++) {
    x = v[i];
    t = bvvar_get_eterm(&solver->vtbl, x);
    printf("--- root bvvar = ");
    print_bvsolver_var(stdout, x);
    printf("---\n");
    print_class_of_term(stdout, solver->egraph, t);
    print_parents_of_term(stdout, solver->egraph, t);
  }
}

/*
 * Heuristic: search for the best interface equality in a class
 * - v = vector 
 */
static bool interface_eq_in_class(bv_solver_t *solver, int32_t *v) {
  assert(ipv_size(v) >= 2);
  bv_solver_bvequiv_lemma(solver, v[0], v[1]);
  return true;
}

/*
 * Search for inconsistencies between the egraph and the bitvector model
 * - An inconsistency is a pair of bit-vector variables x and y
 *   such that x and y have the same value in the solver but 
 *   term_of(x) and term_of(y) are in different classes in the egraph.
 * - To resolve inconsistencies we add the lemma 
 *     (bveq x y) <=> (eq term_of(x) term_of(y))
 * - max_eq = bound on the number of lemma instances
 * - Return the number of instances created
 */
uint32_t bv_solver_reconcile_model(bv_solver_t *solver, uint32_t max_eq) {
  ipart_t partition;
  uint32_t i, n;
  uint32_t neq;

  assert(max_eq > 0);

#if TRACE
  printf("\n---> bv: reconcile model\n");
  fflush(stdout);
#endif


  /*
   * Build partitions:
   * - two variables x and y are in the same class if both are root 
   *   variables and they have the same value in the bit assignment.
   * - i.e., the egraph model says that x != y but the 
   *   bitvector model says that x = y
   */
  init_int_partition(&partition, 0, solver, (ipart_hash_fun_t) bvsolver_model_hash,
		     (ipart_match_fun_t) bv_solver_var_equal_in_model);

  n = solver->vtbl.nvars;
  for (i=0; i<n; i++) {
    if (is_root_var(solver, i)) {
      int_partition_add(&partition, i);
    }
  }

  n = int_partition_nclasses(&partition);
  for (i=0; i<n; i++) {
    printf("Class %"PRIu32"\n", i);
    show_parents_of_class(solver, partition.classes[i]);
    printf("\n");
  }


  /*
   * Process the classes: generate the 'best' conflict pairs 
   * in each class?
   */
  neq = 0;
  for (i=0; i<n; i++) {
    if (interface_eq_in_class(solver, partition.classes[i])) {
      neq ++;
      if (neq == max_eq) break;
    }
  }


  delete_int_partition(&partition);

  return neq;
}






/************************
 *  MODEL CONSTRUCTION  *
 ***********************/

/*
 * When model construction is invoked, the context has determined that
 * the constraints are SAT (so a model does exist). The value of a
 * bitvector variables x is defined by the boolean values of the
 * literal array mapped to x during bit-blasting. In some cases, 
 * this array is incomplete and does not define x's value fully.
 * For example, variables that are not reachable from the top-level atoms
 * are not marked or bitblasted.
 *
 * To complete the model, we can assign a value to the missing bits,
 * based on the variable definitions. This is done by the following functions.
 */
static void bv_solver_value_for_variable(bv_solver_t *solver, thvar_t x);


#ifndef NDEBUG

/*
 * For debugging: check whether x is fully undefined  (all literals for x are nil)
 */
static bool bv_solver_variable_all_undef(bv_solver_t *solver, thvar_t x) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  literal_t l, l0;
  uint32_t i, n;
  
  vtbl = &solver->vtbl;
  rmap = solver->remap;

  assert(valid_bvvar(vtbl, x) && rmap != NULL);

  n = bvvar_bitsize(vtbl, x);
  if (n <= 1) {
    l0 = vtbl->map[x].lit;
    assert(l0 != null_literal);
    l = remap_table_find(rmap, l0);
    return l == null_literal;

  } else {

    for (i=0; i<n; i++) {
      l0 = vtbl->map[x].array[i];
      assert(l0 != null_literal);
      l = remap_table_find(rmap, l0);
      if (l != null_literal) {
	return false;
      }
    }

    return true;    
  }
}

#endif


/*
 * Return the value of b: either VAL_TRUE or VAL_FALSE
 */
static bval_t bv_solver_value_for_bit(bv_solver_t *solver, bit_t b) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  literal_t l, l0;
  bval_t v1, v2;
  thvar_t x;

  vtbl = &solver->vtbl;
  rmap = solver->remap;

  assert(valid_bit(vtbl, b) && rmap != NULL);

  x = var_of_bit(b);
  l0 = vtbl->map[x].lit;
  l = remap_table_find(rmap, l0);
  if (l == null_literal) {
    // no value assigned to x yet
    assert(! bvvar_is_marked(vtbl, x));

    switch (bvvar_tag(vtbl, x)) {
    case BVTAG_SELECT:
      // x is (select i y): compute value for y. This will assign a value to l0
      bv_solver_value_for_variable(solver, vtbl->def[x].sel.var);
      l = remap_table_find(rmap, l0);      
      assert(l != null_literal);
      break;

    case BVTAG_OR:
      v1 = bv_solver_value_for_bit(solver, vtbl->def[x].bop[0]);
      v2 = bv_solver_value_for_bit(solver, vtbl->def[x].bop[1]);
      assert(v1 != VAL_UNDEF && v2 != VAL_UNDEF);
      l = false_literal;
      if (v1 == VAL_TRUE || v2 == VAL_TRUE) {
	l = true_literal;
      }
      remap_table_assign(rmap, l0, l);
      break;

    case BVTAG_XOR:
      v1 = bv_solver_value_for_bit(solver, vtbl->def[x].bop[0]);
      v2 = bv_solver_value_for_bit(solver, vtbl->def[x].bop[1]);
      assert(v1 != VAL_UNDEF && v2 != VAL_UNDEF);
      l = false_literal;
      if ((v1 == VAL_TRUE && v2 == VAL_FALSE) || (v1 == VAL_FALSE && v2 == VAL_TRUE)) {
	l = true_literal;
      }
      remap_table_assign(rmap, l0, l);
      break;

    default:
      assert(false);
      abort();
      break;
    }

    bvvar_set_mark(vtbl, x);    
  }

  // flip literal polarity if b is not(x)
  l ^= sign_of_bit(b);

  return literal_value(solver->core, l);
}



/*
 * Copy the value of y as value of x
 * - x and y must be variables of the same size
 * - x must be all undefined, y must be fully defined
 */
static void bv_solver_copy_value(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  uint32_t i, n;
  literal_t l0, l1, l;

  vtbl = &solver->vtbl;
  rmap = solver->remap;

  assert(valid_bvvar(vtbl, x) && valid_bvvar(vtbl, y) && bvvar_bitsize(vtbl, x) == bvvar_bitsize(vtbl, y));

  n = bvvar_bitsize(vtbl, x);
  if (n <= 1) {
    l0 = vtbl->map[x].lit;
    l1 = vtbl->map[y].lit;
    assert(l0 != null_literal && l1 != null_literal &&
	   remap_table_find(rmap, l0) == null_literal);
    l = remap_table_find(rmap, l1);
    assert(l != null_literal);
    remap_table_assign(rmap, l0, l);

  } else {
    for (i=0; i<n; i++) {
      l0 = vtbl->map[x].array[i];
      l1 = vtbl->map[y].array[i];
      assert(l0 != null_literal && l1 != null_literal && 
	     remap_table_find(rmap, l0) == null_literal);
      l = remap_table_find(rmap, l1);
      assert(l != null_literal);
      remap_table_assign(rmap, l0, l);
    }
  }
}


/*
 * Copy the value of x into word array b
 * - b must be large enough
 * - x must be fully defined
 */
static void bv_solver_extract_value(bv_solver_t *solver, thvar_t x, uint32_t *b) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  literal_t *a;
  literal_t aux;
  uint32_t i, n;
  literal_t l0, l;

  vtbl = &solver->vtbl;
  rmap = solver->remap;

  n = bvvar_bitsize(vtbl, x);
  if (n <= 1) {
    aux = vtbl->map[x].lit;
    a = &aux;
  } else {
    a = vtbl->map[x].array;
    assert(a != NULL);
  }

  for (i=0; i<n; i++) {
    l0 = a[i];
    l = remap_table_find(rmap, l0);
    assert(l != null_literal);
    if (literal_value(solver->core, l) == VAL_FALSE) {
      bvconst_clr_bit(b, i); 
    } else {
      assert(literal_value(solver->core, l) == VAL_TRUE);
      bvconst_set_bit(b, i);
    }
  }

  bvconst_normalize(b, n);
}


/*
 * Assign of word array b to x
 * - x must be fully undefined
 */
static void bv_solver_set_value(bv_solver_t *solver, thvar_t x, uint32_t *b) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  literal_t *a;
  literal_t aux;
  uint32_t i, n;
  literal_t l0;

  vtbl = &solver->vtbl;
  rmap = solver->remap;

  n = bvvar_bitsize(vtbl, x);
  if (n <= 1) {
    aux = vtbl->map[x].lit;
    a = &aux;
  } else {
    a = vtbl->map[x].array;
    assert(a != NULL);
  }

  for (i=0; i<n; i++) {
    l0 = a[i];
    assert(remap_table_find(rmap, l0) == null_literal);
    if (bvconst_tst_bit(b, i)) {
      remap_table_assign(rmap, l0, true_literal);
    } else {
      remap_table_assign(rmap, l0, false_literal);
    }
  }
  
}



/*
 * Assign the opposite of value of y to x
 * - x and y must have the same size
 * - x must be fully undefined
 * - y must be fully defined
 */
static void bv_solver_negate_value(bv_solver_t *solver, thvar_t x, thvar_t y) {
  bv_vartable_t *vtbl;
  uint32_t n, w;
  uint32_t a[4];
  uint32_t *b;

  vtbl = &solver->vtbl;
  assert(valid_bvvar(vtbl, x) && valid_bvvar(vtbl, y) && bvvar_bitsize(vtbl, x) == bvvar_bitsize(vtbl, y));

  n = bvvar_bitsize(vtbl, x);
  assert(n > 0);
  w = (n + 31) >> 5;
  b = a;
  if (w > 4) {
    b = (uint32_t *) safe_malloc(w * sizeof(uint32_t));
  }

  bv_solver_extract_value(solver, y, b); // b := value of y
  bvconst_negate(b, w);  // b := - b
  bv_solver_set_value(solver, x, b); // value of x := b

  if (w > 4) {
    safe_free(b);
  }
}


/*
 * Convert bv's value (as a non-negative integer) into a shift amount. 
 * If bv's value is larger than n, then returns n
 */
static uint32_t get_shift_amount(uint32_t n, uint32_t *bv) {
  uint32_t k, i, s;

  k = (n + 31) >> 5; // number of words in bv
  s = bvconst_get32(bv); // low-order word = shift amount

  // if any of the higher order words in nonzero, return n
  for (i=1; i<k; i++) {
    if (bv[i] != 0) return n;
  }

  // truncate s if required
  return (n <= s) ? n : s;
}


/*
 * Apply op to val[y], val[z] and store the result as val[x]
 * - x, y, z must all have the same size
 * - x must be fully undefined
 * - y and z must be fully defined
 */
static void bv_solver_binop_value(bv_solver_t *solver, bvvar_tag_t op, thvar_t x, thvar_t y, thvar_t z) {
  bv_vartable_t *vtbl;
  uint32_t n, w, k;
  uint32_t a1[4], a2[4], a3[4];
  uint32_t *b1, *b2, *b3;

  vtbl = &solver->vtbl;
  n = bvvar_bitsize(vtbl, x);
  assert(n > 0);
  w = (n + 31) >> 5;
  b1 = a1;
  b2 = a2;
  b3 = a3;
  if (w > 4) {
    b1 = (uint32_t *) safe_malloc(w * sizeof(uint32_t));
    b2 = (uint32_t *) safe_malloc(w * sizeof(uint32_t));
    b3 = NULL; // need this so that safe_free(b3) works
  }

  bv_solver_extract_value(solver, y, b1); // b1 := value of y
  bv_solver_extract_value(solver, z, b2); // b2 := value of z

  switch (op) {
  case BVTAG_ADD:
    bvconst_add(b1, w, b2); // b1 := b1 + b2
    bv_solver_set_value(solver, x, b1);
    break;

  case BVTAG_SUB:
    bvconst_sub(b1, w, b2); // b1 := b1 - b2
    bv_solver_set_value(solver, x, b1);
    break;

  case BVTAG_MUL:
    bvconst_mul(b1, w, b2); // b1 := b1 * b2
    bv_solver_set_value(solver, x, b1);
    break;

  case BVTAG_UDIV:
    if (w > 4) {
      b3 = (uint32_t *) safe_malloc(w * sizeof(uint32_t));
    }
    bvconst_udiv2z(b3, n, b1, b2);
    bv_solver_set_value(solver, x, b3);
    break;

  case BVTAG_UREM:
    if (w > 4) {
      b3 = (uint32_t *) safe_malloc(w * sizeof(uint32_t));
    }
    bvconst_urem2z(b3, n, b1, b2);
    bv_solver_set_value(solver, x, b3);
    break;

  case BVTAG_SDIV:
    if (w > 4) {
      b3 = (uint32_t *) safe_malloc(w * sizeof(uint32_t));
    }
    bvconst_sdiv2z(b3, n, b1, b2);
    bv_solver_set_value(solver, x, b3);
    break;

  case BVTAG_SREM:
    if (w > 4) {
      b3 = (uint32_t *) safe_malloc(w * sizeof(uint32_t));
    }
    bvconst_srem2z(b3, n, b1, b2);
    bv_solver_set_value(solver, x, b3);
    break;

  case BVTAG_SMOD:
    if (w > 4) {
      b3 = (uint32_t *) safe_malloc(w * sizeof(uint32_t));
    }
    bvconst_smod2z(b3, n, b1, b2);
    bv_solver_set_value(solver, x, b3);
    break;

  case BVTAG_SHL:
    k = get_shift_amount(n, b2);
    bvconst_shift_left(b1, n, k, 0);  // b1 := (b1 << k) padded with 0
    bv_solver_set_value(solver, x, b1);
    break;
      
  case BVTAG_LSHR:
    k = get_shift_amount(n, b2);
    bvconst_shift_right(b1, n, k, 0); // b1 := (b1 >> k) padded with 0
    bv_solver_set_value(solver, x, b1);
    break;

  case BVTAG_ASHR:
    k = get_shift_amount(n, b2);
    bvconst_shift_right(b1, n, k, bvconst_tst_bit(b1, n-1)); // padding with sign bit
    bv_solver_set_value(solver, x, b1);
    break;
      
  default:
    assert(false);
    break;
  }

  if (w > 4) {
    safe_free(b1);
    safe_free(b2);
    safe_free(b3);
  }
}








/*
 * Assign a value to all the literals of x
 */
static void bv_solver_value_for_variable(bv_solver_t *solver, thvar_t x) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  literal_t *a;
  literal_t aux;
  bvvar_tag_t op;
  uint32_t i, n;
  literal_t l0, l;
  thvar_t y;

  vtbl = &solver->vtbl;

  assert(valid_bvvar(vtbl, x) && bvvar_bitsize(vtbl, x) > 0);

  /*
   * All marked variables have been bit-blasted so they are fully
   * defined by the SAT solver.
   */
  if (! bvvar_is_marked(vtbl, x)) {

    // a --> array of pseudo literals mapped to x
    // n = number of bits in x = size of array a
    n = bvvar_bitsize(vtbl, x);
    if (n == 1) {
      aux = vtbl->map[x].lit;
      a = &aux;
    } else {
      a = vtbl->map[x].array;
      assert(a != NULL);
    }

    rmap = solver->remap;
    op = bvvar_tag(vtbl, x);

    switch (op) {
    case BVTAG_SMALL_CONST:
    case BVTAG_BIG_CONST:
      // nothing to do. The pseudo-literals are mapped to true or false
      // already.
      break;

    case BVTAG_VAR:      
      // we can assign an arbitrary value to the undefined bits of x
      for (i=0; i<n; i++) {
	l0 = a[i];
	assert(l0 != null_literal);
	l = remap_table_find(rmap, l0);
	if (l == null_literal) {
	  remap_table_assign(rmap, l0, false_literal);
	}
      }
      break;

    case BVTAG_BIT:
      l0 = a[0];
      assert(l0 != null_literal);
      l = remap_table_find(rmap, l0);
      if (l == null_literal) {
	(void) bv_solver_value_for_bit(solver, vtbl->def[x].bval);
       	assert(remap_table_find(rmap, l0) != null_literal);
      }
      break;

    case BVTAG_BIT_ARRAY:
      for (i=0; i<n; i++) {
	l0 = a[i];
	assert(l0 != null_literal);
	l = remap_table_find(rmap, l0);
	if (l == null_literal) {
	  (void) bv_solver_value_for_bit(solver, vtbl->def[x].bit[i]);
	  assert(remap_table_find(rmap, l0) != null_literal);
	}
      }
      break;

    case BVTAG_NEG:
      // x must be fully undefined otherwise something went
      // wrong in the translation.
      assert(bv_solver_variable_all_undef(solver, x));
      y = vtbl->def[x].op[0];
      bv_solver_value_for_variable(solver, y);
      bv_solver_negate_value(solver, x, y);
      break;

    case BVTAG_ADD:
    case BVTAG_SUB:
    case BVTAG_MUL:
    case BVTAG_SHL:
    case BVTAG_UDIV:
    case BVTAG_UREM:
    case BVTAG_SDIV:
    case BVTAG_SREM:
    case BVTAG_SMOD:
    case BVTAG_LSHR:
    case BVTAG_ASHR:
      assert(bv_solver_variable_all_undef(solver, x));
      bv_solver_value_for_variable(solver, vtbl->def[x].op[0]);
      bv_solver_value_for_variable(solver, vtbl->def[x].op[1]);
      bv_solver_binop_value(solver, op, x, vtbl->def[x].op[0], vtbl->def[x].op[1]);
      break;

    case BVTAG_ITE:
      assert(bv_solver_variable_all_undef(solver, x));
      l = vtbl->def[x].ite->cond;
      if (literal_value(solver->core, l) == VAL_TRUE) {
	y = vtbl->def[x].ite->left;
      } else {
	assert(literal_value(solver->core, l) == VAL_FALSE);
	y = vtbl->def[x].ite->right;
      }
      // assign a value to y then assign the same value to x
      bv_solver_value_for_variable(solver, y);
      bv_solver_copy_value(solver, x, y);
      break;

    default:
      assert(false);
      abort();
      break;
    }

    bvvar_set_mark(vtbl, x);
  }  
}





/*
 * Interface function: nothing to do
 */
void bv_solver_build_model(bv_solver_t *solver) {
  // do nothing
}



/*
 * Copy the value assigned to x in the model into buffer c
 * - return true if the value is available
 * - return false if the solver has no model
 */
bool bv_solver_value_in_model(bv_solver_t *solver, thvar_t x, bvconstant_t *c) {
  bv_vartable_t *vtbl;
  remap_table_t *rmap;
  uint32_t i, n;
  literal_t l0, l;
  literal_t *a;

  vtbl = &solver->vtbl;
  n = bvvar_bitsize(vtbl, x);
  assert(n > 0);

  if (solver->bit_blasted) {
    rmap = solver->remap;
    bvconstant_set_bitsize(c, n);

    if (! bvvar_is_marked(vtbl, x)) {
      bv_solver_value_for_variable(solver, x);
    }

    if (n == 1) {

      l0 = vtbl->map[x].lit;
      assert(l0 != null_literal);
      l = remap_table_find(rmap, l0);
      if (l == null_literal) {
	// NOTE: this should not happen if bv_solver_value_for_variable
	// works properly
	goto not_defined;
      } else {
	switch (literal_value(solver->core, l)) {
	case VAL_FALSE:
	  bvconst_clr_bit(c->data, 0);
	  break;
	case VAL_TRUE:
	  bvconst_set_bit(c->data, 0);
	  break;
	case VAL_UNDEF:
	default:
	  goto not_defined;
	}
      }

    } else {

      a = vtbl->map[x].array;
      for (i=0; i<n; i++) {
	l0 = a[i];
	assert(l0 != null_literal);
	l = remap_table_find(rmap, l0);
	if (l == null_literal) {
	  // NOTE: this should not happen if bv_solver_value_for_variable
	  // works properly
	  goto not_defined;
	} else {
	  switch (literal_value(solver->core, l)) {
	  case VAL_FALSE:
	    bvconst_clr_bit(c->data, i);
	    break;
	  case VAL_TRUE:
	    bvconst_set_bit(c->data, i);
	    break;
	  case VAL_UNDEF:
	  default:
	    goto not_defined;
	  }
	}
      }
    }

    bvconst_normalize(c->data, n);

    return true;
  }


 not_defined:
  return false;
}


/*
 * Delete whatever is used to store the model
 */
void bv_solver_free_model(bv_solver_t *solver) {
  // do nothing
}


/*
 * Allocate a small set and add all the used values of size set->bitsize
 * to that set. Store the result into set->ptr.
 */
static void collect_used_values_small(bv_solver_t *solver, bvset_t *set) {    
  small_bvset_t *s;
  bv_vartable_t *vtbl;
  bvconstant_t aux;
  uint32_t i, n;
  uint32_t bitsize;  

  bitsize = set->bitsize;
  s = new_small_bvset(bitsize);
  set->ptr = s;

  init_bvconstant(&aux);

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (bvvar_bitsize(vtbl, i) == bitsize && 
	bv_solver_value_in_model(solver, i, &aux)) {
      // aux = value of i in the model
      // it's stored in aux.data[0]
      small_bvset_add(s, aux.data[0]);
    }
  }

  delete_bvconstant(&aux);
}



/*
 * Allocate a red-black tree and add all the used values of size set->bitsize 
 * to that tree. Store the tree into set->ptr;
 */
static void collect_used_values_rb(bv_solver_t *solver, bvset_t *set) {
  rb_bvset_t *s;
  bv_vartable_t *vtbl;
  bvconstant_t aux;
  uint32_t i, n;
  uint32_t bitsize;  

  bitsize = set->bitsize;
  s = new_rb_bvset(bitsize);
  set->ptr = s;

  init_bvconstant(&aux);

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (bvvar_bitsize(vtbl, i) == bitsize && 
	bv_solver_value_in_model(solver, i, &aux)) {
      // aux = value of i in the model
      // copy the low-order word aux.data[0] into s
      rb_bvset_add(s, aux.data[0]);
    }
  }

  delete_bvconstant(&aux);
}


/*
 * Create a fresh value: distinct from all the other bitvector constants
 * of the same size present in the model.
 * - n = bit size of the new value
 * - v = buffer where the result must be copied
 * - return false if that fails, true otherwise
 */
bool bv_solver_fresh_value(bv_solver_t *solver, bvconstant_t *v, uint32_t n) {
  uint32_t x;
  bvset_t *set;

  set = used_vals_get_set(&solver->used_vals, n);
  if (n <= SMALL_BVSET_LIMIT) {
    if (set->ptr == NULL) {
      collect_used_values_small(solver, set);
    }

    if (small_bvset_full(set->ptr)) {
      // can't create a new value.
      // this should not happen if the solvers are sound.
      // the egraph should not request a fresh value in this case.
      assert(false);
      return false;
    }

    x = small_bvset_get_fresh(set->ptr);
  } else {
    if (set->ptr == NULL) {
      collect_used_values_rb(solver, set);
    }

    if (rb_bvset_full(set->ptr)) {
      assert(false);
      return false;
    }

    x = rb_bvset_get_fresh(set->ptr);
  }

  // copy x into *v
  // padd the rest with 0s
  assert(n >= 32 || (x < (1<<n)));
  bvconstant_set_all_zero(v, n); // v is 0b0.....0
  v->data[0] = x;                // copy x in low-order bits

  return true;
}


/***************************
 *  INTERFACE DESCRIPTORS  *
 **************************/

/*
 * Internalization interface for the context
 */
static bvsolver_interface_t bv_interface = {
  (create_bvvar_fun_t) bv_solver_create_var,
  (create_bvconst_fun_t) bv_solver_create_const,
  (create_bvpoly_fun_t) bv_solver_create_bvpoly,
  (create_bvlogic_fun_t) bv_solver_create_bvlogic,
  (create_bvop_fun_t) bv_solver_create_bvop,
  (create_bvite_fun_t) bv_solver_create_ite,
  (attach_eterm_fun_t) bv_solver_attach_eterm,
  (eterm_of_var_fun_t) bv_solver_eterm_of_var,

  (create_bvatom_fun_t) bv_solver_create_eq_atom,
  (create_bvatom_fun_t) bv_solver_create_ge_atom,
  (create_bvatom_fun_t) bv_solver_create_sge_atom,

  (assert_bvaxiom_fun_t) bv_solver_assert_eq_axiom,
  (assert_bvaxiom_fun_t) bv_solver_assert_ge_axiom,
  (assert_bvaxiom_fun_t) bv_solver_assert_sge_axiom,

  (build_model_fun_t) bv_solver_build_model,
  (free_model_fun_t) bv_solver_free_model,
  (bv_val_in_model_fun_t) bv_solver_value_in_model,
};


/*
 * Control interface for core and egraph
 */
static th_ctrl_interface_t bv_control = {
  (start_intern_fun_t) bv_solver_start_internalization,
  (start_fun_t) bv_solver_start_search,
  (propagate_fun_t) bv_solver_propagate,
  (final_check_fun_t ) bv_solver_final_check,
  (increase_level_fun_t) bv_solver_increase_decision_level,
  (backtrack_fun_t) bv_solver_backtrack,
  (push_fun_t) bv_solver_push,
  (pop_fun_t) bv_solver_pop,
  (reset_fun_t) bv_solver_reset,
};


static th_smt_interface_t bv_smt = {
  (assert_fun_t) bv_solver_assert_atom,
  NULL, // expand explanation
  (select_pol_fun_t) bv_solver_select_polarity,
  NULL, // atom deletion 
  NULL, // end atom deletion
};



/*
 * Satellite solver interface for the egraph
 */
static th_egraph_interface_t bv_egraph = {
  (assert_eq_fun_t) bv_solver_assert_var_eq,
  (assert_diseq_fun_t) bv_solver_assert_var_diseq,
  (assert_distinct_fun_t) bv_solver_assert_var_distinct,
  (check_diseq_fun_t) bv_solver_check_disequality,
  NULL,  // expand_th_explanation
  (reconcile_model_fun_t) bv_solver_reconcile_model,
  (attach_to_var_fun_t) bv_solver_attach_eterm,
  (get_eterm_fun_t) bv_solver_eterm_of_var,
};


/*
 * Theory-specific interface for the egraph
 */
static bv_egraph_interface_t bv_bv_egraph = {
  (make_bv_var_fun_t) bv_solver_create_on_the_fly_var,
  (bv_val_fun_t) bv_solver_value_in_model,
  (bv_fresh_val_fun_t) bv_solver_fresh_value,
};


/*
 * Get the solver's interface descriptors
 */
bvsolver_interface_t *bv_solver_bv_interface(bv_solver_t *solver) {
  return &bv_interface;
}

th_ctrl_interface_t *bv_solver_ctrl_interface(bv_solver_t *solver) {
  return &bv_control;
}

th_smt_interface_t *bv_solver_smt_interface(bv_solver_t *solver) {
  return &bv_smt;
}

th_egraph_interface_t *bv_solver_egraph_interface(bv_solver_t *solver) {
  return &bv_egraph;
}

bv_egraph_interface_t *bv_solver_bv_egraph_interface(bv_solver_t *solver) {
  return &bv_bv_egraph;
}




/*************************
 *  DEBUGGING AND TRACE  *
 ************************/

#if DUMP

/*
 * Dump the solver content into a file
 */
static void bv_solver_dump_state(bv_solver_t *solver, char *filename) {
  FILE *f;

  f = fopen(filename, "w");
  if (f != NULL) {
    fprintf(f, "\n==== BVSOLVER PARTITION ====\n");
    print_bvsolver_partition(f, solver);
    fprintf(f, "\n==== BVSOLVER TERMS ====\n");
    print_bvsolver_bitmaps(f, solver);
    fprintf(f, "\n==== BVSOLVER ATOMS ====\n");
    print_bvsolver_atoms(f, solver);
    fprintf(f, "\n==== CLAUSES ====\n");
    print_clauses(f, solver->core);
    fprintf(f, "\n==== LEMMAS ====\n");
    print_lemmas(f, solver->core);
    fprintf(f, "\n==== BIT ASSIGNEMNT ====\n");
    print_boolean_assignment(f, solver->core);
    fprintf(f, "\n");
    fclose(f);
  }
}

#endif
