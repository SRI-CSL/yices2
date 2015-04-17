/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TABLE OF ATOMS FOR THE BITVECTOR SOLVER
 */

#include "solvers/bv/bv_atomtable.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"


/*
 * Initialization
 * - use the default size
 * - the table is initially empty
 */
void init_bv_atomtable(bv_atomtable_t *table) {
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
void delete_bv_atomtable(bv_atomtable_t *table) {
  safe_free(table->data);
  table->data = NULL;

  delete_int_htbl(&table->htbl);
}


/*
 * Empty the table
 */
void reset_bv_atomtable(bv_atomtable_t *table) {
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
void bv_atomtable_remove_atoms(bv_atomtable_t *table, uint32_t na) {
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



/*
 * Main constructor
 */
int32_t get_bv_atom(bv_atomtable_t *table, bvatm_tag_t op, thvar_t x, thvar_t y) {
  bvatm_hobj.tbl = table;
  bvatm_hobj.op = op;
  bvatm_hobj.left = x;
  bvatm_hobj.right = y;
  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &bvatm_hobj);
}


/*
 * Normalize + hash consing
 */
int32_t get_bveq_atom(bv_atomtable_t *table, thvar_t x, thvar_t y) {
  thvar_t aux;

  if (x > y) {
    aux = x; x = y; y = aux;
  }
  return get_bv_atom(table, BVEQ_ATM, x, y);
}



/*
 * Search for an atom
 * - return the atom id if it exists
 * - return -1 otherwise
 */
int32_t find_bv_atom(bv_atomtable_t *table, bvatm_tag_t op, thvar_t x, thvar_t y) {
  bvatm_hobj.tbl = table;
  bvatm_hobj.op = op;
  bvatm_hobj.left = x;
  bvatm_hobj.right = y;
  return int_htbl_find_obj(&table->htbl, (int_hobj_t *) &bvatm_hobj);
}

int32_t find_bveq_atom(bv_atomtable_t *table, thvar_t x, thvar_t y) {
  thvar_t aux;

  if (x > y) {
    aux = x; x = y; y = aux;
  }
  return find_bv_atom(table, BVEQ_ATM, x, y);
}




