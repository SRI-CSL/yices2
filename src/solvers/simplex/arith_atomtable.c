/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TABLE OF ATOMS FOR ARITHMETIC SOLVERS
 */

/*
 * The atoms can be of the form (x >= k) or (x <= k) or (x == k),
 * where x is a variable in the arithmetic solver and k is a rational
 * constant. Each atom is identified by an index in the table.
 * The table uses hash consing and it supports removal of atoms for push/pop
 * operations.
 *
 * The components of an atom are:
 * - a 2bit tag to specify the atom type (>=, <=, or ==)
 * - the variable x (30bits index)
 * - the rational constant k
 * - a boolean variable (mapped to the atom in the smt-core)
 */

#include "utils/memalloc.h"
#include "solvers/simplex/arith_atomtable.h"


/*
 * Hash code for an atom, based on Jenkins's lookup3.c code
 * - header = tag + variable index
 * - bound = constant
 */
#define rot(x,k) (((x)<<(k)) | ((x)>>(32-(k))))

#define final(a,b,c)      \
{                         \
  c ^= b; c -= rot(b,14); \
  a ^= c; a -= rot(c,11); \
  b ^= a; b -= rot(a,25); \
  c ^= b; c -= rot(b,16); \
  a ^= c; a -= rot(c,4);  \
  b ^= a; b -= rot(a,14); \
  c ^= b; c -= rot(b,24); \
}

static uint32_t hash_arith_atom(uint32_t header, rational_t *bound) {
  uint32_t a, b, c;

  q_hash_decompose(bound, &a, &b);
  c = header + 0xdeadbeef;
  final(a, b, c);
  return c;
}


/*
 * Initialize: use default sizes
 */
void init_arith_atomtable(arith_atomtable_t *table, smt_core_t *core) {
  uint32_t n;

  n = DEF_ARITHATOMTABLE_SIZE;
  assert(n < MAX_ARITHATOMTABLE_SIZE);

  table->size = n;
  table->natoms = 0;
  table->atoms = (arith_atom_t *) safe_malloc(n * sizeof(arith_atom_t));
  table->mark = allocate_bitvector(n);

  table->core = core;
  init_int_htbl(&table->htbl, 0);
  q_init(&table->aux);
}


/*
 * Make the table 50% larger
 */
static void extend_arith_atomtable(arith_atomtable_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;
  if (n >= MAX_ARITHATOMTABLE_SIZE) {
    out_of_memory();
  }
  assert(n > table->size);

  table->size = n;
  table->atoms = (arith_atom_t *) safe_realloc(table->atoms, n * sizeof(arith_atom_t));
  table->mark = extend_bitvector(table->mark, n);
}



/*
 * Create a new atom and attach it to a new boolean variable
 * - header = atom header (var + tag)
 * - bound = rational constant
 */
static int32_t new_arith_atom(arith_atomtable_t *table, uint32_t header, rational_t *bound) {
  int32_t i;
  bvar_t x;

  i = table->natoms;
  if (i == table->size) {
    extend_arith_atomtable(table);
  }
  assert(i < table->size);

  // new boolean variable
  x = create_boolean_variable(table->core);
  attach_atom_to_bvar(table->core, x, arithatom_idx2tagged_ptr(i));

  // initialize the atom descriptor
  table->atoms[i].header = header;
  table->atoms[i].boolvar = x;
  q_init(&table->atoms[i].bound);
  q_set(&table->atoms[i].bound, bound);

  // new atom is not assigned
  clr_bit(table->mark, i);

  table->natoms ++;

  return i;
}



/*
 * Reset the table:
 * - free all rationals
 * - reset the hash table
 */
void reset_arith_atomtable(arith_atomtable_t *table) {
  uint32_t i, n;

  n = table->natoms;
  for (i=0; i<n; i++) {
    q_clear(&table->atoms[i].bound);
  }

  table->natoms = 0;
  reset_int_htbl(&table->htbl);
  q_clear(&table->aux);
}


/*
 * Delete the table
 */
void delete_arith_atomtable(arith_atomtable_t *table) {
  uint32_t i, n;

  n = table->natoms;
  for (i=0; i<n; i++) {
    q_clear(&table->atoms[i].bound);
  }

  safe_free(table->atoms);
  delete_bitvector(table->mark);

  table->atoms = NULL;
  table->mark = NULL;

  delete_int_htbl(&table->htbl);
  q_clear(&table->aux);
}



/*
 * Remove all atoms of index >= natoms
 */
void arith_atomtable_remove_atoms(arith_atomtable_t *table, uint32_t natoms) {
  uint32_t i, n, k;
  arith_atom_t *a;

  assert(natoms <= table->natoms);

  a = table->atoms;
  n = table->natoms;
  for (i=natoms; i<n; i++) {
    // remove i from the hash table
    k = hash_arith_atom(a[i].header, &a[i].bound);
    int_htbl_erase_record(&table->htbl, k, i);

    // free the rational constant
    q_clear(&a[i].bound);
  }

  table->natoms = natoms;
}


/*
 * Get atom index for boolean var v
 * - return -1 if there's no atom for v or the atom is not arithmetic
 */
int32_t arith_atom_id_for_bvar(arith_atomtable_t *table, bvar_t v) {
  void *a;
  int32_t id;

  a = bvar_atom(table->core, v);
  if (a != NULL && atom_tag(a) == ARITH_ATM_TAG) {
    id = arithatom_tagged_ptr2idx(a);
    assert(boolvar_of_atom(arith_atom(table, id)) == v);
    return id;
  } else {
    return -1;
  }
}


/*
 * Get atom descriptor for boolean variable v
 * - return NULL if there's no atom for v or the atom is not arithmetic
 */
arith_atom_t *arith_atom_for_bvar(arith_atomtable_t *table, bvar_t v) {
  void *a;
  int32_t id;

  a = bvar_atom(table->core, v);
  if (a != NULL && atom_tag(a) == ARITH_ATM_TAG) {
    id = arithatom_tagged_ptr2idx(a);
    assert(boolvar_of_atom(arith_atom(table, id)) == v);
    return arith_atom(table, id);
  } else {
    return NULL;
  }
}



/*
 * ATOM CONSTRUCTION
 */

/*
 * Hobject for interfacing with int_hash_table
 */
typedef struct arith_atom_hobj_s {
  int_hobj_t m;
  arith_atomtable_t *table;
  rational_t *bound;
  uint32_t header; // encodes var + tag
} arith_atom_hobj_t;


/*
 * Methods for int_hobj_t
 */
static uint32_t hash_arith_atm_hobj(arith_atom_hobj_t *o) {
  return hash_arith_atom(o->header, o->bound);
}

static bool eq_arith_atm_hobj(arith_atom_hobj_t *o, int32_t i) {
  arith_atomtable_t *table;

  table = o->table;
  assert(0 <= i && i < table->natoms);
  return o->header == table->atoms[i].header && q_eq(o->bound, &table->atoms[i].bound);
}

static int32_t build_arith_atm_hobj(arith_atom_hobj_t *o) {
  return new_arith_atom(o->table, o->header, o->bound);
}


/*
 * Global hash-consing object
 */
static arith_atom_hobj_t arith_atom_hobj = {
  { (hobj_hash_t) hash_arith_atm_hobj, (hobj_eq_t) eq_arith_atm_hobj, (hobj_build_t) build_arith_atm_hobj },
  NULL,
  NULL,
  0,
};



/*
 * EXPORTED FUNCTIONS
 */

/*
 * Search for an atom (x op k) where op is one of GE_ATM, LE_ATM, EQ_ATM
 * - return -1 if there's no such atom, otherwise, return the atom index
 */
int32_t find_arith_atom(arith_atomtable_t *table, thvar_t x, arithatm_tag_t op, rational_t *k) {
  arith_atom_hobj.table = table;
  arith_atom_hobj.header = arithatom_mk_header(x, op);
  arith_atom_hobj.bound = k;

  // int_htbl_find_obj returns -1 (NULL_VALUE) if the object is not found
  return int_htbl_find_obj(&table->htbl, (int_hobj_t *) &arith_atom_hobj);
}


/*
 * Search for the atom (x op k).  Create it if it's not already in the table.
 */
int32_t get_arith_atom(arith_atomtable_t *table, thvar_t x, arithatm_tag_t op, rational_t *k, bool *new_atom) {
  uint32_t n;
  int32_t i;

  arith_atom_hobj.table = table;
  arith_atom_hobj.header = arithatom_mk_header(x, op);
  arith_atom_hobj.bound = k;

  n = table->natoms;
  i = int_htbl_get_obj(&table->htbl, (int_hobj_t *) &arith_atom_hobj);
  *new_atom = table->natoms > n;

  return i;
}



/*
 * Variants: return a literal, create a new atom if needed
 * - for ge_atom/le_atom, is_int indicates whether x is an integer variable:
 *   if x is an integer, then k must also be an integer constant,
 *   and we use the equivalence
 *      (x <= k) <==> not (x >= k+1)
 *   (so all integer atoms are of type GE_ATM)
 *
 * Returned atom index in *new_idx:
 * - *new_idx = -1 if the atom was already present in the table
 * - if a new atom is created, *new_idx is set to that atom's index
 */
literal_t get_literal_for_eq_atom(arith_atomtable_t *table, thvar_t x, rational_t *k, int32_t *new_idx) {
  bool new_atom;
  int32_t i;

  i = get_arith_atom(table, x, EQ_ATM, k, &new_atom);
  if (new_atom) {
    *new_idx = i;
  } else {
    *new_idx = -1;
  }
  return pos_lit(table->atoms[i].boolvar);
}

literal_t get_literal_for_ge_atom(arith_atomtable_t *table, thvar_t x, bool is_int, rational_t *k, int32_t *new_idx) {
  bool new_atom;
  int32_t i;

  assert(! is_int || q_is_integer(k));
  i = get_arith_atom(table, x, GE_ATM, k, &new_atom);
  if (new_atom) {
    *new_idx = i;
  } else {
    *new_idx = -1;
  }
  return pos_lit(table->atoms[i].boolvar);
}

literal_t get_literal_for_le_atom(arith_atomtable_t *table, thvar_t x, bool is_int, rational_t *k, int32_t *new_idx) {
  bool new_atom;
  int32_t i;

  if (is_int) {
    assert(q_is_integer(k));

    // get atom (x >= k+1)
    q_set(&table->aux, k);
    q_add_one(&table->aux);
    i = get_arith_atom(table, x, GE_ATM, &table->aux, &new_atom);
    if (new_atom) {
      *new_idx = i;
    } else {
      *new_idx = -1;
    }
    return neg_lit(table->atoms[i].boolvar);

  } else {
    // get (x <= k)
    i = get_arith_atom(table, x, LE_ATM, k, &new_atom);
    if (new_atom) {
      *new_idx = i;
    } else {
      *new_idx = -1;
    }
    return pos_lit(table->atoms[i].boolvar);
  }
}

