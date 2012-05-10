/*
 * TABLE OF BOOLEAN VARIABLES
 */

#include <assert.h>

#include "memalloc.h"
#include "hash_functions.h"
#include "int_array_sort.h"
#include "bool_vartable.h"



/*
 * ARRAY OF GATE DESCRIPTORS
 */
static void init_bgate_array(bgate_array_t *a) {
  a->data = NULL;
  a->ngates = 0;
  a->size = 0;
}

static void extend_bgate_array(bgate_array_t *a) {
  uint32_t n;

  n = a->size;
  if (n == 0) {
    n = DEF_BGATE_ARRAY_SIZE; // first allocation
    assert(n <= MAX_BGATE_ARRAY_SIZE);
    a->data = (bgate_t *) safe_malloc(n * sizeof(bgate_array_t));
    a->size = n;
  } else {
    // try to make the table 50% larger
    n += (n >> 1);
    assert(n > a->size);
    if (n > MAX_BGATE_ARRAY_SIZE) {
      out_of_memory();
    }

    a->data = (bgate_t *) safe_realloc(a->data, n * sizeof(bgate_array_t));
    a->size = n;
  }
}

static void delete_bgate_array(bgate_array_t *a) {
  safe_free(a->data);
  a->data = NULL;
}

static void reset_bgate_array(bgate_array_t *a) {
  a->ngates = 0;
}


/*
 * Copy g as a new descriptor in a
 * - return the index of the newly allocated element
 */
static uint32_t store_bgate(bgate_array_t *a, bgate_t *g) {
  uint32_t i;

  i = a->ngates;
  if (i == a->size) {
    extend_bgate_array(a);
  }
  assert(i < a->size);
  a->data[i] = *g;
  a->ngates = i+1;

  return i;
}




/*
 * DESCRIPTORS FOR OR GATES
 */
static void init_ordata_array(ordata_array_t *a) {
  a->data = NULL;
  a->top = 0;
  a->size = 0;
}

static void delete_ordata_array(ordata_array_t *a) {
  safe_free(a->data);
  a->data = NULL;
}

static void reset_ordata_array(ordata_array_t *a) {
  a->top = 0;
}


/*
 * Make the array large enough to store n integers
 */
static void ordata_array_resize(ordata_array_t *a, uint32_t n) {
  uint32_t old_size, new_size;

  old_size = a->size;
  if (n < old_size) {
    if (n > MAX_ORDATA_ARRAY_SIZE) {
      out_of_memory();
    }

    if (old_size == 0) {
      /*
       * First allocation: use max(n, default size)
       */
      new_size = DEF_ORDATA_ARRAY_SIZE;
      if (new_size < n) {
	new_size = n;
      }
      assert(new_size <= MAX_ORDATA_ARRAY_SIZE);

      a->data = (int32_t *) safe_malloc(new_size * sizeof(int32_t));
      a->size = new_size;

    } else {
      /*
       * try to increase the size by 50%
       * if that's not enough, use n
       */
      new_size = old_size;
      new_size += new_size >> 1;
      if (new_size > MAX_ORDATA_ARRAY_SIZE) {
	new_size = MAX_ORDATA_ARRAY_SIZE;
      } else if (new_size < n) {
	new_size = n;
      }
      
      assert(new_size <= MAX_ORDATA_ARRAY_SIZE && n <= new_size);
      a->data = (int32_t *) safe_realloc(a->data, new_size * sizeof(int32_t));
      a->size = new_size;
    }
  }
}


/*
 * Copy array b into a
 * - n = number of elements in b
 * - return the index k in a->data where b is copied 
 */
static uint32_t store_ordata(ordata_array_t *a, literal_t *b, uint32_t n) {
  int32_t *aux;
  uint32_t i, k;

  if (n >= MAX_ORDATA_ARRAY_SIZE) {
    out_of_memory();
  }
  ordata_array_resize(a, a->top + n + 1);

  assert(a->top + n + 1 <= a->size);

  k = a->top;
  a->data[k] = n; // store arity first

  aux = a->data + k + 1;
  for (i=0; i<n; i++) {
    aux[i] = b[i];
  }

  return k;
}



/*
 * HASH FUNCTIONS
 */
static uint32_t hash_bgate(bgate_t *g) {
  return jenkins_hash_quad(g->ttbl, g->var[0], g->var[1], g->var[2], 0xae01781a); 
}

static uint32_t hash_orgate(uint32_t n, literal_t *a) {
  return jenkins_hash_intarray2(a, n, 0xfedcba98);
}



/*
 * GLOBAL OPERATIONS ON THE TABLE
 */

/*
 * Initialize the table: this creates variable 0 = true
 */
void init_bool_vartable(bool_vartable_t *table) {
  uint32_t n;

  n = DEF_BOOLVARTABLE_SIZE;
  assert(0 < n && n <= MAX_BOOLVARTABLE_SIZE);

  table->tag = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  table->desc = (uint32_t *) safe_malloc(n * sizeof(uint32_t));

  assert(0 == const_bvar);

  table->tag[0] = BCONST;
  table->desc[0] = 0;

  table->nvars = 1;
  table->size = n;

  init_bgate_array(&table->gates);
  init_ordata_array(&table->ordata);

  init_int_htbl(&table->htbl, 0);
}


/*
 * Make the table 50% larger 
 */
static void extend_bool_vartable(bool_vartable_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;
  if (n > MAX_BOOLVARTABLE_SIZE) {
    out_of_memory();
  }

  table->tag = (uint8_t *) safe_realloc(table->tag, n * sizeof(uint8_t));
  table->desc = (uint32_t *) safe_realloc(table->desc, n * sizeof(uint32_t));
  table->size = n;
}


/*
 * Free memory
 */
void delete_bool_vartable(bool_vartable_t *table) {
  safe_free(table->tag);
  safe_free(table->desc);
  table->tag = NULL;
  table->desc = NULL;
  delete_bgate_array(&table->gates);
  delete_ordata_array(&table->ordata);
  delete_int_htbl(&table->htbl);
}


/*
 * Reset: empty the table. All variables and descriptors are 
 * removed except variable 0.
 */
void reset_bool_vartable(bool_vartable_t *table) {
  table->nvars = 1;
  reset_bgate_array(&table->gates);
  reset_ordata_array(&table->ordata);
  reset_int_htbl(&table->htbl);
}


/*
 * Allocate a new variable index x
 * - set tag[x] to tag and desc[x] to index
 */
static bvar_t bool_vartable_new_var(bool_vartable_t *table, uint8_t tag, uint32_t index) {
  uint32_t i;

  i = table->nvars;
  if (i == table->size) {
    extend_bool_vartable(table);
  }
  assert(i < table->size);

  table->tag[i] = tag;
  table->desc[i] = index;
  table->nvars = i+1;

  return i;
}


/*
 * VARIABLE CONSTRUCTORS
 */

/*
 * New variable (no definition)
 */
bvar_t make_fresh_boolvar(bool_vartable_t *table) {
  return bool_vartable_new_var(table, BVAR, 0);
}


/*
 * New atom with given tag and index
 */
bvar_t bool_vartable_add_atom(bool_vartable_t *table, uint8_t tag, uint32_t index) {
  assert(tag > BOR);
  return bool_vartable_new_var(table, tag, index);
}


/*
 * New gate
 */
static bvar_t bool_vartable_add_gate(bool_vartable_t *table, bgate_t *g) {
  uint32_t k;

  k = store_bgate(&table->gates, g);
  return bool_vartable_new_var(table, BGATE, k);
}


/*
 * New OR gate:
 * - n = arity
 * - a = array of n literals
 */
static bvar_t bool_vartable_add_or_gate(bool_vartable_t *table, uint32_t n, literal_t *a) {
  uint32_t k;

  k = store_ordata(&table->ordata, a, n);
  return bool_vartable_new_var(table, BOR, k);
}



/*
 * HASH CONSING
 */
typedef struct gate_hobj_s {
  int_hobj_t m;
  bool_vartable_t *table;
  bgate_t gate;
} gate_hobj_t;


typedef struct orgate_hobj_s {
  int_hobj_t m;
  bool_vartable_t *table;
  uint32_t n;
  literal_t *a;
} orgate_hobj_t;


static uint32_t hash_gate_hobj(gate_hobj_t *o) {
  return hash_bgate(&o->gate);
}

static uint32_t hash_orgate_hobj(orgate_hobj_t *o) {
  return hash_orgate(o->n, o->a);
}


static bool equal_gates(bgate_t *g1, bgate_t *g2) {
  return g1->ttbl == g2->ttbl && g1->var[0] == g2->var[0] && 
    g1->var[1] == g2->var[1] && g1->var[2] == g2->var[2];
}

static bool eq_gate_hobj(gate_hobj_t *o, int32_t i) {
  bool_vartable_t *table;

  table = o->table;
  return boolvar_is_gate(table, i) && equal_gates(&o->gate, boolvar_gate_desc(table, i));
}


static bool equal_or_gates(uint32_t n, literal_t *a, int32_t *b) {
  uint32_t i;

  if (b[0] != n) return false;

  b ++;
  for (i=0; i<n; i++) {
    if (a[i] != b[i]) return false;
  }

  return true;
}

static bool eq_orgate_hobj(orgate_hobj_t *o, int32_t i) {
  bool_vartable_t *table;

  table = o->table;
  return boolvar_is_or(table, i) && equal_or_gates(o->n, o->a, boolvar_or_desc(table, i));
}


static int32_t build_gate_hobj(gate_hobj_t *o) {
  return bool_vartable_add_gate(o->table, &o->gate);
}

static int32_t build_orgate_hobj(orgate_hobj_t *o) {
  return bool_vartable_add_or_gate(o->table, o->n, o->a);
}



/*
 * Global objects for hash consing
 */
static gate_hobj_t gate_hobj = {
  { (hobj_hash_t) hash_gate_hobj, (hobj_eq_t) eq_gate_hobj, (hobj_build_t) build_gate_hobj },
  NULL,
  { 0, { 0, 0, 0 }},
};

static orgate_hobj_t orgate_hobj = {
  { (hobj_hash_t) hash_orgate_hobj, (hobj_eq_t) eq_orgate_hobj, (hobj_build_t) build_orgate_hobj },
  NULL,
  0,
  NULL,
};



/*
 * Hash-consing constructors
 */
bvar_t get_bgate(bool_vartable_t *table, bgate_t *g) {
  gate_hobj.table = table;
  gate_hobj.gate = *g;
  return int_htbl_get_obj(&table->htbl, &gate_hobj.m);
}

bvar_t get_bor(bool_vartable_t *table, uint32_t n, literal_t *a) {
  orgate_hobj.table = table;
  orgate_hobj.n = n;
  orgate_hobj.a = a;
  return int_htbl_get_obj(&table->htbl, &orgate_hobj.m);
}



/*
 * Direct constructor for or gates
 * - no attempt to simplify
 */
static bvar_t direct_or2_gate(bool_vartable_t *table, literal_t l1, literal_t l2) {
  bgate_t g;
  uint8_t m1, m2;

  assert(false_literal < l1 && l1 < l2 && l1 != not(l2));

  m1 = 0x0F;
  if (is_neg(l1)) m1 = 0xF0;
  m2 = 0x33;
  if (is_neg(l2)) m2 = 0xCC;
  
  g.ttbl = (m1 | m2);
  g.var[0] = var_of(l1);
  g.var[1] = var_of(l2);
  g.var[2] = null_bvar;

  return get_bgate(table, &g);
}

static bvar_t direct_or3_gate(bool_vartable_t *table, literal_t l1, literal_t l2, literal_t l3) {
  bgate_t g;
  uint8_t m1, m2, m3;

  assert(false_literal < l1 && l1 < l2 && l2 < l3 && l1 != not(l2) && l2 != not(l3));

  m1 = 0x0F;
  if (is_neg(l1)) m1 = 0xF0;
  m2 = 0x33;
  if (is_neg(l2)) m2 = 0xCC;
  m3 = 0x55;
  if (is_neg(l3)) m3 = 0xAA;

  g.ttbl = (m1 | m2 | m3);
  g.var[0] = var_of(l1);
  g.var[1] = var_of(l2);
  g.var[2] = var_of(l3);

  return get_bgate(table, &g);
}



/*
 * Same thing for binary xor
 */
static bvar_t direct_xor2_gate(bool_vartable_t *table, literal_t l1, literal_t l2) {
  bgate_t g;

  assert(is_pos(l1) && is_pos(l2) && l1 < l2 && false_literal < l1);
  
  g.ttbl = 0x3C;
  g.var[0] = var_of(l1);
  g.var[1] = var_of(l2);
  g.var[2] = null_bvar;

  return get_bgate(table, &g);  
}



/*
 * Simplify and normalize (or a[0] ... a[n-1]) then build the gate
 * - assume that none of a[0] ... a[n-1] is true or false
 */
static bvar_t make_or_aux(bool_vartable_t *table, uint32_t n, literal_t *a) {
  literal_t aux, l;
  uint32_t i, p;

  if (n == 0) return false_literal;

  /*
   * Sort, remove duplicates, check for complementary literals
   */
  int_array_sort(a, n);
  l = a[0];
  p = 1;
  for (i=1; i<n; i++) {
    aux = a[i];
    if (aux != l) {
      if (aux == not(l)) return true_literal;
      a[p] = aux;
      l = aux;
      p ++;
    }
  }

  // result: a[0 ... p-1]
  switch (p) {
  case 1:  return a[0];
  case 2:  return direct_or2_gate(table, a[0], a[1]);
  case 3:  return direct_or3_gate(table, a[0], a[1], a[2]);
  default: return get_bor(table, p, a);
  }
}


/*
 * Exported constructors for OR and AND
 */
literal_t make_or(bool_vartable_t *table, uint32_t n, literal_t *a) {
  literal_t l;
  uint32_t i, p;

  p = 0;
  for (i=0; i<n; i++) {
    l = a[i];
    if (l == true_literal) return true_literal;
    if (l != false_literal) {
      a[p] = l;
      p ++;
    }
  }

  return pos_lit(make_or_aux(table, p, a));
}

literal_t make_and(bool_vartable_t *table, uint32_t n, literal_t *a) {
  literal_t l;
  uint32_t i, p;

  p = 0;
  for (i=0; i<n; i++) {
    l = a[i];
    if (l == false_literal) return false_literal;
    if (l != true_literal) {
      a[p] = not(l);
      p ++;
    }
  }

  return neg_lit(make_or_aux(table, p, a));
}




/*
 * N-ary XOR contructor
 */
literal_t make_xor(bool_vartable_t *table, uint32_t n, literal_t *a) {
  literal_t l;
  uint32_t i, p, sign;

  /*
   * First pass: remove the true and false literals from a.
   * Convert all literals to positive polarity
   * Flip sign every time we flip a literal polarity
   */
  sign = 0;
  p = 0;
  for (i=0; i<n; i++) {
    l = a[i];
    if (l == true_literal) {
      sign ^= 1; // flip sign
    } else if (l != false_literal) {
      sign ^= sign_of_lit(l);      // flip sign if l is negative
      a[p] = unsigned_literal(l);  // convert l to not(l) if l is negative
      p ++;
    }
  }
  n = p;


  /*
   * Second pass: sort then apply the rule (xor x x) = 0
   */
  if (n >= 2) {
    int_array_sort(a, n);
    p = 0;
    i = 0;
    while (i<n-1) {
      l = a[i];
      if (l == a[i+1]) {
	i += 2;
      } else {
	a[p] = l;
	p ++;
	i ++;
      }
    }
    assert(i == n-1 || i == n);
    if (i < n) {
      a[p] = a[i];
      p ++;
    }
    n = p;
  }


  /*
   * Result:  (xor a[0] ... a[n-1]) if sign is 0
   *      or (not (xor a[0] ... a[n-1])) if sign is 1
   */
  l = false_literal;
  if (n > 0) {
    l = a[0];
    for (i=1; i<n; i++) {
      l = direct_xor2_gate(table, l, a[i]);
    }
  }

  return l ^ sign;
}
