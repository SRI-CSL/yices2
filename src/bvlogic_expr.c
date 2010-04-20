/*
 * Bit-vector logic expressions.
 *
 * Represented as arrays of bits
 */

#include <assert.h>

#include "memalloc.h"
#include "hash_functions.h"
#include "int_array_sort.h"
#include "bvlogic_expr.h"
#include "bv_constants.h"


#define TRACE 0

#if TRACE
#include <stdio.h>
#include <inttypes.h>
#endif

/*
 * Initialize buffer b
 * - nodes = attached node table for bit expressions
 */
void init_bvlogic_buffer(bvlogic_buffer_t *b, node_table_t *nodes) {
  b->nbits = 0;
  b->size = BVLOGIC_BUFFER_INITIAL_SIZE;
  b->bit = (bit_t *) safe_malloc(BVLOGIC_BUFFER_INITIAL_SIZE * sizeof(bit_t));
  b->nodes = nodes;
}


/*
 * Delete b
 */
void delete_bvlogic_buffer(bvlogic_buffer_t *b) {
  safe_free(b->bit);
  b->bit = NULL;
}


/*
 * Clear b
 */
void bvlogic_buffer_clear(bvlogic_buffer_t *b) {
  b->nbits = 0;
}


/*
 * Resize: make b large enough for at least n bits
 */
static void bvlogic_buffer_resize(bvlogic_buffer_t *b, uint32_t n) {
  if (b->size < n) {
    if (n >= BVLOGIC_BUFFER_MAX_SIZE) {
      out_of_memory();
    }
    b->bit = (bit_t *) safe_realloc(b->bit, n * sizeof(bit_t));
    b->size = n;
  }
}


/*
 * Convert b into a bvlogic_expr object, then clear b
 */
bvlogic_expr_t *bvlogic_buffer_get_expr(bvlogic_buffer_t *b) {
  uint32_t i, n;
  bvlogic_expr_t *expr;

  n = b->nbits;
  expr = (bvlogic_expr_t *) safe_malloc(sizeof(bvlogic_expr_t) + n * sizeof(bit_t));
  expr->nbits = n;
  for (i=0; i<n; i++) {
    expr->bit[i] = b->bit[i];
  }

  b->nbits = 0;

  return expr;
}


/*
 * Note: the following operations assume that equal bit indices 
 * represent equal bits. This is true as long as indices are not reused.
 * So this should work as long as the garbage collection is done correctly.
 */

/*
 * Hash bit array stored in b.
 */
uint32_t bvlogic_buffer_hash(bvlogic_buffer_t *b) {
  return jenkins_hash_intarray_var(b->nbits, (int32_t *) b->bit, 0xaef52381);
}

/*
 * Hash bit array e.
 */
uint32_t bvlogic_expr_hash(bvlogic_expr_t *e) {
  return jenkins_hash_intarray_var(e->nbits, (int32_t *) e->bit, 0xaef52381);
}

/*
 * Equality test.
 */
bool bvlogic_buffer_equal_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a) {
  uint32_t i;

  if (n != b->nbits) return false;

  for (i=0; i<n; i++) {
    if (a[i] != b->bit[i]) return false;
  }

  return true;
}


/*
 * Equality test between two bvlogic expressions
 */
bool bvlogic_expr_equal_expr(bvlogic_expr_t *e1, bvlogic_expr_t *e2) {
  uint32_t i, n;

  n = e1->nbits;
  if (n != e2->nbits) return false;

  for (i=0; i<n; i++) {
    if (e1->bit[i] != e2->bit[i]) return false;
  }

  return true;
}


/*
 * Check whether e1 and e2 must be disequal.
 * - i.e., whether e1[i] = not e2[i] for some i
 */
bool bvlogic_must_disequal_expr(bvlogic_expr_t *e1, bvlogic_expr_t *e2) {
  uint32_t i, n;

  n = e1->nbits;
  assert(n == e2->nbits);

  for (i=0; i<n; i++) {
    if (e1->bit[i] == bit_not(e2->bit[i])) return true;
  }

  return false;
}



/*
 * Check whether e and c must be disequal.
 * - i.e., whether e[i] = not c[i] for some i
 * - n = number of bits in c (must be equal to e->nbits).
 */
bool bvlogic_must_disequal_constant(bvlogic_expr_t *e, uint32_t n, uint32_t *c) {
  uint32_t i;

  assert(n == e->nbits);

  for (i=0; i<n; i++) {
    if ((e->bit[i] == true_bit && ! bvconst_tst_bit(c, i))
	|| (e->bit[i] == false_bit && bvconst_tst_bit(c, i))) {
      return true;
    }
  }

  return false;
}



/*
 * Check whether bitvector stored in b is constant.
 */
bool bvlogic_buffer_is_constant(bvlogic_buffer_t *b) {
  uint32_t i, n;

  n = b->nbits;

  for (i=0; i<n; i++) {
    if (! bit_is_const(b->bit[i])) return false;
  }
  return true;
}

/*
 * Check whether bitvector stored in e is constant.
 */
bool bvlogic_expr_is_constant(bvlogic_expr_t *e) {
  uint32_t i, n;

  n = e->nbits;
  for (i=0; i<n; i++) {
    if (! bit_is_const(e->bit[i])) return false;
  }
  return true;
}




/*
 * Convert b to a 64 bit value. If b has fewer than 64 bits,
 * then the result is padded with 0.
 */
uint64_t bvlogic_buffer_get_constant64(bvlogic_buffer_t *b) {
  uint32_t n;
  uint64_t c;

  assert(b->nbits <= 64);
  c = 0;
  n = b->nbits;
  while (n > 0) {
    n --; 
    assert(bit_is_const(b->bit[n]));
    // polarity=0 if b->bit[n] == false_bit
    // polarity=1 if b->bit[n] == true_bit
    c = (c << 1) | bit_const_value(b->bit[n]);
  }

  return c;
}



/*
 * Convert b to a bitvector constant of more than 64 bits.
 * - A fresh constant is allocated
 */
uint32_t *bvlogic_buffer_get_constant(bvlogic_buffer_t *b) {
  uint32_t n, i, k;
  uint32_t *c;

  assert(b->nbits > 64);
  n = b->nbits;
  k = (n + 31) >> 5; // ceil(n/32)

  c = bvconst_alloc(k);
  bvconst_clear(c, k);
  for (i=0; i<n; i++) {
    assert(bit_is_const(b->bit[i]));
    if (b->bit[i] == true_bit) {
      bvconst_set_bit(c, i);
    }
  }

  return c;
}


/*
 * Copy constant stored in b into c, then reset b
 * - b must be a constant.
 */
void bvlogic_buffer_copy_constant(bvlogic_buffer_t *b, bvconstant_t *c) {
  uint32_t n, i, k;

  assert(bvlogic_buffer_is_constant(b));

  n = b->nbits;
  k = (n + 31) >> 5;
  bvconstant_set_bitsize(c, n);

  bvconst_clear(c->data, k);
  for (i=0; i<n; i++) {
    assert(bit_is_const(b->bit[i]));
    if (b->bit[i] == true_bit) {
      bvconst_set_bit(c->data, i);
    }
  }
}



/*
 * Check whether b is equal to a theory variable x
 * - b must equal to the bitarray attached to variable x in manager m
 */
bool bvlogic_buffer_is_variable(bvlogic_buffer_t *b, bv_var_manager_t *m) {
  node_table_t *nodes;
  bit_t *a;
  node_t n0;
  int32_t x;
  uint32_t i;


  if (b->nbits == 0) {
    return false;
  }

  nodes = b->nodes;

  n0 = node_of_bit(b->bit[0]);
  if (! is_variable_node(nodes, n0)) {
    return false;
  }

  x = bv_var_of_node(nodes, n0);

  // check whether bitsize of x == bitsize b
  if (bv_var_bitsize(m, x) != b->nbits) {
    return false;
  }

  // check whether bit array attached to x == b
  a = bv_var_bit_array(m, x);
  if (a == NULL) {
    return false;
  }

  for (i=0; i<b->nbits; i++) {
    if (a[i] != b->bit[i]) return false;
  }

  return true;
}


/*
 * Get variable equal to b: this works only if the previous function
 * returns true.
 */
int32_t bvlogic_buffer_get_variable(bvlogic_buffer_t *b) {
  assert(b->nbits > 0);
  return bv_var_of_node(b->nodes, node_of_bit(b->bit[0]));
}


#if 0
// TOO INEFFICIENT

/*
 * Collect all the bitvector variables occurring in e
 * - store them in u
 * - nodes must be the node table where e was created
 */
void bvlogic_expr_get_vars(bvlogic_expr_t *e, node_table_t *nodes, ivector_t *u) {
  int_hset_t *aux;
  uint32_t i, n;
  uint32_t *a;
  node_t nd;

  aux = node_table_get_node_set(nodes);
  assert(int_hset_is_empty(aux));

  collect_bitarray_nodes(nodes, e->nbits, e->bit, aux);

  /*
   * Scan the set. Collect the variables of all variable nodes
   * Since set is not compacted, we skip all 0 elements
   */
  n = aux->size;
  a = aux->data;
  for (i=0; i<n; i++) {
    nd = a[i];
    if (nd != 0 && is_variable_node(nodes, nd)) {
      ivector_push(u, bv_var_of_node(nodes, nd));
    }
  }

#if TRACE
  printf("---> bvlogic_expr_get_vars: %"PRIu32" bits\n", e->nbits);
  printf("     hset size = %"PRIu32"\n", aux->size);
  printf("     hset card = %"PRIu32"\n", aux->nelems);
  printf("     number of vars = %"PRIu32"\n", u->size);
#endif

  int_hset_reset(aux);
  ivector_remove_duplicates(u);

#if TRACE
  printf("     remove duplicates: %"PRIu32" vars\n", u->size);
  fflush(stdout);
#endif

}


/*
 * Collect all the terms occurring in e
 * - store them in u
 * - nodes must be the node table where e was created
 * - m must be the corresponding bit-vector variable manager
 */
void bvlogic_expr_get_terms(bvlogic_expr_t *e, node_table_t *nodes, bv_var_manager_t *m, ivector_t *u) {
  int_hset_t *aux;
  uint32_t i, n;
  uint32_t *a;
  node_t nd;
  int32_t v, x;

  aux = node_table_get_node_set(nodes);
  assert(int_hset_is_empty(aux));

  collect_bitarray_nodes(nodes, e->nbits, e->bit, aux);


  /*
   * Scan the set and collect the attached terms
   */
  n = aux->size;
  a = aux->data;
  for (i=0; i<n; i++) {
    nd = a[i];
    if (nd != 0 && is_variable_node(nodes, nd)) {
      v = bv_var_of_node(nodes, nd);
      x = bv_var_manager_term_of_var(m, v);
      assert(x >= 0);
      ivector_push(u, x);
    }
  }

  int_hset_reset(aux);
  ivector_remove_duplicates(u);
}

#endif


/*
 * Merge elements of u and v
 * - the elements of u and v must be sorted in increasing order
 * - store the result in u
 */
static void merge_vset(ivector_t *u, vset_t *v) {
  uint32_t i, n, j, p;
  int32_t x, y;

  p = u->size;
  j = 0;
  y = (j < p) ? u->data[j] : INT32_MAX;

  n = v->nelems;
  for (i=0; i<n; i++) {
    x = v->data[i];
    // check whether x belongs to u
    while (y < x) {
      j ++;
      y = (j < p) ? u->data[j] : INT32_MAX;
    }
    if (x < y) {
      // x is not in u: add it after p
      ivector_push(u, x);
    }
  }

  // sort u: we could improve this.
  if (u->size > p) {
    int_array_sort(u->data, u->size);
  }
}

/*
 * Collect all the bitvector variables occurring in e
 * - store them in u
 * - nodes must be the node table where e was created
 */
void bvlogic_expr_get_vars(bvlogic_expr_t *e, node_table_t *nodes, ivector_t *u) {
  vset_t *v, *w;
  uint32_t i, n;

  assert(u->size == 0);
  w = NULL;
  n = e->nbits;
  for (i=0; i<n; i++) {
    v = vars_of_node(nodes, node_of_bit(e->bit[i]));
    if (v != w) {
      // optimization: it's common for all bits to have the same
      // set of variables
      merge_vset(u, v);
      w = v;
    }
  }
}


/*
 * Collect all the terms occurring in e
 * - store them in u
 * - nodes must be the node table where e was created
 * - m must be the corresponding bit-vector variable manager
 */
void bvlogic_expr_get_terms(bvlogic_expr_t *e, node_table_t *nodes, bv_var_manager_t *m, ivector_t *u) {
  uint32_t i, n;
  int32_t v, t;

  // collect the variables of e
  bvlogic_expr_get_vars(e, nodes, u);

  // replace each variable by its term
  n = u->size;
  for (i=0; i<n; i++) {
    v = u->data[i];
    t = bv_var_manager_term_of_var(m, v);
    assert(t >= 0);
    u->data[i] = t;
  }

#ifndef NDEBUG
  // there should be no duplicate terms in u
  int_array_sort(u->data, u->size);
  for (i=0; i+1<u->size; i++) {
    assert(u->data[i] < u->data[i+1]);
  }
#endif
}


/*
 * Get the size of expression e = number of nodes to represent it
 * - nodes must be the node table where e was created
 */
uint32_t bvlogic_expr_size(bvlogic_expr_t *e, node_table_t *nodes) {
  int_hset_t *aux;
  uint32_t n;

  aux = node_table_get_node_set(nodes);
  assert(int_hset_is_empty(aux));
  collect_bitarray_nodes(nodes, e->nbits, e->bit, aux);
  n = aux->nelems;
  int_hset_reset(aux);
  return n;
}


/*
 * Get the size of buffer b = number of nodes to represent it
 */
uint32_t bvlogic_buffer_size(bvlogic_buffer_t *b) {
  node_table_t *nodes;
  int_hset_t *aux;
  uint32_t n;

  nodes = b->nodes;
  aux = node_table_get_node_set(nodes);
  assert(int_hset_is_empty(aux));
  collect_bitarray_nodes(nodes, b->nbits, b->bit, aux);
  n = aux->nelems;
  int_hset_reset(aux);
  return n;
}



/*
 * Get upper and lower bounds on the bitvector stored in array a of n bits
 * - n must be positive
 * - the bound is stored in bvconstant *c
 */

/*
 * Interpreted as an unsigned integer, we have 
 *    a = a[0] + 2 a[1] + ... + 2^(n-1) a[n-1], with 0 <= a[i] <= 1
 * upper bound: replace a[i] by 1 if a[i] is not 0.
 * lower bound: replace a[i] by 0 if a[i] is not 1.
 */
void bitarray_upper_bound_unsigned(uint32_t n, bit_t *a, bvconstant_t *c) {
  uint32_t i;

  assert(n > 0);
  bvconstant_set_all_one(c, n);  // c:= 0b1...1 (n bits)

  for (i=0; i<n; i++) {
    if (a[i] == false_bit) {
      bvconst_clr_bit(c->data, i);
    }
  }
}

void bitarray_lower_bound_unsigned(uint32_t n, bit_t *a, bvconstant_t *c) {
  uint32_t i;

  assert(n > 0);
  bvconstant_set_all_zero(c, n); // c := 0b0...0 (n bits)

  for (i=0; i<n; i++) {
    if (a[i] == true_bit) {
      bvconst_set_bit(c->data, i);
    }
  }
}


/*
 * Interpreted as a signed integer, we have 
 *    b = a[0] + 2 a[1] + ... + 2^(n-2) a[n-2]  - 2^(n-1) a[n-1]
 * upper bound: 
 *     for i=0 to n-2, replace a[i] by 1 if a[i] is not 0
 *     for sign bit, replace a[n-1] by 0 if a[n-1] is not 1
 * lower bound:
 *     for i=0 to n-2, replace a[i] by 0 if a[i] is not 1
 *     for sign bit, replace a[n-1] by 1 if a[n-1] is not 0
 */
void bitarray_upper_bound_signed(uint32_t n, bit_t *a, bvconstant_t *c) {
  uint32_t i;

  assert(n > 0);
  bvconstant_set_all_one(c, n);

  for (i=0; i<n-1; i++) {
    if (a[i] == false_bit) {
      bvconst_clr_bit(c->data, i);
    }
  }

  if (a[i] != true_bit) {
    bvconst_clr_bit(c->data, i);
  }
}


void bitarray_lower_bound_signed(uint32_t n, bit_t *a, bvconstant_t *c) {
  uint32_t i;

  assert(n > 0);
  bvconstant_set_all_zero(c, n);

  for (i=0; i<n-1; i++) {
    if (a[i] == true_bit) {
      bvconst_set_bit(c->data, i);
    }
  }

  if (a[i] != false_bit) {
    bvconst_set_bit(c->data, i);
  }
}


/*
 * Check wether all bits in b are equal to bit
 */
bool bvlogic_buffer_allbit_equal(bvlogic_buffer_t *b, bit_t bit) {
  uint32_t i, n;

  n = b->nbits;
  for (i=0; i<n; i++) {
    if (b->bit[i] != bit) return false;
  }
  return true;
}


/*
 * Set b's size to n bits and initialize all with bit
 */
void bvlogic_buffer_set_allbits(bvlogic_buffer_t *b, uint32_t n, bit_t bit) {
  uint32_t i;

  bvlogic_buffer_resize(b, n);
  for (i=0; i<n; i++) {
    b->bit[i] = bit;
  }
  b->nbits = n;
}


/*
 * Store constant c as a bit array.
 */
void bvlogic_buffer_set_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t i;

  bvlogic_buffer_resize(b, n);
  for (i=0; i<n; i++) {
    b->bit[i] = bit_constant(bvconst_tst_bit(c, i));
  }
  b->nbits = n;
}


/*
 * Store bit array
 */
void bvlogic_buffer_set_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a) {
  uint32_t i;

  bvlogic_buffer_resize(b, n);
  for (i=0; i<n; i++) {
    b->bit[i] = a[i];
  }
  b->nbits = n;
} 


/*
 * Bitwise not
 */
void bvlogic_buffer_not(bvlogic_buffer_t *b) {
  uint32_t i, n;
  n = b->nbits;
  for (i=0; i<n; i++) {
    b->bit[i] = bit_not(b->bit[i]);
  }
}


/*
 * Bitwise and, or, xor with a bitvector constant
 */
void bvlogic_buffer_and_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t i;

  assert(n == b->nbits);

  for (i=0; i<n; i++) {
    if (! bvconst_tst_bit(c, i)) {
      b->bit[i] = false_bit;
    }
  }  
}

void bvlogic_buffer_or_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t i;

  assert(n == b->nbits);

  for (i=0; i<n; i++) {
    if (bvconst_tst_bit(c, i)) {
      b->bit[i] = true_bit;
    }
  }
}

void bvlogic_buffer_xor_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t i;

  assert(n == b->nbits);

  for (i=0; i<n; i++) {
    if (bvconst_tst_bit(c, i)) {
      b->bit[i] = bit_not(b->bit[i]);
    }
  }
}


/*
 * Bitwise and, or, xor with a bit array
 */
void bvlogic_buffer_and_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a) {
  uint32_t i;
  node_table_t *nodes;
  bit_t *bit;

  assert(n == b->nbits);
  nodes = b->nodes;
  bit = b->bit;

  for (i=0; i<n; i++) {
    bit[i] = bit_and2simplify(nodes, bit[i], a[i]);
  }  
}

void bvlogic_buffer_or_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a) {
  uint32_t i;
  node_table_t *nodes;
  bit_t *bit;

  assert(n == b->nbits);
  nodes = b->nodes;
  bit = b->bit;

  for (i=0; i<n; i++) {
    bit[i] = bit_or2simplify(nodes, bit[i], a[i]);
  }  
}

void bvlogic_buffer_xor_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a) {
  uint32_t i;
  node_table_t *nodes;
  bit_t *bit;

  assert(n == b->nbits);
  nodes = b->nodes;
  bit = b->bit;

  for (i=0; i<n; i++) {
    bit[i] = bit_xor2simplify(nodes, bit[i], a[i]);
  }  
}




/*
 * Shift left by k: low-order bits are replaced by padding.
 * - k must be between 0 and b->nbits.
 */
void bvlogic_buffer_shift_left(bvlogic_buffer_t *b, uint32_t k, bit_t padding) {
  uint32_t i;
  bit_t *bit;

  assert(k <= b->nbits);

  bit = b->bit;

  i = b->nbits;
  while (i > k) {
    i --;
    bit[i] = bit[i-k];
  }
  while (i > 0) {
    i --;
    bit[i] = padding;
  }
}


/*
 * Shift right: same constraints.
 */
void bvlogic_buffer_shift_right(bvlogic_buffer_t *b, uint32_t k, bit_t padding) {
  uint32_t i, n;
  bit_t *bit;

  assert(k <= b->nbits);

  bit = b->bit;
  n = b->nbits;
  i=0;

  while (i < n - k) {
    bit[i] = bit[i+k];
    i ++;
  }
  while (i < n) {
    bit[i] = padding;
    i ++;
  }  
}


/*
 * Arithmetic shift: shift to the right, keep sign bit = high order bit of b
 */
void bvlogic_buffer_ashift_right(bvlogic_buffer_t *b, uint32_t k) {
  bit_t sign;
  assert(b->nbits > 0);

  sign = b->bit[b->nbits - 1];
  bvlogic_buffer_shift_right(b, k, sign);
}



/*
 * Auxiliary function for rotation.
 * Reverse subarray b[i]...b[j-1] --> b[j-1]...b[i]
 */
static void reverse_subarray(bit_t *b, uint32_t i, uint32_t j) {
  bit_t aux;

  assert(i <= j);
  if (i == j) return;
  j --;
  while (i < j) {
    aux = b[i];
    b[i] = b[j];
    b[j] = aux;
    i ++;
    j --;
  }
}

/*
 * Rotation to the left by k bits.
 * - k must be between 0 and b->nbits - 1
 */
void bvlogic_buffer_rotate_left(bvlogic_buffer_t *b, uint32_t k) {
  bit_t *bit;
  uint32_t n;

  assert(k < b->nbits);
  bit = b->bit;
  n = b->nbits;

  reverse_subarray(bit, 0, n - k);
  reverse_subarray(bit, n - k, n);
  reverse_subarray(bit, 0, n);
}


/*
 * Rotation to the right
 */
void bvlogic_buffer_rotate_right(bvlogic_buffer_t *b, uint32_t k) {
  bit_t *bit;
  uint32_t n;

  assert(k < b->nbits);
  bit = b->bit;
  n = b->nbits;

  reverse_subarray(bit, 0, k);
  reverse_subarray(bit, k, n);
  reverse_subarray(bit, 0, n);
}


/*
 * Extract subvector b[start .. end].
 * require 0 <= start <= end < b->nbits.
 */
void bvlogic_buffer_extract_subvector(bvlogic_buffer_t *b, uint32_t start, uint32_t end) {
  uint32_t i;
  bit_t *bit;

  assert(start <= end && end < b->nbits);

  end ++;
  b->nbits = end - start;

  if (start > 0) {
    bit = b->bit;
    for (i=start; i<end; i++) {
      bit[i - start] = bit[i];
    }
  }
}



/*
 * Concatenation
 */
void bvlogic_buffer_concat_left_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t i, p;
  bit_t *bit;

  p = b->nbits;
  bvlogic_buffer_resize(b, n + p);
  b->nbits = n + p;

  bit = b->bit;
  for (i=0; i<n; i++) {
    bit[i + p] = bit_constant(bvconst_tst_bit(c, i));
  }
}


void bvlogic_buffer_concat_right_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t i, p;
  bit_t *bit;

  p = b->nbits;
  bvlogic_buffer_resize(b, n + p);
  b->nbits = n + p;

  bit = b->bit;
  i = p;
  while (i > 0) {
    i --;
    bit[n + i] = bit[i];
  }
  for (i=0; i<n; i++) {
    bit[i] = bit_constant(bvconst_tst_bit(c, i));
  }
}


void bvlogic_buffer_concat_left_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a) {
  uint32_t i, p;
  bit_t *bit;

  p = b->nbits;
  bvlogic_buffer_resize(b, n + p);
  b->nbits = n + p;  

  bit = b->bit;
  for (i=0; i<n; i++) {
    bit[i + p] = a[i];
  }
}


void bvlogic_buffer_concat_right_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a) {
  uint32_t i, p;
  bit_t *bit;

  p = b->nbits;
  bvlogic_buffer_resize(b, n + p);
  b->nbits = n + p;

  bit = b->bit;
  i = p;
  while (i > 0) {
    i --;
    bit[n + i] = bit[i];
  }
  for (i=0; i<n; i++) {
    bit[i] = a[i];
  }
}


/*
 * Repeat concat: concatenate b with itself (make n copies)
 * - n must be positive.
 */
void bvlogic_buffer_repeat_concat(bvlogic_buffer_t *b, uint32_t n) {
  uint32_t i, j, p, q;
  uint64_t np;
  bit_t *bit;

  assert(n > 0);
  p = b->bitsize;
  np = n * p;
  if (np >= BVLOGIC_BUFFER_MAX_SIZE) {
    out_of_memory();
  }
  bvlogic_buffer_resize(b, (uint32_t) np);

  bit = b->bit;
  // copy b[0..p-1] n-1 times
  for (i=1, q=p; i<n; i++, q += p) {
    for (j=0; j<p; j++) {
      bit[j + q] = bit[j];
    }
  }  
}


/*
 * Sign-extend: extend b from p to n bits by appending the sign
 * bit (n - p) times
 * - n must be larger than or equal to b->bitsize = p, and p must be positive
 */
void bvlogic_buffer_sign_extend(bvlogic_buffer_t *b, uint32_t n) {
  uint32_t i, p;
  bit_t *bit, sign;

  assert(0 < b->bitsize && b->bitsize <= n);

  p = b->bitsize;
  bvlogic_buffer_resize(b, n);

  bit = b->bit;
  sign = bit[p-1];
  for (i=p; i<n; i++) {
    bit[i] = sign;
  }
}


/*
 * Zero-extend: extend b from p to n bits by appending 0
 * - n must be larger than or equal to b->nbits = p, and p must be positive
 */
void bvlogic_buffer_zero_extend(bvlogic_buffer_t *b, uint32_t n) {
  uint32_t i, p;
  bit_t *bit;

  assert(0 < b->bitsize && b->bitsize <= n);

  p = b->nbits;
  bvlogic_buffer_resize(b, n);

  bit = b->bit;
  for (i=p; i<n; i++) {
    bit[i] = false_bit;
  }
}





/*
 * AND reduction:
 * - compute (and b[0] ... b[n-1]) and store that into b[0]
 */
void bvlogic_buffer_redand(bvlogic_buffer_t *b) {  
  assert(0 < b->nbits);
  b->bit[0] = bit_and(b->nodes, b->bit, b->nbits);
  b->nbits = 1;
}



/*
 * OR reduction
 * - compute (or b[0] ... b[n-1]) and store that into b[0]
 */
void bvlogic_buffer_redor(bvlogic_buffer_t *b) {
  assert(0 < b->nbits);
  b->bit[0] = bit_or(b->nodes, b->bit, b->nbits);
  b->nbits = 1;
}


/*
 * COMP with a constant
 * - compute b[0] := (and (eq b[0] c[0]) ... (eq b[n-1] c[n-1]))
 */
void bvlogic_buffer_comp_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t i;

  assert(n == b->nbits);

  /*
   * first: set b->bit[i] := (eq b->bit[i] c[i]):
   * (eq b->bit[i] false) is not (b->bit[i])
   * (eq b->bit[i] true)  is (b->bit[i])
   */
  for (i=0; i<n; i++) {
    if (! bvconst_tst_bit(c, i)) {
      b->bit[i] = bit_not(b->bit[i]);
    }
  }

  /*
   * Compute the conjunction
   */
  bvlogic_buffer_resize(b, 1);
  b->bit[0] = bit_and(b->nodes, b->bit, n);
  b->nbits = 1;
}



/*
 * Comp with array a
 */
void bvlogic_buffer_comp_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a) {
  uint32_t i;

  assert(n == b->nbits);

  /*
   * first: set b->bit[i] := (eq b->bit[i] a[i]):
   */
  for (i=0; i<n; i++) {
    b->bit[i] = bit_eq2simplify(b->nodes, b->bit[i], a[i]);
  }

  /*
   * Compute the conjunction
   */
  bvlogic_buffer_resize(b, 1);
  b->bit[0] = bit_and(b->nodes, b->bit, n);
  b->nbits = 1;
}




/*
 * CONVERSION OF ADDITION AND PRODUCT TO BV-SHIFT AND BV-OR
 */

/*
 * Attempt to convert b + c * a into (bv-or b (shift-left a k))
 * - c is a bitvector constant of n bits. c must be normalized.
 * - a is a bit array of n bits
 * The conversion works if c is a power of 2 (then k = log_2 c)
 * and if for every index i, we have b[i] == ff or a[i+k] == ff.
 *
 * The function returns true and store b + c * a into b if the 
 * conversion is successful. It returns false otherwise. 
 */
bool bvlogic_buffer_addmul_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a, uint32_t *c) {
  bit_t *bit;
  uint32_t i, w;
  int32_t k;

  assert(n == b->nbits);

  w = (n + 31) >> 5;  // number of words in c
  if (bvconst_is_zero(c, w)) {
    return true; 
  }

  k = bvconst_is_power_of_two(c, w);
  if (k < 0) {
    return false;
  }

  // c = 2^k: check whether b + (a << k) can be done 
  // as a bitwise or operation
  assert(0 <= k && k < n);
  bit = b->bit;
  for (i=k; i<n; i++) {
    if (bit[i] != false_bit && a[i-k] != false_bit) {
      return false;
    }
  }

  // do the bitwise or here
  for (i=k; i<n; i++) {
    if (a[i-k] != false_bit) {
      assert(bit[i] == false_bit);
      bit[i] = a[i-k];
    }
  }

  return true;
}


