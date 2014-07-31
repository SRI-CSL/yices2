/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BUFFERS FOR BITVECTORS REPRESENTED AS ARRAYS OF BOOLEAN TERMS
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "terms/bit_term_conversion.h"
#include "terms/bv64_constants.h"
#include "terms/bvlogic_buffers.h"



/*
 * ALLOCATION/INITIALIZATION
 */

/*
 * Initialize b:
 * - use default size
 * - attach the given term table
 */
void init_bvlogic_buffer(bvlogic_buffer_t *b, node_table_t *nodes) {
  b->bitsize = 0;
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
 * Resize b: make it large enough for at least n bits
 * and set b's bitsize to n.
 */
static void resize_bvlogic_buffer(bvlogic_buffer_t *b, uint32_t n) {
  if (b->size < n) {
    if (n > BVLOGIC_BUFFER_MAX_SIZE) {
      out_of_memory();
    }
    b->bit = (bit_t *) safe_realloc(b->bit, n * sizeof(bit_t));
    b->size = n;
  }
  if (b->bitsize == 0 && n > 0) {
    // increment ref counter in b's node table
    node_table_incref(b->nodes);
  }
  b->bitsize = n;
}



/*
 * Empty buffer b and decrement the ref counter in b's node table/
 */
void bvlogic_buffer_clear(bvlogic_buffer_t *b) {
  if (b->bitsize > 0) {
    node_table_decref(b->nodes);
    b->bitsize = 0;
  }
}



/*
 * TESTS
 */


/*
 * Check whether b is a constant
 */
bool bvlogic_buffer_is_constant(bvlogic_buffer_t *b) {
  uint32_t i, n;

  n = b->bitsize;
  for (i=0; i<n; i++) {
    if (! bit_is_const(b->bit[i])) return false;
  }

  return true;
}


/*
 * Check whether bit b is equal to (select i x)
 */
static bool check_select_bit(node_table_t *nodes, bit_t b, uint32_t i, int32_t x) {
  int32_t p;

  p = node_of_bit(b);
  return bit_is_pos(b) && is_select_node(nodes, p) &&
    index_of_select_node(nodes, p) == i && var_of_select_node(nodes, p) == x;
}

/*
 * Check whether bit b is equal to  (select 0 x) for some x
 */
static bool check_select0_bit(node_table_t *nodes, bit_t b) {
  int32_t p;

  p = node_of_bit(b);
  return bit_is_pos(b) && is_select_node(nodes, p) && index_of_select_node(nodes, p) == 0;
}


/*
 * Check whether b is of the form (sel 0 x) ... (sel k-1 x)
 * - if so return x
 * - otherwise return -1
 */
int32_t bvlogic_buffer_get_var(bvlogic_buffer_t *b) {
  node_table_t *nodes;
  uint32_t i, n;
  bit_t aux;
  int32_t x;

  x = -1;
  n = b->bitsize;
  if (n > 0) {
    nodes = b->nodes;
    aux = b->bit[0];
    if (check_select0_bit(nodes, aux)) {
      // bit[0] is of the form (select 0 x) for some x
      x = var_of_select_node(nodes, node_of_bit(aux));

      // check whether the other bits are (select i x)
      for (i=1; i<n; i++) {
        aux = b->bit[i];
        if (! check_select_bit(nodes, aux, i, x)) {
          x = -1;
          break;
        }
      }
    }
  }

  return x;
}


/*
 * Convert b to a 64 bit value. If b has fewer than 64 bits,
 * then the result is padded with 0.
 */
uint64_t bvlogic_buffer_get_constant64(bvlogic_buffer_t *b) {
  uint32_t n;
  uint64_t c;

  assert(b->bitsize <= 64);
  c = 0;
  n = b->bitsize;
  while (n > 0) {
    n --;
    assert(bit_is_const(b->bit[n]));
    c = (c << 1) | bit_const_value(b->bit[n]);
  }

  return c;
}



/*
 * Copy constant stored in b into c
 * - b must be a constant.
 */
void bvlogic_buffer_get_constant(bvlogic_buffer_t *b, bvconstant_t *c) {
  uint32_t n, i, k;

  n = b->bitsize;
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
 * Check whether all bits in b are equal to bit
 */
bool bvlogic_buffer_allbits_equal(bvlogic_buffer_t *b, bit_t bit) {
  uint32_t i, n;

  n = b->bitsize;
  for (i=0; i<n; i++) {
    if (b->bit[i] != bit) return false;
  }

  return true;
}



/*
 * ASSIGNMENT OPERATIONS
 */
void bvlogic_buffer_set_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c) {
  uint32_t i;

  assert(0 < n && n <= 64);

  resize_bvlogic_buffer(b, n);

  for (i=0; i<n; i++) {
    b->bit[i] = bit_constant(tst_bit64(c, i));
  }
}

void bvlogic_buffer_set_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t i;

  resize_bvlogic_buffer(b, n);

  for (i=0; i<n; i++) {
    b->bit[i] = bit_constant(bvconst_tst_bit(c, i));
  }
}

void bvlogic_buffer_set_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a) {
  uint32_t i;

  assert(0 < n);

  resize_bvlogic_buffer(b, n);

  for (i=0; i<n; i++) {
    b->bit[i] = a[i];
  }
}

void bvlogic_buffer_set_allbits(bvlogic_buffer_t *b, uint32_t n, bit_t bit) {
  uint32_t i;

  assert(0 < n);

  resize_bvlogic_buffer(b, n);

  for (i=0; i<n; i++) {
    b->bit[i] = bit;
  }
}

// v is interpreted as a bit-vector variable
static void bvlogic_buffer_set_bv(bvlogic_buffer_t *b, uint32_t n, int32_t v) {
  uint32_t i;

  assert(0 < n);

  resize_bvlogic_buffer(b, n);

  for (i=0; i<n; i++) {
    b->bit[i] = node_table_alloc_select(b->nodes, i, v);
  }
}


// array of n boolean terms a[0] ... a[n-1]
void bvlogic_buffer_set_term_array(bvlogic_buffer_t *b, term_table_t *table, uint32_t n, const term_t *a) {
  uint32_t i;

  assert(0 < n);

  resize_bvlogic_buffer(b, n);

  for (i=0; i<n; i++) {
    b->bit[i] = convert_term_to_bit(table, b->nodes, a[i], 1);
  }
}



/*
 * Set bit[0 ... k-1] to 1 and bits[k... n-1] to 0
 */
void bvlogic_buffer_set_low_mask(bvlogic_buffer_t *b, uint32_t k, uint32_t n) {
  uint32_t i;

  assert(k < n);

  resize_bvlogic_buffer(b, n);
  for (i=0;i<k; i++) {
    b->bit[i] = true_bit;
  }
  while (i<n) {
    b->bit[i] = false_bit;
    i ++;
  }
}


/*
 * SLICE ASSIGNMENT
 */

/*
 * Given a bitvector u of n bits, the following functions store
 * bits[i ... j] of u into b.
 * - i and j must satisfy 0 <= i <= j < n.
 *
 * The parameters c, a, t are as in the assignment operations above.
 */
void bvlogic_buffer_set_slice_constant64(bvlogic_buffer_t *b, uint32_t i, uint32_t j, uint64_t c) {
  uint32_t k;

  assert(i <= j && j < 64);

  resize_bvlogic_buffer(b, j - i + 1);

  k = 0;
  do {
    b->bit[k] = bit_constant(tst_bit64(c, i));
    k ++;
    i ++;
  } while (i <= j);
}

void bvlogic_buffer_set_slice_constant(bvlogic_buffer_t *b, uint32_t i, uint32_t j, uint32_t *c) {
  uint32_t k;

  assert(i <= j);

  resize_bvlogic_buffer(b, j - i + 1);

  k = 0;
  do {
    b->bit[k] = bit_constant(bvconst_tst_bit(c, i));
    k ++;
    i ++;
  } while (i <= j);
}

void bvlogic_buffer_set_slice_bitarray(bvlogic_buffer_t *b, uint32_t i, uint32_t j, bit_t *a) {
  uint32_t k;

  assert(i <= j);

  resize_bvlogic_buffer(b, j - i + 1);

  k = 0;
  do {
    b->bit[k] = a[i];
    k ++;
    i ++;
  } while (i <= j);
}

// v = bitvector variable
static void bvlogic_buffer_set_slice_bv(bvlogic_buffer_t *b, uint32_t i, uint32_t j, int32_t v) {
  uint32_t k;

  assert(i <= j);

  resize_bvlogic_buffer(b, j - i + 1);

  k = 0;
  do {
    b->bit[k] = node_table_alloc_select(b->nodes, i, v);
    k ++;
    i ++;
  } while (i <= j);
}


// boolean terms a[i] ... a[j]
void bvlogic_buffer_set_slice_term_array(bvlogic_buffer_t *b, term_table_t *table, uint32_t i, uint32_t j, term_t *a) {
  uint32_t k;

  assert(i <= j);

  resize_bvlogic_buffer(b, j - i + 1);

  k = 0;
  do {
    b->bit[k] = convert_term_to_bit(table, b->nodes, a[i], 1);
    k ++;
    i ++;
  } while (i <= j);
}





/*
 * BITWISE OPERATIONS
 */

/*
 * Flip all bits of b
 */
void bvlogic_buffer_not(bvlogic_buffer_t *b) {
  uint32_t i, n;

  n = b->bitsize;
  for (i=0; i<n; i++) {
    b->bit[i] = bit_not(b->bit[i]);
  }
}


/*
 * Bitwise and, or, xor with a small constant c
 * - n = number of bits in c (must be equal to b->bitsize)
 * - n must be between 1 and 64
 */
void bvlogic_buffer_and_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c) {
  uint32_t i;

  assert(n == b->bitsize && 0 < n && n <= 64);

  for (i=0; i<n; i++) {
    if (! tst_bit64(c, i)) {
      b->bit[i] = false_bit;
    }
  }
}

void bvlogic_buffer_or_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c) {
  uint32_t i;

  assert(n == b->bitsize && 0 < n && n <= 64);

  for (i=0; i<n; i++) {
    if (tst_bit64(c, i)) {
      b->bit[i] = true_bit;
    }
  }
}

void bvlogic_buffer_xor_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c) {
  uint32_t i;

  assert(n == b->bitsize && 0 < n && n <= 64);

  for (i=0; i<n; i++) {
    if (tst_bit64(c, i)) {
      b->bit[i] = bit_not(b->bit[i]);
    }
  }
}


/*
 * Bitwise and, or, xor with a large constant c
 * - n = number of bits in c (must be equal to b->bitsize)
 * - c = array of k words (where k = ceil(n/32))
 */
void bvlogic_buffer_and_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t i;

  assert(n == b->bitsize);

  for (i=0; i<n; i++) {
    if (! bvconst_tst_bit(c, i)) {
      b->bit[i] = false_bit;
    }
  }
}

void bvlogic_buffer_or_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t i;

  assert(n == b->bitsize);

  for (i=0; i<n; i++) {
    if (bvconst_tst_bit(c, i)) {
      b->bit[i] = true_bit;
    }
  }
}

void bvlogic_buffer_xor_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t i;

  assert(n == b->bitsize);

  for (i=0; i<n; i++) {
    if (bvconst_tst_bit(c, i)) {
      b->bit[i] = bit_not(b->bit[i]);
    }
  }
}


/*
 * Bitwise and, or, xor with an array of bits
 * - n = number of bits in a (must be equal to b->bitsize)
 */
void bvlogic_buffer_and_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a) {
  uint32_t i;
  node_table_t *nodes;
  bit_t *bit;

  assert(n == b->bitsize);
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

  assert(n == b->bitsize);
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

  assert(n == b->bitsize);
  nodes = b->nodes;
  bit = b->bit;

  for (i=0; i<n; i++) {
    bit[i] = bit_xor2simplify(nodes, bit[i], a[i]);
  }
}


/*
 * Bitwise and, or, xor with a bitvector term v
 * - n = bitsize of v (must be equal to b->bitsize)
 */
static void bvlogic_buffer_and_bv(bvlogic_buffer_t *b, uint32_t n, int32_t v) {
  node_table_t *nodes;
  bit_t *bit;
  bit_t x;
  uint32_t i;

  assert(n == b->bitsize);
  nodes = b->nodes;
  bit = b->bit;

  for (i=0; i<n; i++) {
    x = node_table_alloc_select(nodes, i, v);
    bit[i] = bit_and2simplify(nodes, bit[i], x);
  }
}

static void bvlogic_buffer_or_bv(bvlogic_buffer_t *b, uint32_t n, int32_t v) {
  node_table_t *nodes;
  bit_t *bit;
  bit_t x;
  uint32_t i;

  assert(n == b->bitsize);
  nodes = b->nodes;
  bit = b->bit;

  for (i=0; i<n; i++) {
    x = node_table_alloc_select(nodes, i, v);
    bit[i] = bit_or2simplify(nodes, bit[i], x);
  }
}

static void bvlogic_buffer_xor_bv(bvlogic_buffer_t *b, uint32_t n, int32_t v) {
  node_table_t *nodes;
  bit_t *bit;
  bit_t x;
  uint32_t i;

  assert(n == b->bitsize);
  nodes = b->nodes;
  bit = b->bit;

  for (i=0; i<n; i++) {
    x = node_table_alloc_select(nodes, i, v);
    bit[i] = bit_xor2simplify(nodes, bit[i], x);
  }
}



/*
 * Bitwise or/and/xor with an array of n boolean terms a[0] ... a[n-1]
 */
static void bvlogic_buffer_and_term_array(bvlogic_buffer_t *b, term_table_t *table, uint32_t n, term_t *a) {
  node_table_t *nodes;
  bit_t *bit;
  bit_t x;
  uint32_t i;

  assert(n == b->bitsize);
  nodes = b->nodes;
  bit = b->bit;

  for (i=0; i<n; i++) {
    x = convert_term_to_bit(table, nodes, a[i], 1);
    bit[i] = bit_and2simplify(nodes, bit[i], x);
  }
}


static void bvlogic_buffer_or_term_array(bvlogic_buffer_t *b, term_table_t *table, uint32_t n, term_t *a) {
  node_table_t *nodes;
  bit_t *bit;
  bit_t x;
  uint32_t i;

  assert(n == b->bitsize);
  nodes = b->nodes;
  bit = b->bit;

  for (i=0; i<n; i++) {
    x = convert_term_to_bit(table, nodes, a[i], 1);
    bit[i] = bit_or2simplify(nodes, bit[i], x);
  }
}


static void bvlogic_buffer_xor_term_array(bvlogic_buffer_t *b, term_table_t *table, uint32_t n, term_t *a) {
  node_table_t *nodes;
  bit_t *bit;
  bit_t x;
  uint32_t i;

  assert(n == b->bitsize);
  nodes = b->nodes;
  bit = b->bit;

  for (i=0; i<n; i++) {
    x = convert_term_to_bit(table, nodes, a[i], 1);
    bit[i] = bit_xor2simplify(nodes, bit[i], x);
  }
}





/*
 * CONCATENATION
 *
 * left/right refer to b written in big-endian form: (b[n-1] ... b[0])
 * if v = v[m-1] ... v[0] is the added to b, then
 * - concat_left: v[m-1]...v[0] is added to the left of  b[n-1]
 * - concat_right: v[m-1]...v[0] is added to the right of  b[0]
 */
void bvlogic_buffer_concat_left_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c) {
  uint32_t i, p;
  bit_t *bit;

  p = b->bitsize;
  resize_bvlogic_buffer(b, n + p);

  bit = b->bit;
  for (i=0; i<n; i++) {
    bit[i + p] = bit_constant(tst_bit64(c, i));
  }
}

void bvlogic_buffer_concat_right_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c) {
  uint32_t i, p;
  bit_t *bit;

  p = b->bitsize;
  resize_bvlogic_buffer(b, n + p);

  bit = b->bit;
  i = p;
  while (i > 0) {
    i --;
    bit[n + i] = bit[i];
  }

  for (i=0; i<n; i++) {
    bit[i] = bit_constant(tst_bit64(c, i));
  }
}

void bvlogic_buffer_concat_left_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t i, p;
  bit_t *bit;

  p = b->bitsize;
  resize_bvlogic_buffer(b, n + p);

  bit = b->bit;
  for (i=0; i<n; i++) {
    bit[i + p] = bit_constant(bvconst_tst_bit(c, i));
  }
}

void bvlogic_buffer_concat_right_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t i, p;
  bit_t *bit;

  p = b->bitsize;
  resize_bvlogic_buffer(b, n + p);

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

  p = b->bitsize;
  resize_bvlogic_buffer(b, n + p);

  bit = b->bit;
  for (i=0; i<n; i++) {
    bit[i + p] = a[i];
  }
}

void bvlogic_buffer_concat_right_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a) {
  uint32_t i, p;
  bit_t *bit;

  p = b->bitsize;
  resize_bvlogic_buffer(b, n + p);

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

static void bvlogic_buffer_concat_left_bv(bvlogic_buffer_t *b, uint32_t n, int32_t v) {
  uint32_t i, p;
  bit_t *bit;

  p = b->bitsize;
  resize_bvlogic_buffer(b, n + p);

  bit = b->bit;
  for (i=0; i<n; i++) {
    bit[i + p] = node_table_alloc_select(b->nodes, i, v);
  }
}

static void bvlogic_buffer_concat_right_bv(bvlogic_buffer_t *b, uint32_t n, int32_t v) {
  uint32_t i, p;
  bit_t *bit;

  p = b->bitsize;
  resize_bvlogic_buffer(b, n + p);

  bit = b->bit;
  i = p;
  while (i > 0) {
    i --;
    bit[n + i] = bit[i];
  }

  for (i=0; i<n; i++) {
    bit[i] = node_table_alloc_select(b->nodes, i, v);
  }
}


static void bvlogic_buffer_concat_left_term_array(bvlogic_buffer_t *b, term_table_t *table, uint32_t n, term_t *a) {
  uint32_t i, p;
  bit_t *bit;

  p = b->bitsize;
  resize_bvlogic_buffer(b, n + p);

  bit = b->bit;
  for (i=0; i<n; i++) {
    bit[i + p] = convert_term_to_bit(table, b->nodes, a[i], 1);
  }
}

static void bvlogic_buffer_concat_right_term_array(bvlogic_buffer_t *b, term_table_t *table, uint32_t n, term_t *a) {
  uint32_t i, p;
  bit_t *bit;

  p = b->bitsize;
  resize_bvlogic_buffer(b, n + p);

  bit = b->bit;
  i = p;
  while (i > 0) {
    i --;
    bit[n + i] = bit[i];
  }

  for (i=0; i<n; i++) {
    bit[i] = convert_term_to_bit(table, b->nodes, a[i], 1);
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
  resize_bvlogic_buffer(b, (uint32_t) np);

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
  resize_bvlogic_buffer(b, n);

  bit = b->bit;
  sign = bit[p-1];
  for (i=p; i<n; i++) {
    bit[i] = sign;
  }
}


/*
 * Zero-extend: extend b from p to n bits by appending 0
 * - n must be larger than or equal to b->bitsize = p, and p must be positive
 */
void bvlogic_buffer_zero_extend(bvlogic_buffer_t *b, uint32_t n) {
  uint32_t i, p;
  bit_t *bit;

  assert(0 < b->bitsize && b->bitsize <= n);

  p = b->bitsize;
  resize_bvlogic_buffer(b, n);

  bit = b->bit;
  for (i=p; i<n; i++) {
    bit[i] = false_bit;
  }
}





/*
 * SHIFT AND ROTATE
 */

/*
 * Shift left by k. replace low-order bits by padding.
 * - k must be between 0 and b->bitsize
 */
void bvlogic_buffer_shift_left(bvlogic_buffer_t *b, uint32_t k, bit_t padding) {
  uint32_t i;
  bit_t *bit;

  assert(k <= b->bitsize);

  bit = b->bit;
  i = b->bitsize;
  while (i > k) {
    i --;
    bit[i] = bit[i - k];
  }
  while (i > 0) {
    i --;
    bit[i] = padding;
  }
}


/*
 * Shift right by k. Replace high-order bits by padding.
 * - k must be between 0 and b->bitsize.
 */
void bvlogic_buffer_shift_right(bvlogic_buffer_t *b, uint32_t k, bit_t padding) {
  uint32_t i, n;
  bit_t *bit;

  assert(k <= b->bitsize);

  bit = b->bit;
  n = b->bitsize;
  i = 0;
  while (i < n - k) {
    bit[i] = bit[i + k];
    i ++;
  }
  while (i < n) {
    bit[i] = padding;
    i ++;
  }
}


/*
 * Arithmetic shift: k must be between 0 and b->bitsize
 */
void bvlogic_buffer_ashift_right(bvlogic_buffer_t *b, uint32_t k) {
  bit_t sign;

  assert(b->bitsize > 0);
  sign = b->bit[b->bitsize - 1];
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
 * Left rotation by k bits.
 * - k must be between 0 and b->bitsize - 1
 */
void bvlogic_buffer_rotate_left(bvlogic_buffer_t *b, uint32_t k) {
  bit_t *bit;
  uint32_t n;

  assert(k < b->bitsize);

  bit = b->bit;
  n = b->bitsize;

  reverse_subarray(bit, 0, n - k);
  reverse_subarray(bit, n - k, n);
  reverse_subarray(bit, 0, n);
}


/*
 * Rotation to the right
 * - k must be between 0 and b->bitsize - 1
 */
void bvlogic_buffer_rotate_right(bvlogic_buffer_t *b, uint32_t k) {
  bit_t *bit;
  uint32_t n;

  assert(k < b->bitsize);

  bit = b->bit;
  n = b->bitsize;

  reverse_subarray(bit, 0, k);
  reverse_subarray(bit, k, n);
  reverse_subarray(bit, 0, n);
}




/*
 * SHIFT/ROTATE: SHIFT AMOUNT GIVEN BY A BIT-VECTOR CONSTANT
 */

/*
 * Convert bitvector constant c into a shift amount valid for
 * a bitvector of m bits.
 * - c is interpreted as an unsigned integer.
 * - if c's value is larger than m, return m
 * - otherwise return c's value
 * (so the result is always between 0 and m)
 */
static inline uint32_t shift_amount64(uint64_t c, uint32_t m) {
  return (c >= (uint64_t) m) ? m : (uint32_t) c;
}

// here n = bitsize of c
static uint32_t shift_amount(uint32_t *c, uint32_t n, uint32_t m) {
  uint32_t k, i, s;

  k = (n + 31) >> 5;     // number of words in c
  s = bvconst_get32(c);  // s = lower-order word of c

  // if any of the higher order words is non-zero, return m
  for (i=1; i<k; i++) {
    if (c[i] != 0) return n;
  }

  // the shift amount is s: truncate to m if s is too laree
  return (s < m) ? s : m;
}



/*
 * Shift by the amount stored in a 64bit constant
 */
void bvlogic_buffer_shl_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c) {
  uint32_t k;

  assert(1 <= n && n <= 64 && c == norm64(c, n));
  k = shift_amount64(c, b->bitsize);
  bvlogic_buffer_shift_left0(b, k);
}

void bvlogic_buffer_lshr_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c) {
  uint32_t k;

  assert(1 <= n && n <= 64 && c == norm64(c, n));
  k = shift_amount64(c, b->bitsize);
  bvlogic_buffer_shift_right0(b, k);
}

void bvlogic_buffer_ashr_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c) {
  uint32_t k;

  assert(1 <= n && n <= 64 && c == norm64(c, n));
  k = shift_amount64(c, b->bitsize);
  bvlogic_buffer_ashift_right(b, k);
}



/*
 * Shift by the amount stored in a general constant
 * - n = bitsize of the constant c
 */
void bvlogic_buffer_shl_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t k;

  k = shift_amount(c, n, b->bitsize);
  bvlogic_buffer_shift_left0(b, k);
}

void bvlogic_buffer_lshr_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t k;

  k = shift_amount(c, n, b->bitsize);
  bvlogic_buffer_shift_right0(b, k);
}

void bvlogic_buffer_ashr_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t k;

  k = shift_amount(c, n, b->bitsize);
  bvlogic_buffer_ashift_right(b, k);
}







/*
 * EXTRACTION
 */

/*
 * Extract subvector b[start .. end].
 * require 0 <= start <= end < b->bitsize.
 */
void bvlogic_buffer_extract_subvector(bvlogic_buffer_t *b, uint32_t start, uint32_t end) {
  uint32_t i;
  bit_t *bit;

  assert(start <= end && end < b->bitsize);

  end ++;
  b->bitsize = end - start;

  if (start > 0) {
    bit = b->bit;
    for (i=start; i<end; i++) {
      bit[i - start] = bit[i];
    }
  }
}



/*
 * REDUCTIONS
 */


/*
 * AND reduction:
 * - compute (and b[0] ... b[n-1]) and store that into b[0]
 */
void bvlogic_buffer_redand(bvlogic_buffer_t *b) {
  assert(0 < b->bitsize);
  b->bit[0] = bit_and(b->nodes, b->bit, b->bitsize);
  b->bitsize = 1;
}


/*
 * OR reduction
 * - compute (or b[0] ... b[n-1]) and store that into b[0]
 */
void bvlogic_buffer_redor(bvlogic_buffer_t *b) {
  assert(0 < b->bitsize);
  b->bit[0] = bit_or(b->nodes, b->bit, b->bitsize);
  b->bitsize = 1;
}



/*
 * COMP with a small constant
 * - compute b[0] := (and (eq b[0] c[0]) ... (eq b[n-1] c[n-1]))
 */
void bvlogic_buffer_comp_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c) {
  uint32_t i;

  assert(n == b->bitsize);

  /*
   * first: set b->bit[i] := (eq b->bit[i] c[i]):
   * (eq b->bit[i] false) is not (b->bit[i])
   * (eq b->bit[i] true)  is (b->bit[i])
   */
  for (i=0; i<n; i++) {
    if (! tst_bit64(c, i)) {
      b->bit[i] = bit_not(b->bit[i]);
    }
  }

  /*
   * Compute the conjunction
   */
  resize_bvlogic_buffer(b, 1);
  b->bit[0] = bit_and(b->nodes, b->bit, n);
}


/*
 * COMP with a constant
 * - compute b[0] := (and (eq b[0] c[0]) ... (eq b[n-1] c[n-1]))
 */
void bvlogic_buffer_comp_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t i;

  assert(n == b->bitsize);

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
  resize_bvlogic_buffer(b, 1);
  b->bit[0] = bit_and(b->nodes, b->bit, n);
}



/*
 * COMP with array a
 */
void bvlogic_buffer_comp_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a) {
  uint32_t i;

  assert(n == b->bitsize);

  /*
   * first: set b->bit[i] := (eq b->bit[i] a[i]):
   */
  for (i=0; i<n; i++) {
    b->bit[i] = bit_eq2simplify(b->nodes, b->bit[i], a[i]);
  }

  /*
   * Compute the conjunction
   */
  resize_bvlogic_buffer(b, 1);
  b->bit[0] = bit_and(b->nodes, b->bit, n);
}



/*
 * COMP with a bitvector variable v
 */
static void bvlogic_buffer_comp_bv(bvlogic_buffer_t *b, uint32_t n, int32_t v) {
  bit_t x;
  uint32_t i;

  assert(n == b->bitsize);

  /*
   * first: set b->bit[i] := (eq b->bit[i] a[i]):
   */
  for (i=0; i<n; i++) {
    x = node_table_alloc_select(b->nodes, i, v);
    b->bit[i] = bit_eq2simplify(b->nodes, b->bit[i], x);
  }

  /*
   * Compute the conjunction
   */
  resize_bvlogic_buffer(b, 1);
  b->bit[0] = bit_and(b->nodes, b->bit, n);
}




/*
 * COMP with an array of n terms
 */
static void bvlogic_buffer_comp_term_array(bvlogic_buffer_t *b, term_table_t *table, uint32_t n, term_t *a) {
  bit_t x;
  uint32_t i;

  assert(n == b->bitsize);

  /*
   * first: set b->bit[i] := (eq b->bit[i] a[i]):
   */
  for (i=0; i<n; i++) {
    x = convert_term_to_bit(table, b->nodes, a[i], 1);
    b->bit[i] = bit_eq2simplify(b->nodes, b->bit[i], x);
  }

  /*
   * Compute the conjunction
   */
  resize_bvlogic_buffer(b, 1);
  b->bit[0] = bit_and(b->nodes, b->bit, n);
}



/*
 * OPERATIONS WITH BIT-VECTOR TERMS AS OPERANDS
 */

/*
 * Copy t into buffer b
 * - t must be a bitvector term in table
 */
void bvlogic_buffer_set_term(bvlogic_buffer_t *b, term_table_t *table, term_t t) {
  bvconst64_term_t *c64;
  bvconst_term_t *c;
  composite_term_t *d;
  uint32_t n;
  int32_t i;

  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t));

  i = index_of(t);
  switch (table->kind[i]) {
  case BV64_CONSTANT:
    c64 = bvconst64_for_idx(table, i);
    bvlogic_buffer_set_constant64(b, c64->bitsize, c64->value);
    break;

  case BV_CONSTANT:
    c = bvconst_for_idx(table, i);
    bvlogic_buffer_set_constant(b, c->bitsize, c->data);
    break;

  case BV_ARRAY:
    d = composite_for_idx(table, i);
    bvlogic_buffer_set_term_array(b, table, d->arity, d->arg);
    break;

  default:
    n = bitsize_for_idx(table, i);
    bvlogic_buffer_set_bv(b, n, t);
    break;
  }
}


/*
 * Copy bits i ... j of t into b
 */
void bvlogic_buffer_set_slice_term(bvlogic_buffer_t *b, term_table_t *table, uint32_t i, uint32_t j, term_t t) {
  bvconst64_term_t *c64;
  bvconst_term_t *c;
  composite_term_t *d;
  int32_t k;

  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) && i <= j);

  k = index_of(t);
  switch (table->kind[k]) {
  case BV64_CONSTANT:
    c64 = bvconst64_for_idx(table, k);
    assert(j < c64->bitsize);
    bvlogic_buffer_set_slice_constant64(b, i, j, c64->value);
    break;

  case BV_CONSTANT:
    c = bvconst_for_idx(table, k);
    assert(j < c->bitsize);
    bvlogic_buffer_set_slice_constant(b, i, j, c->data);
    break;

  case BV_ARRAY:
    d = composite_for_idx(table, k);
    assert(j < d->arity);
    bvlogic_buffer_set_slice_term_array(b, table, i, j, d->arg);
    break;

  default:
    assert(j < bitsize_for_idx(table, k));
    bvlogic_buffer_set_slice_bv(b, i, j, t);
    break;
  }
}




/*
 * Bitwise and/or/xor
 * - t must be a bitvector term in table of bitsize equal to b's.
 */
void bvlogic_buffer_and_term(bvlogic_buffer_t *b, term_table_t *table, term_t t) {
  bvconst64_term_t *c64;
  bvconst_term_t *c;
  composite_term_t *d;
  uint32_t n;
  int32_t i;

  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) &&
         term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (table->kind[i]) {
  case BV64_CONSTANT:
    c64 = bvconst64_for_idx(table, i);
    bvlogic_buffer_and_constant64(b, c64->bitsize, c64->value);
    break;

  case BV_CONSTANT:
    c = bvconst_for_idx(table, i);
    bvlogic_buffer_and_constant(b, c->bitsize, c->data);
    break;

  case BV_ARRAY:
    d = composite_for_idx(table, i);
    bvlogic_buffer_and_term_array(b, table, d->arity, d->arg);
    break;

  default:
    n = bitsize_for_idx(table, i);
    bvlogic_buffer_and_bv(b, n, t);
    break;
  }
}


void bvlogic_buffer_or_term(bvlogic_buffer_t *b, term_table_t *table, term_t t) {
  bvconst64_term_t *c64;
  bvconst_term_t *c;
  composite_term_t *d;
  uint32_t n;
  int32_t i;

  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) &&
         term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (table->kind[i]) {
  case BV64_CONSTANT:
    c64 = bvconst64_for_idx(table, i);
    bvlogic_buffer_or_constant64(b, c64->bitsize, c64->value);
    break;

  case BV_CONSTANT:
    c = bvconst_for_idx(table, i);
    bvlogic_buffer_or_constant(b, c->bitsize, c->data);
    break;

  case BV_ARRAY:
    d = composite_for_idx(table, i);
    bvlogic_buffer_or_term_array(b, table, d->arity, d->arg);
    break;

  default:
    n = bitsize_for_idx(table, i);
    bvlogic_buffer_or_bv(b, n, t);
    break;
  }
}


void bvlogic_buffer_xor_term(bvlogic_buffer_t *b, term_table_t *table, term_t t) {
  bvconst64_term_t *c64;
  bvconst_term_t *c;
  composite_term_t *d;
  uint32_t n;
  int32_t i;

  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) &&
         term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (table->kind[i]) {
  case BV64_CONSTANT:
    c64 = bvconst64_for_idx(table, i);
    bvlogic_buffer_xor_constant64(b, c64->bitsize, c64->value);
    break;

  case BV_CONSTANT:
    c = bvconst_for_idx(table, i);
    bvlogic_buffer_xor_constant(b, c->bitsize, c->data);
    break;

  case BV_ARRAY:
    d = composite_for_idx(table, i);
    bvlogic_buffer_xor_term_array(b, table, d->arity, d->arg);
    break;

  default:
    n = bitsize_for_idx(table, i);
    bvlogic_buffer_xor_bv(b, n, t);
    break;
  }
}


/*
 * COMP reduction: t must be a valid bitvector term of same size as b
 */
void bvlogic_buffer_comp_term(bvlogic_buffer_t *b, term_table_t *table, term_t t) {
  bvconst64_term_t *c64;
  bvconst_term_t *c;
  composite_term_t *d;
  uint32_t n;
  int32_t i;

  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) &&
         term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (table->kind[i]) {
  case BV64_CONSTANT:
    c64 = bvconst64_for_idx(table, i);
    bvlogic_buffer_comp_constant64(b, c64->bitsize, c64->value);
    break;

  case BV_CONSTANT:
    c = bvconst_for_idx(table, i);
    bvlogic_buffer_comp_constant(b, c->bitsize, c->data);
    break;

  case BV_ARRAY:
    d = composite_for_idx(table, i);
    bvlogic_buffer_comp_term_array(b, table, d->arity, d->arg);
    break;

  default:
    n = bitsize_for_idx(table, i);
    bvlogic_buffer_comp_bv(b, n, t);
    break;
  }
}



/*
 * Concatenation: t must be a bitvector term in table
 */
void bvlogic_buffer_concat_left_term(bvlogic_buffer_t *b, term_table_t *table, term_t t) {
  bvconst64_term_t *c64;
  bvconst_term_t *c;
  composite_term_t *d;
  uint32_t n;
  int32_t i;

  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t));

  i = index_of(t);
  switch (table->kind[i]) {
  case BV64_CONSTANT:
    c64 = bvconst64_for_idx(table, i);
    bvlogic_buffer_concat_left_constant64(b, c64->bitsize, c64->value);
    break;

  case BV_CONSTANT:
    c = bvconst_for_idx(table, i);
    bvlogic_buffer_concat_left_constant(b, c->bitsize, c->data);
    break;

  case BV_ARRAY:
    d = composite_for_idx(table, i);
    bvlogic_buffer_concat_left_term_array(b, table, d->arity, d->arg);
    break;

  default:
    n = bitsize_for_idx(table, i);
    bvlogic_buffer_concat_left_bv(b, n, t);
    break;
  }
}

void bvlogic_buffer_concat_right_term(bvlogic_buffer_t *b, term_table_t *table, term_t t) {
  bvconst64_term_t *c64;
  bvconst_term_t *c;
  composite_term_t *d;
  uint32_t n;
  int32_t i;

  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t));

  i = index_of(t);
  switch (table->kind[i]) {
  case BV64_CONSTANT:
    c64 = bvconst64_for_idx(table, i);
    bvlogic_buffer_concat_right_constant64(b, c64->bitsize, c64->value);
    break;

  case BV_CONSTANT:
    c = bvconst_for_idx(table, i);
    bvlogic_buffer_concat_right_constant(b, c->bitsize, c->data);
    break;

  case BV_ARRAY:
    d = composite_for_idx(table, i);
    bvlogic_buffer_concat_right_term_array(b, table, d->arity, d->arg);
    break;

  default:
    n = bitsize_for_idx(table, i);
    bvlogic_buffer_concat_right_bv(b, n, t);
    break;
  }
}

