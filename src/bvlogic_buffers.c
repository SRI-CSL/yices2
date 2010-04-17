/*
 * BUFFERS FOR BITVECTORS REPRESENTED AS ARRAYS OF BOOLEAN TERMS
 */

#include <assert.h>

#include "memalloc.h"
#include "bv64_constants.h"
#include "bvlogic_buffers.h"



/*
 * ALLOCATION/INITIALIZATION
 */

/*
 * Initialize b:
 * - use default size
 * - attach the given term table
 */
void init_bvlogic_buffer(bvlogic_buffer_t *b, term_table_t *terms) {
  b->bitsize = 0;
  b->size = BVLOGIC_BUFFER_INITIAL_SIZE;
  b->bit = (term_t *) safe_malloc(BVLOGIC_BUFFER_INITIAL_SIZE * sizeof(term_t));
  b->terms = terms;
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
 */
static void resize_bvlogic_buffer(bvlogic_buffer_t *b, uint32_t n) {
  if (b->size < n) {
    if (n > BVLOGIC_BUFFER_MAX_SIZE) {
      out_of_memory();
    }
    b->bit = (term_t *) safe_realloc(b->bit, n * sizeof(term_t));
    b->size = n;
  }
}




/*
 * TESTS
 */

/*
 * Check whether t is a constant bit 
 * (i.e., either true_term or false_term)
 */
static inline bool bit_is_const(term_t t) {
  return index_of(t) == bool_const;
}


/*
 * Convert bool tt to a term:
 */
static inline term_t bit_constant(bool tt) {
  return mk_term(bool_const, tt);
}


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
    assert(b->bit[n] == true_term || b->bit[n] == false_term);
    // is_pos=0 if b->bit[n] == false_term
    // is_pos=1 if b->bit[n] == true_term
    c = (c << 1) | is_pos_term(b->bit[n]);
  }

  return c;
}



/*
 * Copy constant stored in b into c, then reset b
 * - b must be a constant.
 */
void bvlogic_buffer_get_constant(bvlogic_buffer_t *b, bvconstant_t *c) {
  uint32_t n, i, k;

  assert(bvlogic_buffer_is_constant(b));

  n = b->bitsize;
  k = (n + 31) >> 5;
  bvconstant_set_bitsize(c, n);

  bvconst_clear(c->data, k);
  for (i=0; i<n; i++) {
    assert(bit_is_const(b->bit[i]));
    if (b->bit[i] == true_term) {
      bvconst_set_bit(c->data, i);
    }
  }
}


/*
 * Check wether all bits in b are equal to term 'bit'
 * - bit must be a valid boolean term
 */
bool bvlogic_buffer_allbits_equal(bvlogic_buffer_t *b, term_t bit) {
  uint32_t i, n;

  assert(is_boolean_term(b->terms, bit));

  n = b->bitsize;
  for (i=0; i<n; i++) {
    if (b->bit[i] != bit) return false;
  }

  return true;
}



/*
 * ASSIGNMENT OPERATIONS
 *
 * For operations that use a term t: t must be a bit-vector term defined in
 * the b->terms, and t must have the same bitsize as b.
 *
 * For all the other operations: 
 * - n = number of bits in the operand (n must be equal to b's bitsize).
 * - the array a used as operand must be an array of n boolean terms.
 */
void bvlogic_buffer_set_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c) {
  uint32_t i;

  assert(0 < n && n <= 64 && b->size >= 64);

  b->bitsize = n;
  for (i=0; i<n; i++) {
    b->bit[i] = bit_constant(tst_bit64(c, i));
  }
}

void bvlogic_buffer_set_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
  uint32_t i;

  resize_bvlogic_buffer(b, n);

  b->bitsize = n;
  for (i=0; i<n; i++) {
    b->bit[i] = bit_constant(bvconst_tst_bit(c, i));
  }
}

void bvlogic_buffer_set_bitarray(bvlogic_buffer_t *b, uint32_t n, term_t *a) {
  uint32_t i;

  resize_bvlogic_buffer(b, n);

  b->bitsize = n;
  for (i=0; i<n; i++) {
    assert(is_boolean_term(b->terms, a[i]));
    b->bit[i] = a[i];
  }
}

void bvlogic_buffer_set_allbits(bvlogic_buffer_t *b, uint32_t n, term_t bit) {
  uint32_t i;

  assert(is_boolean_term(b->terms, bit));

  resize_bvlogic_buffer(b, n);

  b->bitsize = n;
  for (i=0; i<n; i++) {
    b->bit[i] = bit;
  }
}


// convert t to the array (bit 0 t) ... (bit n-1 t) where n = bitsize of t
static void bvlogic_buffer_set_term0(bvlogic_buffer_t *b, term_t t) {
  term_table_t *terms;
  uint32_t i, n;

  terms = b->terms;
  n = term_bitsize(terms, t);

  resize_bvlogic_buffer(b, n);

  b->bitsize = n;
  for (i=0; i<n; i++) {
    b->bit[i] = bit_term(terms, i, t);
  }
}

void bvlogic_buffer_set_term(bvlogic_buffer_t *b, term_t t) {  
  term_table_t *terms;
  bvconst64_term_t *c64;
  bvconst_term_t *c;
  composite_term_t *p;
  int32_t i;

  assert(is_pos_term(t) && is_bitvector_term(b->terms, t));

  terms = b->terms;
  i = index_of(t);
  switch (terms->kind[i]) {
  case BV64_CONSTANT:
    c64 = bvconst64_for_idx(terms, i);
    bvlogic_buffer_set_constant64(b, c64->bitsize, c64->value);
    break;

  case BV_CONSTANT:
    c = bvconst_for_idx(terms, i);
    bvlogic_buffer_set_constant(b, c->bitsize, c->data);
    break;

  case BV_ARRAY:
    p = composite_for_idx(terms, i);
    bvlogic_buffer_set_bitarray(b, p->arity, p->arg);
    break;

  default:
    bvlogic_buffer_set_term0(b, t);
    break;
  }  
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
    b->bit[i] = opposite_term(b->bit[i]);
  }
}


/*
 * Bitwise and, or, xro with a small constant c
 * - n = number of bits in c (must be equal to b->bitsize)
 * - n must be between 1 and 64
 */
void bvlogic_buffer_and_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c) {  
}

void bvlogic_buffer_or_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c) {
}

void bvlogic_buffer_xor_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c) {
}



void bvlogic_buffer_and_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
}

void bvlogic_buffer_or_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
}

void bvlogic_buffer_xor_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c) {
}


void bvlogic_buffer_and_bitarray(bvlogic_buffer_t *b, uint32_t n, term_t *a) {
}

void bvlogic_buffer_or_bitarray(bvlogic_buffer_t *b, uint32_t n, term_t *a) {
}

void bvlogic_buffer_xor_bitarray(bvlogic_buffer_t *b, uint32_t n, term_t *a) {
}


void bvlogic_buffer_and_term(bvlogic_buffer_t *b, term_t t) {
}

void bvlogic_buffer_or_term(bvlogic_buffer_t *b, term_t t) {
}

void bvlogic_buffer_xor_term(bvlogic_buffer_t *b, term_t t) {
}


