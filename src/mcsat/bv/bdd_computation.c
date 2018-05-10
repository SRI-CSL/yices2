/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "bdd_computation.h"
#include "bv_utils.h"

#include "terms/bv64_constants.h"

//#define DEBUG_PRINT(x, n) fprintf(stderr, #x" = "); bdds_print(cudd, x, n, stderr); fprintf(stderr, "\n");
#define DEBUG_PRINT(x, n)

static inline
void bdds_reverse(BDD** bdds, uint32_t n) {
  assert(n > 0);
  BDD** p = bdds;
  BDD** q = bdds + n - 1;
  BDD* tmp;
  while (p < q) {
    tmp = *p; *p = *q; *q = tmp;
    p ++; q --;
  }
}

static inline
void bdds_swap(BDD** a, BDD** b, uint32_t n) {
  BDD* tmp;
  for (uint32_t i = 0; i < n; ++ i) {
    assert(a[i] != NULL);
    assert(b[i] != NULL);
    tmp = a[i]; a[i] = b[i]; b[i] = tmp;
  }
}

static inline
void bdds_copy(BDD** out, BDD** a, uint32_t n) {
  for (uint32_t i = 0; i < n; ++ i) {
    assert(a[i] != NULL);
    assert(out[i] == NULL);
    out[i] = a[i];
    Cudd_Ref(out[i]);
  }
}

static inline
void bdds_move(BDD** out, BDD** a, uint32_t n) {
  for (uint32_t i = 0; i < n; ++ i) {
    assert(a[i] != NULL);
    assert(out[i] == NULL);
    out[i] = a[i];
    a[i] = NULL;
  }
}

CUDD* bdds_new() {
  CUDD* cudd = (CUDD*) safe_malloc(sizeof(CUDD));
  cudd->cudd = Cudd_Init(0, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS,0);
  cudd->tmp_alloc_size = 0;
  cudd->tmp_inputs = NULL;
  cudd->tmp_model = NULL;
  for (uint32_t i = 0; i < BDDS_RESERVE_MAX; ++ i) {
    init_pvector(&cudd->reserve[i], 0);
  }
  cudd->reserve_i = 0;
  return cudd;
}

void bdds_delete(CUDD* cudd) {
  int leaks = Cudd_CheckZeroRef(cudd->cudd);
  (void) leaks;
  assert(leaks == 0);
  Cudd_Quit(cudd->cudd);
  safe_free(cudd->tmp_inputs);
  safe_free(cudd->tmp_model);
  assert(cudd->reserve_i == 0);
  for (uint32_t i = 0; i < BDDS_RESERVE_MAX; ++ i) {
    assert(cudd->reserve[i].size == 0);
    delete_pvector(&cudd->reserve[i]);
  }
}

BDD** bdds_allocate_reserve(CUDD* cudd, uint32_t n) {
  assert(n > 0);
  if (cudd->reserve[cudd->reserve_i].size > 0) {
    cudd->reserve_i ++;
  }
  assert(cudd->reserve_i < BDDS_RESERVE_MAX);
  assert(cudd->reserve[cudd->reserve_i].size == 0);
  for (uint32_t i = 0; i < n; ++ i) {
    pvector_push(&cudd->reserve[cudd->reserve_i], NULL);
  }
  return (BDD**) cudd->reserve[cudd->reserve_i].data;
}

void bdds_remove_reserve(CUDD* cudd, uint32_t n) {
  assert(n > 0);
  assert(cudd->reserve[cudd->reserve_i].size == n);
  for (uint32_t i = 0; i < n; ++ i) {
    assert(cudd->reserve[cudd->reserve_i].data[i] == NULL);
  }
  pvector_reset(&cudd->reserve[cudd->reserve_i]);
  if (cudd->reserve_i > 0) {
    cudd->reserve_i --;
  }
}

void bdds_init(BDD** a, uint32_t n) {
  for(uint32_t i = 0; i < n; ++ i) {
    a[i] = NULL;
  }
}

void bdds_clear(CUDD* cudd, BDD** a, uint32_t n) {
  for(uint32_t i = 0; i < n; ++ i) {
    if (a[i] != NULL) {
      Cudd_IterDerefBdd(cudd->cudd, a[i]);
    }
    a[i] = NULL;
  }
}

void bdds_attach(BDD** a, uint32_t n) {
  for(uint32_t i = 0; i < n; ++ i) {
    assert(a[i] != NULL);
    Cudd_Ref(a[i]);
  }
}

bool bdds_eq(BDD** a, BDD** b, uint32_t n) {
  for(uint32_t i = 0; i < n; ++ i) {
    if (a[i] != b[i]) {
      return false;
    }
  }
  return true;
}

void bdds_print(CUDD* cudd, BDD** a, uint32_t n, FILE* out) {
  Cudd_DumpFactoredForm(cudd->cudd, n, a, NULL, NULL, out);
}

void bdds_mk_variable(CUDD* cudd, BDD** out, uint32_t n) {
  BDD* bdd_i = NULL;
  for (uint32_t i = 0; i < n; ++i) {
    bdd_i = Cudd_bddNewVar(cudd->cudd);
    out[i] = bdd_i;
    // We do increase the reference count so that we are uniform when dereferencing
    Cudd_Ref(bdd_i);
  }
  if (bdd_i) {
    // Max index: last allocated variable
    unsigned int needed_size = Cudd_NodeReadIndex(bdd_i) + 1;
    if (needed_size > cudd->tmp_alloc_size) {
      if (cudd->tmp_alloc_size == 0) {
        cudd->tmp_alloc_size = 10;
      }
      while (needed_size > cudd->tmp_alloc_size) {
        cudd->tmp_alloc_size += cudd->tmp_alloc_size >> 1;
      }
      cudd->tmp_inputs = (int*) safe_realloc(cudd->tmp_inputs, sizeof(int)*cudd->tmp_alloc_size);
      cudd->tmp_model = (char*) safe_realloc(cudd->tmp_model, sizeof(char)*cudd->tmp_alloc_size);
    }
  }
}

void bdds_mk_zero(CUDD* cudd, BDD** out, uint32_t n) {
  for(uint32_t i = 0; i < n; ++ i) {
    assert(out[i] == NULL);
    out[i] = Cudd_ReadLogicZero(cudd->cudd);
    Cudd_Ref(out[i]);
  }
}

void bdds_mk_one(CUDD* cudd, BDD** out, uint32_t n) {
  for(uint32_t i = 0; i < n; ++ i) {
    assert(out[i] == NULL);
    if (i) {
      out[i] = Cudd_ReadLogicZero(cudd->cudd);
    } else {
      out[i] = Cudd_ReadOne(cudd->cudd);
    }
    Cudd_Ref(out[i]);
  }
}

void bdds_mk_constant_64(CUDD* cudd, BDD** out, uint32_t n, uint64_t c) {
  for(uint32_t i = 0; i < n; ++ i) {
    assert(out[i] == NULL);
    bool bit_i = tst_bit64(c, i);
    out[i] = bit_i ? Cudd_ReadOne(cudd->cudd) : Cudd_ReadLogicZero(cudd->cudd);
    Cudd_Ref(out[i]);
  }
}

void bdds_mk_constant_raw(CUDD* cudd, BDD** out, uint32_t n, const uint32_t* c) {
  for(uint32_t i = 0; i < n; ++ i) {
    assert(out[i] == NULL);
    bool bit_i = bvconst_tst_bit(c, i);
    out[i] = bit_i ? Cudd_ReadOne(cudd->cudd) : Cudd_ReadLogicZero(cudd->cudd);
    Cudd_Ref(out[i]);
  }
}

void bdds_mk_constant(CUDD* cudd, BDD** out, uint32_t n, const bvconstant_t* c) {
  assert(n == c->bitsize);
  for(uint32_t i = 0; i < n; ++ i) {
    assert(out[i] == NULL);
    bool bit_i = bvconst_tst_bit(c->data, i);
    out[i] = bit_i ? Cudd_ReadOne(cudd->cudd) : Cudd_ReadLogicZero(cudd->cudd);
    Cudd_Ref(out[i]);
  }
}

void bdds_mk_not(CUDD* cudd, BDD** out, BDD** a, uint32_t n) {
  for(uint32_t i = 0; i < n; ++ i) {
    assert(out[i] == NULL);
    out[i] = Cudd_Not(a[i]);
    Cudd_Ref(out[i]);
  }
}

void bdds_mk_and(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n) {
  for(uint32_t i = 0; i < n; ++ i) {
    assert(out[i] == NULL);
    out[i] = Cudd_bddAnd(cudd->cudd, a[i], b[i]);
    Cudd_Ref(out[i]);
  }
}

void bdds_mk_or(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n) {
  for(uint32_t i = 0; i < n; ++ i) {
    assert(out[i] == NULL);
    out[i] = Cudd_bddOr(cudd->cudd, a[i], b[i]);
    Cudd_Ref(out[i]);
  }
}

void bdds_mk_2s_complement(CUDD* cudd, BDD** out, BDD** a, uint32_t n) {
  BDD* carry = Cudd_ReadOne(cudd->cudd);
  Cudd_Ref(carry);

  for(uint32_t i = 0; i < n; ++ i) {
    BDD* a_neg = Cudd_Not(a[i]);
    BDD* sum = Cudd_bddXor(cudd->cudd, carry, a_neg);
    Cudd_Ref(sum);

    BDD* new_carry = Cudd_bddAnd(cudd->cudd, carry, a_neg);
    Cudd_Ref(new_carry);
    Cudd_IterDerefBdd(cudd->cudd, carry);
    carry = new_carry;

    assert(out[i] == NULL);
    out[i] = sum;
  }

  Cudd_IterDerefBdd(cudd->cudd, carry);
}

void bdds_mk_shl(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n) {
  BDD** shift_const = bdds_allocate_reserve(cudd, n);
  BDD* b_eq_shift_const = NULL;

  bdds_mk_zero(cudd, out, n);

  for (uint32_t shift = 0; shift < n; ++ shift) {

    bdds_mk_constant_64(cudd, shift_const, n, shift);
    bdds_mk_eq(cudd, &b_eq_shift_const, b, shift_const, n);

    for (uint32_t i = 0; i < n; ++ i) {
      BDD* shifted_a_i = i < shift ? Cudd_ReadLogicZero(cudd->cudd) : a[i-shift];
      Cudd_Ref(shifted_a_i);

      BDD* else_case = out[i];
      out[i]  = Cudd_bddIte(cudd->cudd, b_eq_shift_const, shifted_a_i, else_case);
      Cudd_Ref(out[i]);

      Cudd_IterDerefBdd(cudd->cudd, shifted_a_i);
      Cudd_IterDerefBdd(cudd->cudd, else_case);
    }

    bdds_clear(cudd, shift_const, n);
    bdds_clear(cudd, &b_eq_shift_const, 1);
  }

  bdds_remove_reserve(cudd, n);
}

void bdds_mk_lshr(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n) {
  BDD** shift_const = bdds_allocate_reserve(cudd, n);
  BDD* b_eq_shift_const = NULL;

  bdds_mk_zero(cudd, out, n);

  for (uint32_t shift = 0; shift < n; ++ shift) {

    bdds_mk_constant_64(cudd, shift_const, n, shift);
    bdds_mk_eq(cudd, &b_eq_shift_const, b, shift_const, n);

    for (uint32_t i = 0; i < n; ++ i) {
      BDD* shifted_a_i = i + shift >= n ? Cudd_ReadLogicZero(cudd->cudd) : a[i+shift];
      Cudd_Ref(shifted_a_i);

      BDD* else_case = out[i];
      out[i]  = Cudd_bddIte(cudd->cudd, b_eq_shift_const, shifted_a_i, else_case);
      Cudd_Ref(out[i]);

      Cudd_IterDerefBdd(cudd->cudd, shifted_a_i);
      Cudd_IterDerefBdd(cudd->cudd, else_case);
    }

    bdds_clear(cudd, shift_const, n);
    bdds_clear(cudd, &b_eq_shift_const, 1);
  }

  bdds_remove_reserve(cudd, n);
}

void bdds_mk_ashr(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n) {
  BDD** shift_const = bdds_allocate_reserve(cudd, n);
  BDD* b_eq_shift_const = NULL;

  bdds_mk_zero(cudd, out, n);

  for (uint32_t shift = 0; shift < n; ++ shift) {

    bdds_mk_constant_64(cudd, shift_const, n, shift);
    bdds_mk_eq(cudd, &b_eq_shift_const, b, shift_const, n);

    for (uint32_t i = 0; i < n; ++ i) {
      BDD* shifted_a_i = i + shift >= n ? a[n-1] : a[i+shift];
      Cudd_Ref(shifted_a_i);

      BDD* else_case = out[i];
      out[i]  = Cudd_bddIte(cudd->cudd, b_eq_shift_const, shifted_a_i, else_case);
      Cudd_Ref(out[i]);

      Cudd_IterDerefBdd(cudd->cudd, shifted_a_i);
      Cudd_IterDerefBdd(cudd->cudd, else_case);
    }

    bdds_clear(cudd, shift_const, n);
    bdds_clear(cudd, &b_eq_shift_const, 1);
  }

  bdds_remove_reserve(cudd, n);
}

void bdds_mk_bool_or(CUDD* cudd, BDD** out, const pvector_t* children_bdds) {
  uint32_t n = children_bdds->size;
  out[0] = Cudd_ReadLogicZero(cudd->cudd);
  Cudd_Ref(out[0]);
  for (uint32_t i = 0; i < n; i ++ ) {
    BDD* tmp = out[0];
    BDD** child_i = (BDD**) children_bdds->data[i];
    out[0] = Cudd_bddOr(cudd->cudd, tmp, child_i[0]);
    Cudd_Ref(out[0]);
    Cudd_IterDerefBdd(cudd->cudd, tmp);
  }
}

void bdds_mk_eq(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n) {
  assert(n > 0);
  assert(out[0] == NULL);
  out[0] = Cudd_Xeqy(cudd->cudd, n, a, b);
  Cudd_Ref(out[0]);
}

void bdds_mk_eq0(CUDD* cudd, BDD** out, BDD** a, uint32_t n) {
  assert(n > 0);
  assert(out[0] == NULL);
  BDD* result = Cudd_ReadLogicZero(cudd->cudd);
  Cudd_Ref(result);
  for (uint32_t i = 0; i < n; ++ i) {
    BDD* new_result = Cudd_bddAnd(cudd->cudd, result, Cudd_Not(a[i]));
    Cudd_Ref(new_result);
    Cudd_IterDerefBdd(cudd->cudd, result);
    result = new_result;
  }
  out[0] = result;
}

/** out += cond*a << shift (out must be allocated) */
void bdds_mk_plus_in_place(CUDD* cudd, BDD** out, BDD** a, BDD* cond, uint32_t n, uint32_t shift) {

  BDD* carry = Cudd_ReadLogicZero(cudd->cudd);
  Cudd_Ref(carry);

  for (uint32_t i = shift, j = 0; i < n; ++ i, ++ j) {
    // What we are adding (with condition if there)
    BDD* to_add = cond == NULL ? a[j] : Cudd_bddAnd(cudd->cudd, cond, a[j]);
    Cudd_Ref(to_add);
    // Sum up the bits
    BDD* sum1 = Cudd_bddXor(cudd->cudd, out[i], to_add);
    Cudd_Ref(sum1);
    BDD* sum2 = Cudd_bddXor(cudd->cudd, sum1, carry);
    Cudd_Ref(sum2);
    // Compute carry
    BDD* carry1 = Cudd_bddAnd(cudd->cudd, out[i], to_add);
    Cudd_Ref(carry1);
    BDD* carry2 = Cudd_bddAnd(cudd->cudd, sum1, carry);
    Cudd_Ref(carry2);
    Cudd_IterDerefBdd(cudd->cudd, carry);
    carry = Cudd_bddOr(cudd->cudd, carry1, carry2);
    Cudd_Ref(carry);
    // Save to output
    Cudd_IterDerefBdd(cudd->cudd, out[i]);
    out[i] = sum2; // Don't deref sum2, it's in out now
    // Remove temps
    Cudd_IterDerefBdd(cudd->cudd, to_add);
    Cudd_IterDerefBdd(cudd->cudd, sum1);
    Cudd_IterDerefBdd(cudd->cudd, carry1);
    Cudd_IterDerefBdd(cudd->cudd, carry2);
  }

  Cudd_IterDerefBdd(cudd->cudd, carry);
}

void bdds_mk_plus(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n) {
  bdds_copy(out, a, n);
  bdds_mk_plus_in_place(cudd, out, b, NULL, n, 0);
}

/** Multiplication with repeated addition (we index over bits of b) */
void bdds_mk_mult(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n) {
  bdds_mk_zero(cudd, out, n);
  for(uint32_t k = 0; k < n; ++ k) {
    bdds_mk_plus_in_place(cudd, out, a, b[k], n, k);
  }
}

void bdds_mk_div_rem(CUDD* cudd, BDD** out_div, BDD** out_rem, BDD** a, BDD** b, uint32_t n) {

  uint32_t tmp_size = 3*n;
  BDD** tmp = bdds_allocate_reserve(cudd, tmp_size);

  BDD** a_extended = tmp; // 2n bits
  BDD** a_sub_b = tmp + 2*n; // n bits

  BDD* zero = Cudd_ReadLogicZero(cudd->cudd); Cudd_Ref(zero);
  BDD* one = Cudd_ReadOne(cudd->cudd); Cudd_Ref(one);

  // a_extended = [0..00]@a
  bdds_copy(a_extended, a, n);
  bdds_mk_zero(cudd, a_extended + n, n);

  for (uint32_t i = 1; i <= n; ++ i) {
    // current slice of a we are working on
    BDD** a_slice = a_extended + n - i;
    // compare slice to b
    BDD* a_slice_ge_b = NULL;
    bdds_mk_ge(cudd, &a_slice_ge_b, a_slice, b, n);
    // compute a_slice - b
    bdds_mk_2s_complement(cudd, a_sub_b, b, n);
    bdds_mk_plus_in_place(cudd, a_sub_b, a_slice, NULL, n, 0);
    // record division bit
    if (out_div != NULL) {
      assert(out_div[n-i] == NULL);
      out_div[n-i] = Cudd_bddIte(cudd->cudd, a_slice_ge_b, one, zero);
      Cudd_Ref(out_div[n-i]);
    }
    // update slice
    for (uint32_t k = 0; k < n; ++ k) {
      BDD* tmp = a_slice[k];
      a_slice[k] = Cudd_bddIte(cudd->cudd, a_slice_ge_b, a_sub_b[k], a_slice[k]);
      Cudd_Ref(a_slice[k]);
      Cudd_IterDerefBdd(cudd->cudd, tmp);
    }
    // remove temp
    Cudd_IterDerefBdd(cudd->cudd, a_slice_ge_b);
    bdds_clear(cudd, a_sub_b, n);
  }

  if (out_rem != NULL) {
    bdds_move(out_rem, a_extended, n);
    bdds_clear(cudd, a_extended + n, n);
  } else {
    bdds_clear(cudd, a_extended, 2*n);
  }

  bdds_remove_reserve(cudd, tmp_size);

  Cudd_IterDerefBdd(cudd->cudd, zero);
  Cudd_IterDerefBdd(cudd->cudd, one);
}

void bdds_mk_div(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n) {
  bdds_mk_div_rem(cudd, out, NULL, a, b, n);
}

void bdds_mk_rem(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n) {
  bdds_mk_div_rem(cudd, NULL, out, a, b, n);
}

void bdds_mk_ite(CUDD* cudd, BDD** out, BDD* cond, BDD** a, BDD** b, uint32_t n) {
  for (uint32_t i = 0; i < n; ++ i) {
    assert(out[i] == NULL);
    out[i] = Cudd_bddIte(cudd->cudd, cond, a[i], b[i]);
    Cudd_Ref(out[i]);
  }
}

//    (bvsdiv s t) abbreviates
//      (let ((?msb_s ((_ extract |m-1| |m-1|) s))
//            (?msb_t ((_ extract |m-1| |m-1|) t)))
//        (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
//             (bvudiv s t)
//        (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
//             (bvneg (bvudiv (bvneg s) t))
//        (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
//             (bvneg (bvudiv s (bvneg t)))
//             (bvudiv (bvneg s) (bvneg t))))))
void bdds_mk_sdiv(CUDD* cudd, BDD** out_bdds, BDD** a, BDD** b, uint32_t n) {
  assert(n > 0);

  BDD* msb_a = a[n-1];
  BDD* msb_b = b[n-1];

  uint32_t tmp_size = 10*n;
  BDD** tmp = bdds_allocate_reserve(cudd, tmp_size);

  BDD** case00_result = tmp; // n bits
  BDD** bvneg_a = tmp + n; // n bits
  BDD** bvdiv_bvneg_a_b = tmp + 2*n; // n bits
  BDD** case10_result = tmp + 3*n; // n bits
  BDD** bvneg_b = tmp + 4*n; // n bits
  BDD** bvdiv_a_bvneg_b = tmp + 5*n; // nbits
  BDD** case01_result = tmp + 6*n; // n bits
  BDD** case11_result = tmp + 7*n; // n bits
  BDD** ite1 = tmp + 8*n; // n bits
  BDD** ite2 = tmp + 9*n; // n bits

  // Case msb_a = 0, msb_b = 0
  BDD* case00 = Cudd_bddAnd(cudd->cudd, Cudd_Not(msb_a), Cudd_Not(msb_b));
  Cudd_Ref(case00);
  bdds_mk_div(cudd, case00_result, a, b, n);

  // Case msb_a = 1, msb_b = 0
  BDD* case10 = Cudd_bddAnd(cudd->cudd, msb_a, Cudd_Not(msb_b));
  Cudd_Ref(case10);
  bdds_mk_2s_complement(cudd, bvneg_a, a, n);
  bdds_mk_div(cudd, bvdiv_bvneg_a_b, bvneg_a, b, n);
  bdds_mk_2s_complement(cudd, case10_result, bvdiv_bvneg_a_b, n);

  // Case msb_a = 0, msb_b = 1
  BDD* case01 = Cudd_bddAnd(cudd->cudd, Cudd_Not(msb_a), msb_b);
  Cudd_Ref(case01);
  bdds_mk_2s_complement(cudd, bvneg_b, b, n);
  bdds_mk_div(cudd, bvdiv_a_bvneg_b, a, bvneg_b, n);
  bdds_mk_2s_complement(cudd, case01_result, bvdiv_a_bvneg_b, n);

  // Case msb_a = 1, msb_b = 1
  bdds_mk_div(cudd, case11_result, bvneg_a, bvneg_b, n);

  // Final ITE result
  bdds_mk_ite(cudd, ite1, case01, case01_result, case11_result, n);
  bdds_mk_ite(cudd, ite2, case10, case10_result, ite1, n);
  bdds_mk_ite(cudd, out_bdds, case00, case00_result, ite2, n);

  // Clear temps
  Cudd_IterDerefBdd(cudd->cudd, case00);
  Cudd_IterDerefBdd(cudd->cudd, case10);
  Cudd_IterDerefBdd(cudd->cudd, case01);
  bdds_clear(cudd, tmp, tmp_size);
  bdds_remove_reserve(cudd, tmp_size);
}

//   (bvsrem s t) abbreviates
//     (let ((?msb_s ((_ extract |m-1| |m-1|) s))
//           (?msb_t ((_ extract |m-1| |m-1|) t)))
//       (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
//            (bvurem s t)
//       (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
//            (bvneg (bvurem (bvneg s) t))
//       (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
//            (bvurem s (bvneg t)))
//            (bvneg (bvurem (bvneg s) (bvneg t))))))
void bdds_mk_srem(CUDD* cudd, BDD** out_bdds, BDD** a, BDD** b, uint32_t n) {
  assert(n > 0);

  BDD* msb_a = a[n-1];
  BDD* msb_b = b[n-1];

  uint32_t tmp_size = 10*n;
  BDD** tmp = bdds_allocate_reserve(cudd, tmp_size);

  BDD** case00_result = tmp; // n bits
  BDD** bvneg_a = tmp + n; // n bits
  BDD** bvrem_bvneg_a_b = tmp + 2*n; // n bits
  BDD** case10_result = tmp + 3*n; // n bits
  BDD** bvneg_b = tmp + 4*n; // n bits
  BDD** case01_result = tmp + 5*n; // n bits
  BDD** bvrem_bvneg_a_bvneg_b = tmp + 6*n; // nbits
  BDD** case11_result = tmp + 7*n; // n bits
  BDD** ite1 = tmp + 8*n; // n bits
  BDD** ite2 = tmp + 9*n; // n bits

  // Case msb_a = 0, msb_b = 0 -> (bvurem s t)
  BDD* case00 = Cudd_bddAnd(cudd->cudd, Cudd_Not(msb_a), Cudd_Not(msb_b));
  Cudd_Ref(case00);
  bdds_mk_rem(cudd, case00_result, a, b, n);

  // Case msb_a = 1, msb_b = 0 -> (bvneg (bvurem (bvneg s) t))
  BDD* case10 = Cudd_bddAnd(cudd->cudd, msb_a, Cudd_Not(msb_b));
  Cudd_Ref(case10);
  bdds_mk_2s_complement(cudd, bvneg_a, a, n);
  bdds_mk_rem(cudd, bvrem_bvneg_a_b, bvneg_a, b, n);
  bdds_mk_2s_complement(cudd, case10_result, bvrem_bvneg_a_b, n);

  // Case msb_a = 0, msb_b = 1 -> (bvurem s (bvneg t)))
  BDD* case01 = Cudd_bddAnd(cudd->cudd, Cudd_Not(msb_a), msb_b);
  Cudd_Ref(case01);
  bdds_mk_2s_complement(cudd, bvneg_b, b, n);
  bdds_mk_rem(cudd, case01_result, a, bvneg_b, n);

  // Case msb_a = 1, msb_b = 1 -> (bvneg (bvurem (bvneg s) (bvneg t)))
  bdds_mk_rem(cudd, bvrem_bvneg_a_bvneg_b, bvneg_a, bvneg_b, n);
  bdds_mk_2s_complement(cudd, case11_result, bvrem_bvneg_a_bvneg_b, n);

  // Final ITE result
  bdds_mk_ite(cudd, ite1, case01, case01_result, case11_result, n);
  bdds_mk_ite(cudd, ite2, case10, case10_result, ite1, n);
  bdds_mk_ite(cudd, out_bdds, case00, case00_result, ite2, n);

  // Clear temps
  Cudd_IterDerefBdd(cudd->cudd, case00);
  Cudd_IterDerefBdd(cudd->cudd, case10);
  Cudd_IterDerefBdd(cudd->cudd, case01);
  bdds_clear(cudd, tmp, tmp_size);
  bdds_remove_reserve(cudd, tmp_size);
}

//    (bvsmod s t) abbreviates
//      (let ((?msb_s ((_ extract |m-1| |m-1|) s))
//            (?msb_t ((_ extract |m-1| |m-1|) t)))
//        (let ((abs_s (ite (= ?msb_s #b0) s (bvneg s)))
//              (abs_t (ite (= ?msb_t #b0) t (bvneg t))))
//          (let ((u (bvurem abs_s abs_t)))
//            (ite (= u (_ bv0 m))
//                 u
//            (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
//                 u
//            (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
//                 (bvadd (bvneg u) t)
//            (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
//                 (bvadd u t)
//                 (bvneg u))))))))
void bdds_mk_smod(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n) {
  assert(n > 0);

  BDD* msb_a = a[n-1];
  BDD* msb_b = b[n-1];

  uint32_t tmp_size = 11*n;
  BDD** tmp = bdds_allocate_reserve(cudd, tmp_size);

  // Temporary storage
  BDD** bvneg_a = tmp;
  BDD** bvneg_b = tmp + n;
  BDD** abs_a = tmp + 2*n;
  BDD** abs_b = tmp + 3*n;
  BDD** u = tmp + 4*n;
  BDD** bvadd_u_b = tmp + 5*n;
  BDD** bvneg_u = tmp + 6*n;
  BDD** bvadd_bvneg_u_b = tmp + 7*n;
  BDD** ite2 = tmp + 8*n;
  BDD** ite3 = tmp + 9*n;
  BDD** ite4 = tmp + 10*n;

  // All the intermediary terms
  bdds_mk_2s_complement(cudd, bvneg_a, a, n);
  bdds_mk_2s_complement(cudd, bvneg_b, b, n);
  bdds_mk_ite(cudd, abs_a, msb_a, bvneg_a, a, n);
  bdds_mk_ite(cudd, abs_b, msb_b, bvneg_b, b, n);
  bdds_mk_rem(cudd, u, abs_a, abs_b, n);
  bdds_mk_plus(cudd, bvadd_u_b, u, b, n);
  bdds_mk_2s_complement(cudd, bvneg_u, u, n);
  bdds_mk_plus(cudd, bvadd_bvneg_u_b, bvneg_u, b, n);

  // ITE conditions
  BDD* cond1 = NULL;
  bdds_mk_eq0(cudd, &cond1, u, n);
  BDD* cond2 = Cudd_bddAnd(cudd->cudd, Cudd_Not(msb_a), Cudd_Not(msb_b));
  Cudd_Ref(cond2);
  BDD* cond3 = Cudd_bddAnd(cudd->cudd, msb_a, Cudd_Not(msb_b));
  Cudd_Ref(cond3);
  BDD* cond4 = Cudd_bddAnd(cudd->cudd, Cudd_Not(msb_a), msb_b);
  Cudd_Ref(cond4);

  // (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
  //   (bvadd u t) (bvneg u))
  bdds_mk_ite(cudd, ite4, cond4, bvadd_u_b, bvneg_u, n);
  // (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
  //  (bvadd (bvneg u) t) ite4)
  bdds_mk_ite(cudd, ite3, cond3, bvadd_bvneg_u_b, ite4, n);
  // (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
  //   u ite3)
  bdds_mk_ite(cudd, ite2, cond2, u, ite3, n);
  // (ite (= u (_ bv0 m)) u ite2)
  bdds_mk_ite(cudd, out, cond1, u, ite2, n);

  // Clear temps
  Cudd_IterDerefBdd(cudd->cudd, cond1);
  Cudd_IterDerefBdd(cudd->cudd, cond2);
  Cudd_IterDerefBdd(cudd->cudd, cond3);
  Cudd_IterDerefBdd(cudd->cudd, cond4);
  bdds_clear(cudd, tmp, tmp_size);
  bdds_remove_reserve(cudd, tmp_size);
}

void bdds_compute_bdds(CUDD* cudd, term_table_t* terms, term_t t,
    const pvector_t* children_bdds, BDD** out_bdds) {

  assert(bv_term_has_children(terms, t));

  BDD** t0;
  BDD** t1;

  uint32_t t_bitsize = bv_term_bitsize(terms, t);

  if (is_neg_term(t)) {
    // Negation
    assert(children_bdds->size == 1);
    t0 = (BDD**) children_bdds->data[0];
    bdds_mk_not(cudd, out_bdds, t0, t_bitsize);
  } else {
    term_kind_t kind = term_kind(terms, t);
    switch (kind) {
    case BV_DIV:
      assert(children_bdds->size == 2);
      t0 = (BDD**) children_bdds->data[0];
      t1 = (BDD**) children_bdds->data[1];
      bdds_mk_div(cudd, out_bdds, t0, t1, t_bitsize);
      break;
    case BV_REM:
      assert(children_bdds->size == 2);
      t0 = (BDD**) children_bdds->data[0];
      t1 = (BDD**) children_bdds->data[1];
      bdds_mk_rem(cudd, out_bdds, t0, t1, t_bitsize);
      break;
    case BV_SDIV:
      assert(children_bdds->size == 2);
      t0 = (BDD**) children_bdds->data[0];
      t1 = (BDD**) children_bdds->data[1];
      bdds_mk_sdiv(cudd, out_bdds, t0, t1, t_bitsize);
      break;
    case BV_SREM:
      assert(children_bdds->size == 2);
      t0 = (BDD**) children_bdds->data[0];
      t1 = (BDD**) children_bdds->data[1];
      bdds_mk_srem(cudd, out_bdds, t0, t1, t_bitsize);
      break;
    case BV_SMOD:
      assert(children_bdds->size == 2);
      t0 = (BDD**) children_bdds->data[0];
      t1 = (BDD**) children_bdds->data[1];
      bdds_mk_smod(cudd, out_bdds, t0, t1, t_bitsize);
      break;
    case BV_SHL:
      assert(children_bdds->size == 2);
      t0 = (BDD**) children_bdds->data[0];
      t1 = (BDD**) children_bdds->data[1];
      bdds_mk_shl(cudd, out_bdds, t0, t1, t_bitsize);
      break;
    case BV_LSHR:
      assert(children_bdds->size == 2);
      t0 = (BDD**) children_bdds->data[0];
      t1 = (BDD**) children_bdds->data[1];
      bdds_mk_lshr(cudd, out_bdds, t0, t1, t_bitsize);
      break;
    case BV_ASHR:
      assert(children_bdds->size == 2);
      t0 = (BDD**) children_bdds->data[0];
      t1 = (BDD**) children_bdds->data[1];
      bdds_mk_ashr(cudd, out_bdds, t0, t1, t_bitsize);
      break;
    case BV_ARRAY: {
      assert(children_bdds->size == t_bitsize);
      for (uint32_t i = 0; i < children_bdds->size; ++ i) {
        assert(out_bdds[i] == NULL);
        out_bdds[i] = ((BDD**) children_bdds->data[i])[0];
        Cudd_Ref(out_bdds[i]);
      }
      break;
    }
    case BIT_TERM: {
      assert(t_bitsize == 1);
      assert(children_bdds->size == 1);
      select_term_t* desc = bit_term_desc(terms, t);
      uint32_t select_idx = desc->idx;
      BDD** child_bdds = ((BDD**)children_bdds->data[0]);
      BDD* bit_bdd = child_bdds[select_idx];
      assert(out_bdds[0] == NULL);
      out_bdds[0] = bit_bdd;
      Cudd_Ref(out_bdds[0]);
      break;
    }
    case BV_POLY: {
      uint32_t tmp_size = 2*t_bitsize;
      BDD** tmp = bdds_allocate_reserve(cudd, tmp_size);
      BDD** const_bdds = tmp;
      BDD** mult_bdds = tmp + t_bitsize;
      bdds_mk_zero(cudd, out_bdds, t_bitsize);
      bvpoly_t* p = bvpoly_term_desc(terms, t);
      for (uint32_t i = 0, child_i = 0; i < p->nterms; ++ i) {
        uint32_t* c = p->mono[i].coeff;
        bdds_mk_constant_raw(cudd, const_bdds, t_bitsize, c);
        if (p->mono[i].var == const_idx) {
          // Just constant: out += c
          bdds_mk_plus_in_place(cudd, out_bdds, const_bdds, NULL, t_bitsize, 0);
          bdds_clear(cudd, const_bdds, t_bitsize);
          continue;
        } else {
          // Non constant: out += c*x
          BDD** child_bdds = ((BDD**)children_bdds->data[child_i]);
          bdds_mk_mult(cudd, mult_bdds, child_bdds, const_bdds, t_bitsize);
          bdds_mk_plus_in_place(cudd, out_bdds, mult_bdds, NULL, t_bitsize, 0);
          bdds_clear(cudd, const_bdds, t_bitsize);
          bdds_clear(cudd, mult_bdds, t_bitsize);
          ++ child_i;
        }
      }
      bdds_remove_reserve(cudd, tmp_size);
      break;
    }
    case BV64_POLY: {
      uint32_t tmp_size = 2*t_bitsize;
      BDD** tmp = bdds_allocate_reserve(cudd, tmp_size);
      BDD** const_bdds = tmp;
      BDD** mult_bdds = tmp + t_bitsize;
      bdds_mk_zero(cudd, out_bdds, t_bitsize);
      bvpoly64_t* p = bvpoly64_term_desc(terms, t);
      for (uint32_t i = 0, child_i = 0; i < p->nterms; ++ i) {
        uint64_t c = p->mono[i].coeff;
        bdds_mk_constant_64(cudd, const_bdds, t_bitsize, c);
        if (p->mono[i].var == const_idx) {
          // Just constant: out += c
          bdds_mk_plus_in_place(cudd, out_bdds, const_bdds, NULL, t_bitsize, 0);
          bdds_clear(cudd, const_bdds, t_bitsize);
          continue;
        } else {
          // Non constant: out += c*x
          BDD** child_bdds = ((BDD**)children_bdds->data[child_i]);
          bdds_mk_mult(cudd, mult_bdds, child_bdds, const_bdds, t_bitsize);
          bdds_mk_plus_in_place(cudd, out_bdds, mult_bdds, NULL, t_bitsize, 0);
          bdds_clear(cudd, const_bdds, t_bitsize);
          bdds_clear(cudd, mult_bdds, t_bitsize);
          ++ child_i;
        }
      }
      bdds_remove_reserve(cudd, tmp_size);
      break;
    }
    case POWER_PRODUCT: {
      BDD** mult_bdds = bdds_allocate_reserve(cudd, t_bitsize);
      bdds_mk_one(cudd, out_bdds, t_bitsize);
      pprod_t* t_pprod = pprod_term_desc(terms, t);
      for (uint32_t i = 0; i < t_pprod->len; ++ i) {
        uint32_t exp = t_pprod->prod[i].exp;
        BDD** child_bdds = ((BDD**)children_bdds->data[i]);
        for (uint32_t d = 0; d < exp; ++ d) {
          bdds_mk_mult(cudd, mult_bdds, out_bdds, child_bdds, t_bitsize);
          bdds_swap(mult_bdds, out_bdds, t_bitsize);
          bdds_clear(cudd, mult_bdds, t_bitsize);
        }
      }
      bdds_remove_reserve(cudd, t_bitsize);
      break;
    }
    case OR_TERM: {
      composite_term_t* t_comp = or_term_desc(terms, t);
      assert(children_bdds->size == t_comp->arity);
      bdds_mk_bool_or(cudd, out_bdds, children_bdds);
      break;
    }
    case EQ_TERM: // Boolean equality
    case BV_EQ_ATOM: {
      assert(children_bdds->size == 2);
      composite_term_t* comp = composite_term_desc(terms, t);
      term_t child = comp->arg[0];
      uint32_t child_bitsize = bv_term_bitsize(terms, child);
      t0 = (BDD**) children_bdds->data[0];
      t1 = (BDD**) children_bdds->data[1];
      bdds_mk_eq(cudd, out_bdds, t0, t1, child_bitsize);
      break;
    }
    case BV_GE_ATOM: {
      assert(children_bdds->size == 2);
      composite_term_t* comp = composite_term_desc(terms, t);
      term_t child = comp->arg[0];
      uint32_t child_bitsize = bv_term_bitsize(terms, child);
      t0 = (BDD**) children_bdds->data[0];
      t1 = (BDD**) children_bdds->data[1];
      bdds_mk_ge(cudd, out_bdds, t0, t1, child_bitsize);
      break;
    }
    case BV_SGE_ATOM: {
      assert(children_bdds->size == 2);
      composite_term_t* comp = composite_term_desc(terms, t);
      term_t child = comp->arg[0];
      uint32_t child_bitsize = bv_term_bitsize(terms, child);
      t0 = (BDD**) children_bdds->data[0];
      t1 = (BDD**) children_bdds->data[1];
      bdds_mk_sge(cudd, out_bdds, t0, t1, child_bitsize);
      break;
    }
    default:
      // Not composite
      assert(false);
      break;
    }
  }
}

void bdds_mk_ge(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n) {
  assert(n > 0);
  assert(out[0] == NULL);
  // Reverse to satisfy CUDD
  bdds_reverse(a, n);
  bdds_reverse(b, n);
  // a < b
  out[0] = Cudd_Xgty(cudd->cudd, n, NULL, b, a);
  Cudd_Ref(out[0]);
  // a >= b
  out[0] = Cudd_Not(out[0]);
  // Undo reversal
  bdds_reverse(a, n);
  bdds_reverse(b, n);
}

void bdds_mk_sge(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n) {
  // signed comparison, just invert the first bits
  assert(n > 0);
  a[n-1] = Cudd_Not(a[n-1]);
  b[n-1] = Cudd_Not(b[n-1]);
  bdds_mk_ge(cudd, out, a, b, n);
  a[n-1] = Cudd_Not(a[n-1]);
  b[n-1] = Cudd_Not(b[n-1]);
}

bool bdds_is_point(CUDD* cudd, BDD* a, uint32_t size) {
  bool is_cube = Cudd_CheckCube(cudd->cudd, a);
  if (!is_cube) { return false; }
  int dag_size = Cudd_DagSize(a);
  if (dag_size != size + 1) { return false; }
  return true;
}

bool bdds_is_model(CUDD* cudd, BDD** x, BDD* C_x, const bvconstant_t* out) {
  for (uint32_t i = 0; i < out->bitsize; ++ i) {
    unsigned int x_i = Cudd_NodeReadIndex(x[i]);
    bool bit_i_true = bvconst_tst_bit(out->data, i);
    cudd->tmp_inputs[x_i] = bit_i_true ? 1 : 0;
  }
  return Cudd_Eval(cudd->cudd, C_x, cudd->tmp_inputs) == Cudd_ReadOne(cudd->cudd);
}

void bdds_get_model(CUDD* cudd, BDD** x, BDD* C_x, bvconstant_t* out) {
  Cudd_bddPickOneCube(cudd->cudd, C_x, cudd->tmp_model);
  // Set the ones in the cube
  for (uint32_t i = 0; i < out->bitsize; ++ i) {
    unsigned int x_i = Cudd_NodeReadIndex(x[i]);
    char x_i_value = cudd->tmp_model[x_i];
    if (x_i_value == 1) {
      bvconst_set_bit(out->data, i);
    } else {
      // We just take 0 as the default (if x_i_value == 2, we can choose anything)
      bvconst_clr_bit(out->data, i);
    }
  }
}

