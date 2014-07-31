/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Tests
 */

#include <stdio.h>
#include "utils/bitvectors.h"

static void display_bitvector(byte_t *bv, int32_t n) {
  int32_t i;

  for (i=0; i<n; i++) {
    printf("%d", tst_bit(bv, i));
  }
  printf("\n");
}

int main() {
  byte_t *bv;
  int32_t i;

  bv = allocate_bitvector(20);
  printf("initial 20bit bv (%p):\n", bv);
  display_bitvector(bv, 20);
  clear_bitvector(bv, 20);
  printf("all cleared:\n");
  display_bitvector(bv, 20);
  set_bit(bv, 5);
  set_bit(bv, 7);
  set_bit(bv, 8);
  printf("bits 5, 7, 8 set:\n");
  display_bitvector(bv, 20);

  bv = extend_bitvector(bv, 32);
  printf("extended to 32bits (%p):\n", bv);
  display_bitvector(bv, 32);
  for (i=20; i<32; i++) {
    set_bit(bv, i);
  }
  printf("setting bits 20 to 31:\n");
  display_bitvector(bv, 32);

  flip_bit(bv, 0);
  flip_bit(bv, 31);
  flip_bit(bv, 13);
  printf("flipping bits 0, 31, 13:\n");
  display_bitvector(bv, 32);

  clr_bit(bv, 10);
  clr_bit(bv, 0);
  clr_bit(bv, 13);
  printf("clearing bits 0, 10, 13:\n");
  display_bitvector(bv, 32);

  clear_bitvector(bv, 32);
  printf("clearing all bits:\n");
  display_bitvector(bv, 32);
  printf("\n");

  set_bitvector(bv, 32);
  printf("setting all bits:\n");
  display_bitvector(bv, 32);

  for (i=0; i<32; i += 3) {
    clr_bit(bv, i);
  }
  printf("cleared one in three bits:\n");
  display_bitvector(bv, 32);

  assign_bit(bv, 1, tst_bit(bv, 0));
  printf("copied bit[0] to bit[1]:\n");
  display_bitvector(bv, 32);

  assign_bit(bv, 5, tst_bit(bv, 4));
  printf("copied bit[4] to bit[5]:\n");
  display_bitvector(bv, 32);

  assign_bit(bv, 6, tst_bit(bv, 7));
  printf("copied bit[7] to bit[6]:\n");
  display_bitvector(bv, 32);

  assign_bit(bv, 30, tst_bit(bv, 27));
  printf("copied bit[27] to bit[30]:\n");
  display_bitvector(bv, 32);
  printf("\n");

  set_bitvector(bv, 32);
  printf("setting all bits:\n");
  display_bitvector(bv, 32);

  for (i=0; i<32; i += 3) {
    clr_bit(bv, i);
  }
  printf("cleared one in three bits:\n");
  display_bitvector(bv, 32);

  assign_bit_old(bv, 1, tst_bit(bv, 0));
  printf("copied bit[0] to bit[1]:\n");
  display_bitvector(bv, 32);

  assign_bit_old(bv, 5, tst_bit(bv, 4));
  printf("copied bit[4] to bit[5]:\n");
  display_bitvector(bv, 32);

  assign_bit_old(bv, 6, tst_bit(bv, 7));
  printf("copied bit[7] to bit[6]:\n");
  display_bitvector(bv, 32);

  assign_bit_old(bv, 30, tst_bit(bv, 27));
  printf("copied bit[27] to bit[30]:\n");
  display_bitvector(bv, 32);


  delete_bitvector(bv);


  printf("\n**** 0-initialized vectors ****\n");
  bv = allocate_bitvector0(19);
  printf("%p bv:\n", bv);
  display_bitvector(bv, 19);
  set_bit(bv, 1);
  set_bit(bv, 6);
  set_bit(bv, 18);
  printf("bits 1, 6, 18 set:\n");
  display_bitvector(bv, 19);

  bv = extend_bitvector0(bv, 22, 19);
  printf("extended to 22 bits:\n");
  display_bitvector(bv, 22);
  set_bit(bv, 21);
  printf("bit 21 set:\n");
  display_bitvector(bv, 22);

  bv = extend_bitvector0(bv, 257, 22);
  printf("extended to 257 bits:\n");
  display_bitvector(bv, 257);

  delete_bitvector(bv);

  return 0;
}
