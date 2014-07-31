/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <inttypes.h>

#include "utils/int_powers.h"

int main(void) {
  uint32_t d;

  // powers of 0
  for (d=0; d<16; d++) {
    printf("pow32(0, %"PRIu32") = %"PRIu32"\n", d, upower32(0, d));
    printf("pow64(0, %"PRIu32") = %"PRIu64"\n", d, upower64(0, d));
  }

  // powers of 1
  for (d=0; d<16; d++) {
    printf("pow32(1, %"PRIu32") = %"PRIu32"\n", d, upower32(1, d));
    printf("pow64(1, %"PRIu32") = %"PRIu64"\n", d, upower64(1, d));
  }

  // powers of 2
  for (d=0; d<80; d++) {
    printf("pow32(2, %"PRIu32") = %"PRIu32"\n", d, upower32(2, d));
    printf("pow64(2, %"PRIu32") = %"PRIu64"\n", d, upower64(2, d));
  }

  return 0;
}
