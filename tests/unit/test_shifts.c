/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>

int main() {
  uint32_t n;
  uint64_t aux, mask, neg;

  for (n=1; n<=64; n++) {
    aux = ((uint64_t) 1) << n;
    mask = ~((uint64_t) 0) >> (64 - n);
    neg = - mask;
    printf("n = %2"PRIu32", aux = %016"PRIx64" mask = %016"PRIx64", neg = %016"PRIx64"\n", n, aux, mask, neg);
  }

  return 0;
}
