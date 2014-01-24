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
