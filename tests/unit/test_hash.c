/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <inttypes.h>

#include "utils/cputime.h"
#include "utils/hash_functions.h"


#define N 2048
#define MASK (N - 1)

static char *test[] = {
  "abchbj",
  "hjnd2qb367",
  "x10", "x11", "x12", "x13", "x14",
  "x15", "x16", "x17", "x18", "x19",
  "alpha", "beta", "gamma", "delta", "epsilon", "eta", "phi", "iota",
  "kappa", "psi", "mu", "nu", "omega", "omicron", "theta",
  "January", "February", "March", "April", "May", "June", "July",
  "August", "September", "October", "November", "December",
  "Janvier", "Fevrier", "Mars", "Avril", "May", "Juin", "Juillet",
  "Aout", "Septembre", "Octobre", "Novembre", "Decembre",
  "monday-1", "tuesday-2", "wednesday-3", "thursday-4", "friday-5",
  "saturday-6", "sunday-7",
};


/*
 * Simple hash for strings
 */
static uint32_t hash_string(char *s) {
  uint32_t h, x;

  h = 0;
  x = *s;
  while (x != 0) {
    h = 31 * h + x;
    s ++;
    x = *s;
  }

  return h;
}


/*
 * Original jenkins's hash functions (lookup2)
 */

/* Jenkins's lookup2.c code */
#define mix(a, b, c)                \
{                                   \
  a -= b; a -= c; a ^= (c>>13);     \
  b -= c; b -= a; b ^= (a<<8);      \
  c -= a; c -= b; c ^= (b>>13);     \
  a -= b; a -= c; a ^= (c>>12);     \
  b -= c; b -= a; b ^= (a<<16);     \
  c -= a; c -= b; c ^= (b>>5);      \
  a -= b; a -= c; a ^= (c>>3);      \
  b -= c; b -= a; b ^= (a<<10);     \
  c -= a; c -= b; c ^= (b>>15);     \
}


/*
 * Original Jenkins hash function
 */
static uint32_t jenkins_hash_byte_ori(char *k, uint32_t len, uint32_t initval) {
  uint32_t a, b, c, n;

  a = b = 0x9e3779b9;
  c = initval;
  n = len;

  while (n >= 12) {
    a += (k[0] +((uint32_t)k[1]<<8) +((uint32_t)k[2]<<16) +((uint32_t)k[3]<<24));
    b += (k[4] +((uint32_t)k[5]<<8) +((uint32_t)k[6]<<16) +((uint32_t)k[7]<<24));
    c += (k[8] +((uint32_t)k[9]<<8) +((uint32_t)k[10]<<16)+((uint32_t)k[11]<<24));
    mix(a, b, c);
    k += 12;
    n -= 12;
   }

  c += len;
  switch (n) {
  case 11: c+=((uint32_t)k[10]<<24);
  case 10: c+=((uint32_t)k[9]<<16);
  case 9 : c+=((uint32_t)k[8]<<8);
    /* the first byte of c is reserved for the length */
  case 8 : b+=((uint32_t)k[7]<<24);
  case 7 : b+=((uint32_t)k[6]<<16);
  case 6 : b+=((uint32_t)k[5]<<8);
  case 5 : b+=k[4];
  case 4 : a+=((uint32_t)k[3]<<24);
  case 3 : a+=((uint32_t)k[2]<<16);
  case 2 : a+=((uint32_t)k[1]<<8);
  case 1 : a+=k[0];
    /* case 0: nothing left to add */
  }
  mix(a, b, c);

  return c;
}



/*
 * Hash of a character string.
 */
uint32_t jenkins_hash_string_ori(char *s, uint32_t seed) {
  uint32_t n;
  n = strlen(s);
  return jenkins_hash_byte_ori(s, n, seed);
}


/*
 * Hack: we print the value of h to stop a GCC warning (variable h set
 * but not used).
 */
int main(void) {
  int i, n;
  uint32_t h;
  double runtime;

  runtime = get_cpu_time();
  for (n=0; n<1000000; n++) {
    for (i=0; i<58; i++) {
      h = hash_string(test[i]) & MASK;
    }
  }
  runtime = get_cpu_time() - runtime;
  printf("naive hash:   %u calls\n", 10000000 * 58);
  printf("cpu time:     %.4f s\n", runtime);
  printf("last code:    %"PRIu32"\n", h);

  runtime = get_cpu_time();
  for (n=0; n<1000000; n++) {
    for (i=0; i<58; i++) {
      h = jenkins_hash_string_ori(test[i], 0x17838abc) & MASK;
    }
  }
  runtime = get_cpu_time() - runtime;
  printf("jenkins hash:  %u calls\n", 10000000 * 58);
  printf("cpu time:      %.4f s\n", runtime);
  printf("last code:    %"PRIu32"\n", h);

  runtime = get_cpu_time();
  for (n=0; n<1000000; n++) {
    for (i=0; i<58; i++) {
      h = jenkins_hash_byte_var((uint8_t*) test[i], 0x17838abc) & MASK;
    }
  }
  runtime = get_cpu_time() - runtime;
  printf("jenkins hash2: %u calls\n", 10000000 * 58);
  printf("cpu time:      %.4f s\n", runtime);
  printf("last code:    %"PRIu32"\n", h);

  return 0;
}
