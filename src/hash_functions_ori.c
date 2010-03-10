/*
 * Variant (slower) implementation of the hash functions
 * we use. This is still needed by some of the test modules.
 */

#include <string.h>
#include "hash_functions_ori.h"


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
 * Hash of an array of integers.
 * Assumption: most integers are small (less than 16 bit)
 */
static uint32_t jenkins_hash_int_ori(uint32_t *k, uint32_t len, uint32_t initval) {
  uint32_t a, b, c, n;

  a = b = 0x9e3779b9;
  c = initval;
  n = len;

  while (n >= 6) {
    a += ((k[0] & 0xffff) + (k[1] << 16));
    b += ((k[2] & 0xffff) + (k[3] << 16));
    c += ((k[4] & 0xffff) + (k[5] << 16));
    mix(a, b, c);
    k += 6;
    n -= 6;
   }

  c += len;
  switch (n) {
  case 5: c += (k[5] << 16);
  case 4: b += (k[4] & 0xffff);
  case 3: b += (k[3] << 16);
  case 2: a += (k[1] & 0xffff);
  case 1: a += k[0];
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
 * Hash of an array of small integers
 */
uint32_t jenkins_hash_intarray_ori(int n, int32_t *d, uint32_t seed) {
  return jenkins_hash_int_ori((uint32_t *) d, n, seed);
}

