/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <string.h>
#include "utils/hash_functions.h"

/*
 * The source for Jenkins's mix and hash functions is
 * http://www.burtleburtle.net/bob/hash/index.html
 *
 * The specific function below is lookup2.c (this is Public Domain)
 * http://www.burtleburtle.net/bob/c/lookup2.c
 *
 * int_hash_sets.c uses another hash function from Bob Jenkins's web
 * site.
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


/* Jenkins's lookup3 code */
#define rot(x,k) (((x)<<(k)) | ((x)>>(32-(k))))

#define mixx(a,b,c)                 \
{                                   \
  a -= c;  a ^= rot(c, 4);  c += b; \
  b -= a;  b ^= rot(a, 6);  a += c; \
  c -= b;  c ^= rot(b, 8);  b += a; \
  a -= c;  a ^= rot(c,16);  c += b; \
  b -= a;  b ^= rot(a,19);  a += c; \
  c -= b;  c ^= rot(b, 4);  b += a; \
}

#define final(a,b,c)      \
{                         \
  c ^= b; c -= rot(b,14); \
  a ^= c; a -= rot(c,11); \
  b ^= a; b -= rot(a,25); \
  c ^= b; c -= rot(b,16); \
  a ^= c; a -= rot(c,4);  \
  b ^= a; b -= rot(a,14); \
  c ^= b; c -= rot(b,24); \
}



/*
 * Variant of Jenkins's original lookup2 hash function
 * for null-terminated strings.
 */
uint32_t jenkins_hash_byte_var(const uint8_t *s, uint32_t seed) {
  uint32_t a, b, c, x;

  a = b = 0x9e3779b9;
  c = seed;

  for (;;) {
    x = *s ++;
    if (x == 0) return c;
    a += x;
    a <<= 8;
    x = *s ++;
    if (x == 0) break;
    a += x;
    a <<= 8;
    x = *s ++;
    if (x == 0) break;
    a += x;
    a <<= 8;
    x = *s ++;
    if (x == 0) break;
    a += x;

    x = *s ++;
    if (x == 0) break;
    b += x;
    b <<= 8;
    x = *s ++;
    if (x == 0) break;
    b += x;
    b <<= 8;
    x = *s ++;
    if (x == 0) break;
    b += x;
    b <<= 8;
    x = *s ++;
    if (x == 0) break;
    b += x;

    x = *s ++;
    if (x == 0) break;
    c += x;
    c <<= 8;
    x = *s ++;
    if (x == 0) break;
    c += x;
    c <<= 8;
    x = *s ++;
    if (x == 0) break;
    c += x;
    c <<= 8;
    x = *s ++;
    if (x == 0) break;
    c += x;

    mix(a, b, c);
  }

  mix(a, b, c);

  return c;
}


/*
 * Hash code of an array of unsigned integers.
 * This is based on Jenkins's lookup3 code.
 */
uint32_t jenkins_hash_array(const uint32_t *d, uint32_t n, uint32_t seed) {
  uint32_t a, b, c;

  a = b = c = 0xdeadbeef + n + seed;
  while (n > 3) {
    a += d[0];
    b += d[1];
    c += d[2];
    mixx(a, b, c);
    d += 3;
    n -= 3;
  }

  // last block of 1, 2, or 3 integers
  switch (n) {
  case 3: c += d[2];
  case 2: b += d[1];
  case 1: a += d[0];
    final(a, b, c);
    break;

  default:
    // empty array: return the seed
    c = seed;
    break;
  }

  return c;
}


/*
 * Hash a pair of integers with the given seed
 */
uint32_t jenkins_hash_pair(uint32_t a, uint32_t b, uint32_t seed) {
  uint32_t x, y;

  x = 0x9e3779b9 + a;
  y = 0x9e3779b9 + b;
  final(x, y, seed);

  return seed;
}


/*
 * Triple
 */
uint32_t jenkins_hash_triple(uint32_t a, uint32_t b, uint32_t c, uint32_t seed) {
  uint32_t x, y;

  x = 0x9e3779b9 + a;
  y = 0x9e3779b9 + b;
  mixx(x, y, seed);
  x += c;
  final(x, y, seed);

  return seed;
}


/*
 * Quadruple
 */
uint32_t jenkins_hash_quad(uint32_t a, uint32_t b, uint32_t c, uint32_t d, uint32_t seed) {
  uint32_t x, y;

  x = 0x9e3779b9 + a;
  y = 0x9e3779b9 + b;
  mixx(y, y, seed);
  x += c;
  y += d;
  final(x, y, seed);

  return seed;
}


/*
 * Mix of hash codes.
 */
uint32_t jenkins_hash_mix2(uint32_t x, uint32_t y) {
  uint32_t c;

  c = 0x17838abc;
  final(x, y, c);

  return c;
}

uint32_t jenkins_hash_mix3(uint32_t x, uint32_t y, uint32_t z) {
  final(x, y, z);

  return z;
}




/*
 * Hash code for a 32bit integer
 */
uint32_t jenkins_hash_uint32(uint32_t x) {
  x = (x + 0x7ed55d16) + (x<<12);
  x = (x ^ 0xc761c23c) ^ (x>>19);
  x = (x + 0x165667b1) + (x<<5);
  x = (x + 0xd3a2646c) ^ (x<<9);
  x = (x + 0xfd7046c5) + (x<<3);
  x = (x ^ 0xb55a4f09) ^ (x>>16);

  return x;
}


/*
 * Hash code for a 64bit integer
 */
uint32_t jenkins_hash_uint64(uint64_t x) {
  uint32_t a, b, c;

  a = (uint32_t) x; // low order bits
  b = (uint32_t) (x >> 32); // high order bits
  c = 0xdeadbeef;
  final(a, b, c);

  return c;
}


/*
 * Hash code for an arbitrary pointer p
 */
uint32_t jenkins_hash_ptr(const void *p) {
  return jenkins_hash_uint64((uint64_t) ((size_t) p));
}


