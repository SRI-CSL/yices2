#include <string.h>
#include "hash_functions.h"

/*
 * The source for Jenkins's mix and hash functions is 
 * http://www.burtleburtle.net/bob/hash/index.html
 *
 * The specific function below is lookup2.c (this is Public Domain)
 * http://www.burtleburtle.net/bob/c/lookup2.c
 *
 * int_hash_sets.c uses another hash function from Bob Jenkins's web
 * site.
 *
 * TODO: migrate to Jenkins's lookup3.c (also Public Domain)
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
 * for null-terminated strings. The original implementation
 * is in hash_functions_ori.c.
 */
static uint32_t jenkins_hash_byte_var(char *s, uint32_t initval) {
  uint32_t a, b, c, x;

  a = b = 0x9e3779b9;
  c = initval;

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
 * Variant of Jenkins's original hash-function for array of integers.
 * This assumes that most integers are small (16bits).
 * The original implementation is in hash_functions_ori.c.
 */
static uint32_t jenkins_hash_int_var(uint32_t *k, uint32_t len, uint32_t initval) {
  uint32_t a, b, c, x;

  a = b = 0x9e3779b9;
  c = initval;

  while (len >= 6) {
    x = * k++; a += (x & 0xffff); a <<= 16;
    x = * k++; a += (x & 0xffff);

    x = *k ++; b += (x & 0xffff); b <<= 16;
    x = *k ++; b += (x & 0xffff);

    x = *k ++; c += (x & 0xffff); c <<= 16;
    x = *k ++; c += (x & 0xffff);

    mix(a, b, c);
    len -= 6;
  }

  switch (len) {
  case 5: x = *k ++; a += (x & 0xffff); a <<= 16;
  case 4: x = *k ++; a += (x & 0xffff);
  case 3: x = *k ++; b += (x & 0xffff); b <<= 16;
  case 2: x = *k ++; b += (x & 0xffff);
  case 1: x = *k; c += (x & 0xffff);
    mix(a, b, c);
  }

  return c;
}

/*
 * Hash of a character string.
 */
uint32_t jenkins_hash_string_var(char *s, uint32_t seed) {
  return jenkins_hash_byte_var(s, seed);
}

/*
 * Hash of an array of small integers
 */
uint32_t jenkins_hash_intarray_var(int n, int32_t *d, uint32_t seed) {
  return jenkins_hash_int_var((uint32_t *) d, n, seed);
}

/*
 * Hash a pair of (small) integers with the given seed
 */
uint32_t jenkins_hash_pair(int32_t a, int32_t b, uint32_t seed) {
  uint32_t x, y;

  x = 0x9e3779b9 + (uint32_t) a;
  y = 0x9e3779b9 + (uint32_t) b;
  mix(x, y, seed);
  return seed;
}

/*
 * Triple
 */
uint32_t jenkins_hash_triple(int32_t a, int32_t b, int32_t c, uint32_t seed) {
  uint32_t x, y;

  x = 0x9e3779b9 + (((uint32_t) a) & 0xffff) + (((uint32_t) b) << 16);
  y = 0x9e3779b9 + (uint32_t) c;
  mix(x, y, seed);
  return seed;
}


/*
 * Quadruple
 */
uint32_t jenkins_hash_quad(int32_t a, int32_t b, int32_t c, int32_t d, uint32_t seed) {
  uint32_t x, y;

  x = 0x9e3779b9 + (((uint32_t) a) & 0xffff) + (((uint32_t) b) << 16);
  y = 0x9e3779b9 + (((uint32_t) c) & 0xffff) + (((uint32_t) d) << 16);
  mix(x, y, seed);
  return seed;
}


/*
 * Mix of hash codes.
 */
uint32_t jenkins_hash_mix2(uint32_t x, uint32_t y) {
  uint32_t c;

  c = 0x17838abc;
  mix(x, y, c);
  return c;
}

uint32_t jenkins_hash_mix3(uint32_t x, uint32_t y, uint32_t z) {
  mix(x, y, z);
  return z;
}



/*
 * Hash code for an arbitrary pointer ptr 
 */
uint32_t jenkins_hash_ptr(void *p) {
  uint32_t x, y, c;
  
  c = 0x1839829;
  x = (uint32_t) (((size_t) p) & 0xFFFFFFFF);
  y = 0x3783;
  mix(x, y, c);
  return c;
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

