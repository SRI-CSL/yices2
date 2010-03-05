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

/* Jenkins hash */
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
 * Faster variant
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
 * Variant
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

uint32_t jenkins_hash_string_ori(char *s, uint32_t seed) {
  uint32_t n;
  n = strlen(s);
  return jenkins_hash_byte_ori(s, n, seed);
}


/*
 * Hash of an array of small integers
 */
uint32_t jenkins_hash_intarray_var(int n, int32_t *d, uint32_t seed) {
  return jenkins_hash_int_var((uint32_t *) d, n, seed);
}

uint32_t jenkins_hash_intarray_ori(int n, int32_t *d, uint32_t seed) {
  return jenkins_hash_int_ori((uint32_t *) d, n, seed);
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


/*
 * Simple hash for strings
 */
uint32_t hash_string(char *s) {
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
 * Simple hash for integer array
 */
uint32_t hash_intarray(int n, int32_t *d) {
  uint32_t h, c;

  h = 0x887392de;
  c = 31;
  while (n > 0) {
    h += c * (*d);
    d ++;
    n --;
  }
  h += c;

  return h;
}

