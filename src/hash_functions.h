/*
 * Hash functions: all return an unsigned 32bit integer
 */

#ifndef __HASH_FUNCTIONS_H
#define __HASH_FUNCTIONS_H

#include <stdint.h>

/*
 * Generic hash functions for (small) integers, using Jenkin's mix function
 */

// hash with a seed
extern uint32_t jenkins_hash_pair(int32_t a, int32_t b, uint32_t seed);
extern uint32_t jenkins_hash_triple(int32_t a, int32_t b, int32_t c, uint32_t seed);
extern uint32_t jenkins_hash_quad(int32_t a, int32_t b, int32_t c, int32_t d, uint32_t seed);

// mix of two or three hash codes
extern uint32_t jenkins_hash_mix2(uint32_t x, uint32_t y);
extern uint32_t jenkins_hash_mix3(uint32_t x, uint32_t y, uint32_t z);

// null-termninated string
extern uint32_t jenkins_hash_string_var(char *s, uint32_t seed);

// array of n integers
extern uint32_t jenkins_hash_intarray_var(uint32_t n, int32_t *d, uint32_t seed);


/*
 * Use default seeds
 */
static inline uint32_t jenkins_hash_string(char * s) {
  return jenkins_hash_string_var(s, 0x17838abc);
}

static inline uint32_t jenkins_hash_intarray(uint32_t n, int32_t *d) {
  return jenkins_hash_intarray_var(n, d, 0x17836abc);
}


/*
 * Hash code for an arbitrary pointer
 */
extern uint32_t jenkins_hash_ptr(void *p);


/*
 * Hash code for a 32bit integer
 */
extern uint32_t jenkins_hash_uint32(uint32_t x);

// signed integer
static inline uint32_t jenkins_hash_int32(int32_t x) {
  return jenkins_hash_uint32(x);
}


/*
 * Hash code for a 64bit integer
 */
extern uint32_t jenkins_hash_uint64(uint64_t x);

// signed integer
static inline uint32_t jenkins_hash_int64(int64_t x) {
  return jenkins_hash_uint64(x);
}


#endif
