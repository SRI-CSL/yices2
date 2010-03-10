/*
 * Hash functions: all return an unsigned 32bit integer
 *
 * This module includes variant implementations of hash functions
 * that are used only for tests. Moved them here so that they don't
 * get linked into the binaries.
 */

#ifndef __HASH_FUNCTIONS_ORI_H
#define __HASH_FUNCTIONS_ORI_H

#include <stdint.h>

extern uint32_t jenkins_hash_string_ori(char *s, uint32_t seed);
extern uint32_t jenkins_hash_intarray_ori(int n, int32_t *d, uint32_t seed);

#endif /* __HASH_FUNCTIONS_ORI_H */
