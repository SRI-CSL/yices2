/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#ifndef __TAGGED_POINTERS_H
#define __TAGGED_POINTERS_H

#include <stdbool.h>
#include <stddef.h>
#include <assert.h>


/*
 * First version: 2bit tags are stored in the two low-order bits
 * of (void *) pointers.
 */
#define PTR_TAG_MASK ((size_t) 0x3)

// get the tag of pointer p
static inline uint32_t ptr_tag(void *p) {
  return ((size_t) p) & PTR_TAG_MASK;
}

// untag the pointer
static inline void *untag_ptr(void *p) {
  return (void*)(((size_t) p) & ~PTR_TAG_MASK);
}

// add tag to pointer p
static inline void *tag_ptr(void *p, uint32_t tag) {
  assert((tag & ~PTR_TAG_MASK) == 0 && ptr_tag(p) == 0);
  return (void *) (((size_t) p) | (size_t) tag);
}


/*
 * Second version: void *p stores either a pointer
 * or a 31 bit integer. The tag is the low-order bit
 * - for an integer, the tag is 1
 * - for a pointer, the tag is 0
 */
#define IPTR_TAG_MASK ((size_t) 1)

// check whether p is a pointer or an int
static inline bool has_int_tag(void *p) {
  return (((size_t) p) & IPTR_TAG_MASK);
}

// extract the integer from p (as a signed integer)
static inline int32_t untag_i32(void *p) {
  assert(has_int_tag(p));
  return ((int32_t) ((size_t) p)) >> 1;
}

// extract an unsigned integer from p
static inline uint32_t untag_u32(void *p) {
  assert(has_int_tag(p));
  return ((uint32_t)((size_t) p)) >> 1;
}

// pack x into a void * pointer and add the tag
static inline void *tag_i32(int32_t x) {
  return (void *) ((size_t)((uint32_t)((x << 1)|1)));
}

// same thing for an unsigned integer x
static inline void *tag_u32(uint32_t x) {
  return (void *) ((size_t)((x << 1)|1));
}


#endif /* __TAGGED_POINTERS_H */
