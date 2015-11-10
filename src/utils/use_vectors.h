/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * USE VECTOR = VECTOR OF POINTERS TO TERMS OR OTHER OBJECTS
 */

#ifndef __USE_VECTORS_H
#define __USE_VECTORS_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <assert.h>



/*
 * - data is an array of pointers
 * - the used entries are data[0 ... last-1]
 * - the unused entries are data[last ... size-1]
 * - every entry in data[0 ... last-1] contains a tagged pointer
 * - the tag is in the two low-order bits
 *    if tag = 00, data[i] = a pointer to some object
 *    if tag = 01, data[i] = pointer with a special mark
 *    if tag = 11, data[i] is empty, and data[i]>>2 is
 *    an index in the data array used to maintain a free list
 */
typedef struct use_vector_s {
  void **data;     // array of pointers
  uint32_t size;   // size of data array
  uint32_t last;   // first unused entry
  uint32_t nelems; // number of valid entries (not marked or deleted)
  int32_t free;    // start of the free list or -1
} use_vector_t;



/*
 * Maximal size
 */
#define MAX_USE_VECTOR_SIZE (UINT32_MAX/8)

/*
 * Minimum size after the first extension
 */
#define DEFAULT_USE_VECTOR_SIZE 8


/*
 * Tags
 */
typedef enum uv_tag {
  valid_tag = 0,  // pointer: tag = 0b00
  mark_tag = 1,   // pointer with mark
  free_tag = 3,   // empty entry: tag = 0b11
} uv_tag_t;

#define TAG_MASK ((uintptr_t) 0x3)

/*
 * Get the tag of p
 */
static inline uv_tag_t entry_tag(void *p) {
  return ((uintptr_t) p) & TAG_MASK;
}

/*
 * Checks on a vector element p
 */
static inline bool valid_entry(void *p) {
  return entry_tag(p) == valid_tag;
}

static inline bool marked_entry(void *p) {
  return entry_tag(p) == mark_tag;
}

static inline bool empty_entry(void *p) {
  return entry_tag(p) == free_tag;
}


static inline int32_t entry2index(void *p) {
  return ((int32_t)((uintptr_t) p)) >> 2;
}

static inline void *index2entry(int32_t idx) {
  return (void *) (((uintptr_t) (idx << 2)) | free_tag);
}

static inline void *unmark_entry(void *p) {
  return (void*)(((uintptr_t) p) & ~TAG_MASK);
}

static inline void *mark_entry(void *p) {
  return (void*)(((uintptr_t) p) | mark_tag);
}


/*
 * Initialization: n = initial size
 */
extern void init_use_vector(use_vector_t *v, uint32_t n);


/*
 * Resize: make size at least equal to n (no change if it's already
 * large enough).
 */
extern void resize_use_vector(use_vector_t *v, uint32_t n);


/*
 * Deletion
 */
extern void delete_use_vector(use_vector_t *v);


/*
 * Allocate an entry in the data array
 * - return its index in data
 */
extern int32_t alloc_use_vector_entry(use_vector_t *v);


/*
 * Check whether v is empty
 */
static inline bool empty_use_vector(use_vector_t *v) {
  return v->nelems == 0;
}

/*
 * Reset: empty the whole vector
 */
static inline void reset_use_vector(use_vector_t *v) {
  v->free = -1;
  v->nelems = 0;
  v->last = 0;
}

/*
 * Clear entry i: mark it as empty, add it to the free list
 */
static inline void clear_use_vector_entry(use_vector_t *v, int32_t i) {
  assert(0 <= i && i < (int32_t) v->last && valid_entry(v->data[i]));
  v->data[i] = index2entry(v->free);
  v->free = i;
  v->nelems --;
}


/*
 * Mark entry i: set tag to mark_tag
 */
static inline void mark_use_vector_entry(use_vector_t *v, int32_t i) {
  assert(0 <= i && i < (int32_t) v->last && valid_entry(v->data[i]));
  v->data[i] = mark_entry(v->data[i]);
  v->nelems --;
}


/*
 * Remove mark on entry i: set tag to valid_tag
 */
static inline void unmark_use_vector_entry(use_vector_t *v, int32_t i) {
  assert(0 <= i && i < (int32_t) v->last && marked_entry(v->data[i]));
  v->data[i] = unmark_entry(v->data[i]);
  v->nelems ++;
}

/*
 * Store ptr in a new entry and return its index
 */
static inline int32_t use_vector_store(use_vector_t *v, void *ptr) {
  int32_t i;
  assert(valid_entry(ptr));
  i = alloc_use_vector_entry(v);
  v->data[i] = ptr;
  v->nelems ++;
  return i;
}




#endif /* __USE_VECTORS_H */
