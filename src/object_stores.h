/*
 * Store for allocation/release of (small) objects of fixed size.
 */

#ifndef __OBJECT_STORES_H
#define __OBJECT_STORES_H

#include <stdint.h>

/*
 * Bank = a block of objects
 */
typedef struct object_bank_s {
  struct object_bank_s *next;
  char block[0]; // real size determined at allocation time
} object_bank_t;

/*
 * Store = a list of blocks
 * - allocations are performed via a free list, 
 * - or in the first block of the bank list,
 * - or by adding a new block.
 */
typedef struct object_store_s {
  object_bank_t *bnk;  // first block in the bank list
  void *free_list;
  uint32_t free_index; // index of last allocated object in first block
  uint32_t objsize;    // size of all objects (in bytes)
  uint32_t blocksize;  // size of blocks (multiple of objsize).
} object_store_t;


/*
 * Bounds of objsize and nobj per block: to avoid numerical overflows,
 * we need objsize * nobj <= UINT32_MAX.  Stores are intended for
 * small objects so the following bounds should be more than enough.
 */
#define MAX_OBJ_SIZE 512
#define MAX_OBJ_PER_BLOCK 4096


/*
 * Initialize store s for object of the given size
 * - n = number of objects in each block
 */
extern void init_objstore(object_store_t *s, uint32_t objsize, uint32_t n);

/*
 * Delete the full store: all banks are freed
 */
extern void delete_objstore(object_store_t *s);

/*
 * Reset the store: remove all objects
 */
extern void reset_objstore(object_store_t *s);


/*
 * Delete with finalizer: apply function f to all 
 * objects in the store before freeing the banks.
 */
extern void objstore_delete_finalize(object_store_t *s, void (*f)(void *));

/*
 * Allocate an object
 */
extern void *objstore_alloc(object_store_t *s);

/*
 * Free an allocated object: add it to s->free_list.
 * next pointer is stored in *object
 */
static inline void objstore_free(object_store_t *s, void *object) {
  * ((void **) object) = s->free_list;
  s->free_list = object;
}


#endif /* __OBJECT_STORES_H */

