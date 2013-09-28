/*
 * Symbol tables: map strings to non-negative 32bit integers
 */

#ifndef __SYMBOL_TABLES_H
#define __SYMBOL_TABLES_H

#include <stdint.h>


/*
 * A symbol table contains a lists of records <string, hash, value>.
 * The same string symbol may occur several times in the list.
 * In such a case, the first record masks the others.
 */
typedef struct stbl_rec_s stbl_rec_t; 

struct stbl_rec_s {
  uint32_t hash;
  int32_t value;
  char *string;
  stbl_rec_t *next;
};


/*
 * Bank for allocation of records
 */
#define STBL_BANK_SIZE 255

typedef struct stbl_bank_s stbl_bank_t;

struct stbl_bank_s {
  stbl_bank_t *next;
  stbl_rec_t block[STBL_BANK_SIZE];
};


/*
 * Finalizer: called when a record r is being deleted (see remove)
 * when finalize(r) is called, r->hash, r->value, r->string are still valid.
 */
typedef void (*stbl_finalizer_t)(stbl_rec_t *r);


/*
 * To determine when it makes sense to resize the table (i.e., double
 * the number of buckets), we need to take into account the fact that
 * a bucket may contain the same string several times.  The average
 * list size is nelems/size But resizing when this ratio becomes too
 * high does not pay off if there are many records with the same
 * string. (In the worst case, the load is concentrated in one bucket
 * and all records have the same string. We don't want to resize the
 * table in this scenario). To decide when to resize, we keep track of
 * the cost of every lookup operation and we resize when this cost
 * becomes too high. Most recent lookups matter more than old ones so
 * we estimate cost as follows:
 * - initially cost = 0
 * - during a lookup operation, we count the number of records traversed
 *   then we set cost := N + \alpha cost where 0 < \alpha < 1
 * - we resize when cost > RESIZE_THRESHOLD
 *
 * We set the threshold to (log 0.1)/(log alpha) so that alpha ^ threshold = 0.1
 * - roughly this means that we interprete cost as approximately equal to the
 *   cost of the last K lookups for K close to alpha. Then we resize if
 *   the last K lookups visited more than K records.
 */
#define ALPHA 0.8
#define RESIZE_THRESHOLD 10.32
// #define ALPHA 0.9
// #define RESIZE_THRESHOLD 21.85
// #define ALPHA 0.95
// #define RESIZE_THRESHOLD 44.89


/*
 * Symbol table
 */
typedef struct stbl_s {
  stbl_rec_t **data;     // array of record list (hash table)
  stbl_bank_t *bnk;
  stbl_rec_t *free_rec;  // list of free records
  uint32_t size;         // power of 2 = number of buckets
  uint32_t nelems;       // number of records
  uint32_t ndeleted;     // number of deleted records (in the free_rec list)
  uint32_t free_idx;     // free slot in bnk
  double cost;

  stbl_finalizer_t finalize;
} stbl_t;


/*
 * Default initial size
 */
#define STBL_DEFAULT_SIZE 64


/*
 * Maximal size
 */
#define MAX_STBL_SIZE (UINT32_MAX/sizeof(stbl_rec_t))


/*
 * Initialize: empty table of size n. n must be a power of 2.
 * If n = 0, the default size is used.
 */
extern void init_stbl(stbl_t *sym_table, uint32_t n);

/*
 * Set the finalizer callback
 */
static inline void stbl_set_finalizer(stbl_t *sym_table, stbl_finalizer_t fun) {
  sym_table->finalize = fun;
}

/*
 * Delete the full table. The finalizer is called for all the records
 * in the table.
 */
extern void delete_stbl(stbl_t *sym_table);

/*
 * Empty the table. The finalizer is called for all the deleted records.
 */
extern void reset_stbl(stbl_t *sym_table);

/*
 * Remove value attached to symbol. No effect if symbol is not in the table.
 * If symbol is in the table, then the finalizer is called on the corresponding
 * record.
 */
extern void stbl_remove(stbl_t *sym_table, const char *symbol);

/*
 * Return value attached to symbol or -1 if symbol is not in the table.
 */
extern int32_t stbl_find(stbl_t *sym_table, const char *symbol);

/*
 * Add mapping symbol --> value. The previous value mapped to
 * symbol is hidden. It is revealed after stbl_remove(sym_table, symbol).
 * The table stores symbol as a pointer, no copy is made.
 */
extern void stbl_add(stbl_t *sym_table, char *symbol, int32_t val);

/*
 * Remove the mapping symbol --> val from the table.
 * This removes the mapping even if it's hidden.
 * If the mapping is not in the table, this has no effect.
 * If the mapping occurs several times, then only the most recent
 * occurrence is removed.
 */
extern void stbl_delete_mapping(stbl_t *sym_table, const char *symbol, int32_t val);


/*
 * Iterator: call f(aux, r) for every live record r in the table
 * - aux is an arbitrary pointer, provided by the caller
 * - f must not have side effects (it must not add or remove anything 
 *   from the symbol table, or modify the record r).
 */
typedef void (*stbl_iterator_t)(void *aux, stbl_rec_t *r);

extern void stbl_iterate(stbl_t *sym_table, void *aux, stbl_iterator_t f);


#endif /* __SYMBOL_TABLES_H */
