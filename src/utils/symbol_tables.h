/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SYMBOL TABLES
 *
 * They map strings to non-negative 32bit integers
 */

#ifndef __SYMBOL_TABLES_H
#define __SYMBOL_TABLES_H

#include <stdint.h>
#include <stdbool.h>

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
 * the number of buckets), we periodically check the average cost
 * of recent lookups. If this cost is high, we try to resize the table.
 * But we must also take into account the fact that the same string
 * may occur several times in one list (in which case, resizing may
 * not help at all).
 *
 * We estimate the cost of a lookup by counting the number of records
 * visited when scanning a list. A lookup is considered expensive if
 * it visits at least MAXVISITS records. If a lookup in list data[i]
 * is expensive, we check whether the list contains different records
 * or many times the same symbol.
 *
 * The following parameters are used:
 * - NLOOKUPS = periodic check for resizing
 * - MAXVISITS = threshold for expensive lookups
 * - RESIZE_THRESHOLD = total cost of the last NLOOKUPS before resizing
 *   is triggered.
 */
#define STBL_NLOOKUPS 10u
#define STBL_MAXVISITS 3u
#define STBL_RESIZE_THRESHOLD 20u



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

  // counters for cost/resize heuristics
  uint32_t lctr;         // lookup counter: when this gets to 0, we check w
  uint32_t cost;         // accumulated cost of all lookups since last reset of lctr

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
typedef void (*stbl_iterator_t)(void *aux, const stbl_rec_t *r);

extern void stbl_iterate(stbl_t *sym_table, void *aux, stbl_iterator_t f);


/*
 * Remove all records that satisfy f:
 * - calls f(aux, r) on every record r present in the table
 * - if f(aux, r) returns true, then the finalizer is called (finalize(r))
 *   then r is removed from the table.
 * - f must not have side effects
 */
typedef bool (*stbl_filter_t)(void *aux, const stbl_rec_t *r);

extern void stbl_remove_records(stbl_t *sym_table, void *aux, stbl_filter_t f);

#endif /* __SYMBOL_TABLES_H */
