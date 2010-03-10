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
 * when final(r) is called, r->hash, r->value, r->string are still valid.
 */
typedef void (*stbl_finalizer_t)(stbl_rec_t *r);


/*
 * Symbol table
 */
typedef struct stbl_s {
  uint32_t size;     // power of 2
  uint32_t nelems;   // number of records
  uint32_t ndeleted; // number of deleted records (in the free_rec list)
  uint32_t free_idx;     // free slot in bnk
  stbl_bank_t *bnk;
  stbl_rec_t *free_rec;  // list of free records
  stbl_rec_t **data;     // array of record list (hash table)

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
extern void stbl_remove(stbl_t *sym_table, char *symbol);

/*
 * Return value attached to symbol or -1 if symbol is not in the table.
 */
extern int32_t stbl_find(stbl_t *sym_table, char *symbol);

/*
 * Add mapping symbol --> value. The previous value mapped to
 * symbol is hidden. It is revealed after stbl_remove(sym_table, symbol).
 * The table stores symbol as a pointer, no copy is made.
 */
extern void stbl_add(stbl_t *sym_table, char *symbol, int32_t val);



#endif /* __SYMBOL_TABLES_H */
