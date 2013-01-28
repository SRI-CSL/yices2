#ifndef _hash_h_
#define _hash_h_

#ifdef __cplusplus
extern "C" {
#endif

struct hash_table_internal;

struct hash_table {
    struct hash_table_internal *i;
    size_t (**hashfn)(const void *);
    int (*cmpfn)(const void *, const void *);
    union {
	unsigned char *s1;
	unsigned short *s2;
	unsigned int *s3;
    } hash;
    union {
	void	**set;
	struct {
	    void *key;
	    void *val;
	} *map;
    } contents;
    size_t	hashsize;
    unsigned	size, limit, use, collisions, log_hashsize;
};

struct hash_lookup_cache {
    size_t	slot;
    unsigned	collisions;
};

typedef unsigned hash_table_iter;

#ifdef __cplusplus
#define DEFAULT(X)	= X
#else
typedef struct hash_table hash_table;
typedef struct hash_lookup_cache hash_lookup_cache;
#define DEFAULT(X)
#endif

void init_hash_table(hash_table *ht, int ismap, int ismulti, unsigned size,
                     size_t (**hashfn)(const void *), void *cmpfn);
hash_table *new_hashmap(size_t (**hashfn)(const void *), void *cmpfn,
			unsigned size DEFAULT(0));
hash_table *new_hashset(size_t (**hashfn)(const void *), void  *cmpfn,
			unsigned size DEFAULT(0));
hash_table *new_multimap(size_t (**hashfn)(const void *), void *cmpfn,
			 unsigned size DEFAULT(0));
hash_table *new_multiset(size_t (**hashfn)(const void *), void  *cmpfn,
			 unsigned size DEFAULT(0));
void fini_hash_table(hash_table *ht);
void free_hashmap(hash_table *ht);

void *hashmap_lookup(hash_table *ht, const void *key,
		     hash_lookup_cache *cache DEFAULT(0));
void *hashmap_lookup_next(hash_table *ht, const void *key,
			  hash_lookup_cache *cache);
void *hashmap_insert(hash_table *ht, const void *key, const void *val,
		     hash_lookup_cache *cache DEFAULT(0));
void *hashmap_remove(hash_table *ht, const void *key,
		     hash_lookup_cache *cache DEFAULT(0));

#define free_hashset(ht)		free_hashmap(ht)
#define hashset_lookup(ht, k, c)	hashmap_lookup(ht, k, c)
#define hashset_lookup_next(ht, k, c)	hashmap_lookup_next(ht, k, c)
#define hashset_insert(ht, k, c)	hashmap_insert(ht, k, k, c)
#define hashset_remove(ht, k, c)	hashmap_remove(ht, k, c)

void *hashmap_first(hash_table *ht, hash_table_iter *iter);
void *hashmap_last(hash_table *ht, hash_table_iter *iter);
void *hashmap_next(hash_table *ht, hash_table_iter *iter);
void *hashmap_prev(hash_table *ht, hash_table_iter *iter);
void *hashiter_key(hash_table *ht, hash_table_iter *iter);

#define hashset_first(ht, it)		hashmap_first(ht, it)
#define hashset_last(ht, it)		hashmap_last(ht, it)
#define hashset_next(ht, it)		hashmap_next(ht, it)
#define hashset_prev(ht, it)		hashmap_prev(ht, it)

#ifdef DEBUG
#include <stdio.h>
void dump_hash_table(FILE *fp, hash_table *ht,
		     void (*pr)(FILE *, void *, void *));
#endif /* DEBUG */

extern size_t (*strhash[])(const void *);

extern size_t (*ptrhash[])(const void *);
int ptrcmp(const void *, const void *);

#ifdef __cplusplus
}
#endif

#endif /* _hash_h_ */
