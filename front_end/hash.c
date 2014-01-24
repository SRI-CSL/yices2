#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "hash.h"

/* FIXME -- there are almost certainly problems when the hashtable size
 * FIXME -- exceeds INT_MAX elements.  That requires 16GB+ memory... */

struct hash_table_internal {
  unsigned      (*gethash)(hash_table *, size_t);
  void          (*sethash)(hash_table *, size_t, unsigned);
  const void    **(*key)(hash_table *, unsigned);
  const void    **(*val)(hash_table *, unsigned);
  unsigned	maxset;
  char          ismap, ismulti, hashelsize, contentelsize;
};

static unsigned gethash_s1(hash_table *ht, size_t i) { return ht->hash.s1[i]; }
static unsigned gethash_s2(hash_table *ht, size_t i) { return ht->hash.s2[i]; }
static unsigned gethash_s3(hash_table *ht, size_t i) { return ht->hash.s3[i]; }
static void sethash_s1(hash_table *ht, size_t i, unsigned v) {
	ht->hash.s1[i] = v; }
static void sethash_s2(hash_table *ht, size_t i, unsigned v) {
	ht->hash.s2[i] = v; }
static void sethash_s3(hash_table *ht, size_t i, unsigned v) {
	ht->hash.s3[i] = v; }

static const void **key_set(hash_table *ht, unsigned i) {
	return &ht->contents.set[i]; }
static const void **key_map(hash_table *ht, unsigned i) {
	return &ht->contents.map[i].key; }
static const void **val_map(hash_table *ht, unsigned i) {
	return &ht->contents.map[i].val; }

static struct hash_table_internal formats[] = {
    { gethash_s1, sethash_s1, key_set, key_set,
      UCHAR_MAX, 0, 0, sizeof(unsigned char), sizeof(void *) },
    { gethash_s2, sethash_s2, key_set, key_set,
      USHRT_MAX, 0, 0, sizeof(unsigned short), sizeof(void *) },
    { gethash_s3, sethash_s3, key_set, key_set,
      UINT_MAX, 0, 0, sizeof(unsigned int), sizeof(void *) },
    { gethash_s1, sethash_s1, key_map, val_map,
      UCHAR_MAX, 1, 0, sizeof(unsigned char), 2*sizeof(void *) },
    { gethash_s2, sethash_s2, key_map, val_map,
      USHRT_MAX, 1, 0, sizeof(unsigned short), 2*sizeof(void *) },
    { gethash_s3, sethash_s3, key_map, val_map,
      UINT_MAX, 1, 0, sizeof(unsigned int), 2*sizeof(void *) },
    { gethash_s1, sethash_s1, key_set, key_set,
      UCHAR_MAX, 0, 1, sizeof(unsigned char), sizeof(void *) },
    { gethash_s2, sethash_s2, key_set, key_set,
      USHRT_MAX, 0, 1, sizeof(unsigned short), sizeof(void *) },
    { gethash_s3, sethash_s3, key_set, key_set,
      UINT_MAX, 0, 1, sizeof(unsigned int), sizeof(void *) },
    { gethash_s1, sethash_s1, key_map, val_map,
      UCHAR_MAX, 1, 1, sizeof(unsigned char), 2*sizeof(void *) },
    { gethash_s2, sethash_s2, key_map, val_map,
      USHRT_MAX, 1, 1, sizeof(unsigned short), 2*sizeof(void *) },
    { gethash_s3, sethash_s3, key_map, val_map,
      UINT_MAX, 1, 1, sizeof(unsigned int), 2*sizeof(void *) },
    { 0, 0, 0, 0,   0, -1, -1, 0, 0 }
};

static size_t mod_f(size_t x) { return x % 0xf; }
static size_t mod_1f(size_t x) { return x % 0x1f; }
static size_t mod_3f(size_t x) { return x % 0x3f; }
static size_t mod_7f(size_t x) { return x % 0x7f; }
static size_t mod_ff(size_t x) { return x % 0xff; }
static size_t mod_1ff(size_t x) { return x % 0x1ff; }
static size_t mod_3ff(size_t x) { return x % 0x3ff; }
static size_t mod_7ff(size_t x) { return x % 0x7ff; }
static size_t mod_fff(size_t x) { return x % 0xfff; }
static size_t mod_1fff(size_t x) { return x % 0x1fff; }
static size_t mod_3fff(size_t x) { return x % 0x3fff; }
static size_t mod_7fff(size_t x) { return x % 0x7fff; }
static size_t mod_ffff(size_t x) { return x % 0xffff; }
static size_t mod_1ffff(size_t x) { return x % 0x1ffff; }
static size_t mod_3ffff(size_t x) { return x % 0x3ffff; }
static size_t mod_7ffff(size_t x) { return x % 0x7ffff; }
static size_t mod_fffff(size_t x) { return x % 0xfffff; }
static size_t mod_1fffff(size_t x) { return x % 0x1fffff; }
static size_t mod_3fffff(size_t x) { return x % 0x3fffff; }
static size_t mod_7fffff(size_t x) { return x % 0x7fffff; }
static size_t mod_ffffff(size_t x) { return x % 0xffffff; }
static size_t mod_1ffffff(size_t x) { return x % 0x1ffffff; }
static size_t mod_3ffffff(size_t x) { return x % 0x3ffffff; }
static size_t mod_7ffffff(size_t x) { return x % 0x7ffffff; }
static size_t mod_fffffff(size_t x) { return x % 0xfffffff; }
static size_t mod_1fffffff(size_t x) { return x % 0x1fffffff; }
static size_t mod_3fffffff(size_t x) { return x % 0x3fffffff; }
static size_t mod_7fffffff(size_t x) { return x % 0x7fffffff; }
static size_t mod_ffffffff(size_t x) { return x % 0xffffffff; }

static size_t (*mod_hashsize[])(size_t x) = { 0, 0, 0, 0,
    mod_f, mod_1f, mod_3f, mod_7f, mod_ff,
    mod_1ff, mod_3ff, mod_7ff, mod_fff,
    mod_1fff, mod_3fff, mod_7fff, mod_ffff,
    mod_1ffff, mod_3ffff, mod_7ffff, mod_fffff,
    mod_1fffff, mod_3fffff, mod_7fffff, mod_ffffff,
    mod_1ffffff, mod_3ffffff, mod_7ffffff, mod_fffffff,
    mod_1fffffff, mod_3fffffff, mod_7fffffff, mod_ffffffff,
};

void init_hash_table(hash_table *ht, int ismap, int ismulti, unsigned size,
		     size_t (**hashfn)(const void *), void *cmpfn)
{
    ht->hashfn = hashfn;
    ht->cmpfn = cmpfn;
    ht->size = 7;
    ht->log_hashsize = 4;
    while (ht->size < size) {
	ht->size += ht->size + 1;
	ht->log_hashsize++; }
    ht->hashsize = ht->size * 2 + 1;
    assert(ht->hashsize + 1 == (1 << ht->log_hashsize));
    ht->i = formats + (ismap ? 3 : 0) + (ismulti ? 6 : 0);
    assert(ht->i->ismap == ismap);
    while (ht->size > ht->i->maxset) {
	ht->i++;
	assert(ht->i->ismap == ismap); }
    ht->hash.s1 = malloc(ht->hashsize * ht->i->hashelsize);
    memset(ht->hash.s1, 0, ht->hashsize * ht->i->hashelsize);
    ht->contents.set = malloc(ht->size * ht->i->contentelsize);
    ht->limit = ht->use = ht->collisions = 0;
}

hash_table *new_hashmap(size_t (**hashfn)(const void *), void *cmpfn,
                        unsigned size)
{
    hash_table *rv = malloc(sizeof(hash_table));
    init_hash_table(rv, 1, 0, size, hashfn, cmpfn);
    return rv;
}

hash_table *new_hashset(size_t (**hashfn)(const void *), void *cmpfn,
                        unsigned size)
{
    hash_table *rv = malloc(sizeof(hash_table));
    init_hash_table(rv, 0, 0, size, hashfn, cmpfn);
    return rv;
}

hash_table *new_multimap(size_t (**hashfn)(const void *), void *cmpfn,
                         unsigned size)
{
    hash_table *rv = malloc(sizeof(hash_table));
    init_hash_table(rv, 1, 1, size, hashfn, cmpfn);
    return rv;
}

hash_table *new_multiset(size_t (**hashfn)(const void *), void *cmpfn,
                         unsigned size)
{
    hash_table *rv = malloc(sizeof(hash_table));
    init_hash_table(rv, 0, 1, size, hashfn, cmpfn);
    return rv;
}

void fini_hash_table(hash_table *ht)
{
    free(ht->hash.s1);
    free(ht->contents.set);
}

void free_hashmap(hash_table *ht)
{
    fini_hash_table(ht);
    free(ht);
}

static unsigned hashmap_find(hash_table *ht, const void *key,
			     hash_lookup_cache *cache)
{
    size_t hash = mod_hashsize[ht->log_hashsize]((**ht->hashfn)(key));
    unsigned idx, collisions = 0;
    const void *k;
    while ((idx = ht->i->gethash(ht, hash)) &&
	   (!(k = *ht->i->key(ht, idx-1)) || ht->cmpfn(key, k)))
    {
	++collisions;
	if (++hash == ht->hashsize) hash = 0; }
    cache->slot = hash;
    cache->collisions = collisions;
    return idx;
}

static unsigned hashmap_find_next(hash_table *ht, const void *key,
				  hash_lookup_cache *cache)
{
    size_t hash = cache->slot;
    unsigned idx, collisions = cache->collisions;
    const void *k;
    if (!(idx = ht->i->gethash(ht, hash))) return idx;
    if (++hash == ht->hashsize) hash = 0;
    while ((idx = ht->i->gethash(ht, hash)) &&
	   (!(k = *ht->i->key(ht, idx-1)) || ht->cmpfn(key, k)))
    {
	++collisions;
	if (++hash == ht->hashsize) hash = 0; }
    cache->slot = hash;
    cache->collisions = collisions;
    return idx;
}

const void *hashmap_lookup(hash_table *ht, const void *key, hash_lookup_cache *cache)
{
    unsigned idx;
    hash_lookup_cache	local;
    if (!cache) cache = &local;
    idx = hashmap_find(ht, key, cache);
    return idx ? *ht->i->val(ht, idx-1) : 0;
}

const void *hashmap_lookup_next(hash_table *ht, const void *key, hash_lookup_cache *cache)
{
    unsigned idx = 0;
    if (ht->i->ismulti)
	idx = hashmap_find_next(ht, key, cache);
    return idx ? *ht->i->val(ht, idx-1) : 0;
}

static void redo_hash(hash_table *ht)
{
    unsigned i, j;
    const void *k, *v;
    hash_lookup_cache	cache;
    memset(ht->hash.s1, 0, ht->hashsize * ht->i->hashelsize);
    ht->collisions = 0;
    for (i = j = 0; i < ht->limit; i++) {
	if ((v = *ht->i->val(ht, i))) {
	    k = *ht->i->key(ht, i);
	    if (hashmap_find(ht, k, &cache)) {
		if (ht->i->ismulti)
		    while (hashmap_find_next(ht, k, &cache));
		else assert(0); }
	    if (j != i) {
		*ht->i->val(ht, j) = v;
		*ht->i->key(ht, j) = k; }
	    ht->i->sethash(ht, cache.slot, ++j);
	    ht->collisions += cache.collisions; } }
    ht->limit = ht->use = j;
}

const void *hashmap_insert(hash_table *ht, const void *key, const void *val,
			   hash_lookup_cache *cache)
{
    hash_lookup_cache	local;
    const void		*rv = 0;
    unsigned		idx, need_redo;
    if (!val)
	return hashmap_remove(ht, key, cache);
    if (cache) {
#ifndef NDEBUG
	if (hashmap_find(ht, key, &local) && ht->i->ismulti)
	    while (hashmap_find_next(ht, key, &local));
	assert(local.slot == cache->slot);
	assert(local.collisions == cache->collisions);
#endif
    } else {
	cache = &local;
	if (hashmap_find(ht, key, cache) && ht->i->ismulti)
	    while (hashmap_find_next(ht, key, cache)); }
    if ((ht->collisions += cache->collisions) > ht->size) {
	/* Too many collisions -- redo hash table */
	if (ht->use*3 < ht->limit*2) {
	    /* Many empty slots from removals, so don't expand anything */
	} else if (!ht->hashfn[1] || ht->hashsize > ht->use*10) {
	    /* Hashtable 90% empty and no alternate hash function.   Hash
	     * function isn't working but expanding further will likely
	     * make things worse, not better.
	     * Nothing we can do, so punt */
	} else if (!ht->hashfn[1] || ht->hashsize < ht->limit*3) {
	    /* No alternate hashfn, or hashtable pretty full, expand hash */
	    ht->hashsize += ht->hashsize + 1;
	    ht->log_hashsize++;
	    assert((ht->hashsize & (ht->hashsize+1)) == 0);
	    assert(ht->hashsize + 1 == (1 << ht->log_hashsize));
	    ht->hash.s1 = realloc(ht->hash.s1,
				  ht->hashsize * ht->i->hashelsize);
	} else {
	    ht->hashfn++; }
	redo_hash(ht);
	if (hashmap_find(ht, key, cache) && ht->i->ismulti)
	    while (hashmap_find_next(ht, key, cache)); }
    if ((idx = ht->i->gethash(ht, cache->slot)) == 0) {
	if (ht->limit == ht->size) {
	    ht->size += ht->size + 1;
	    assert((ht->size & (ht->size+1)) == 0);
	    ht->contents.set = realloc(ht->contents.set,
				       ht->size * ht->i->contentelsize);
	    need_redo = 0;
	    if (ht->size == ht->hashsize) {
		ht->hashsize += ht->hashsize + 1;
		ht->log_hashsize++;
		assert((ht->hashsize & (ht->hashsize+1)) == 0);
		assert(ht->hashsize + 1 == (1 << ht->log_hashsize));
		need_redo = 1; }
	    if (ht->size > ht->i->maxset) {
		assert(ht->i->ismap == ht->i[1].ismap);
		ht->i++;
		need_redo = 1; }
	    if (need_redo) {
		ht->hash.s1 = realloc(ht->hash.s1,
				      ht->hashsize * ht->i->hashelsize);
		redo_hash(ht);
		if (hashmap_find(ht, key, cache) && ht->i->ismulti)
		    while (hashmap_find_next(ht, key, cache)); } }
	idx = ++ht->limit;
	ht->i->sethash(ht, cache->slot, idx);
	ht->use++;
    } else
	rv = *ht->i->val(ht, idx-1);
    *ht->i->key(ht, idx-1) = key;
    *ht->i->val(ht, idx-1) = val;
    return rv;
}

const void *hashmap_remove(hash_table *ht, const void *key,
			   hash_lookup_cache *cache)
{
    hash_lookup_cache	local;
    const void		*rv = 0;
    unsigned		idx;
    if (cache) {
#ifndef NDEBUG
	if (hashmap_find(ht, key, &local) && ht->i->ismulti)
	    while (local.slot != cache->slot &&
		   hashmap_find_next(ht, key, cache));
	assert(local.slot == cache->slot);
	assert(local.collisions == cache->collisions);
#endif
    } else {
	cache = &local;
	hashmap_find(ht, key, cache); }
    if ((idx = ht->i->gethash(ht, cache->slot)) != 0) {
	rv = *ht->i->val(ht, idx-1);
	*ht->i->val(ht, idx-1) = 0;
	if (idx == ht->limit) {
	    ht->limit--;
	    ht->i->sethash(ht, cache->slot, 0);
	    ht->collisions -= cache->collisions; }
	ht->use--; }
    return rv;
}

const void *hashmap_first(hash_table *ht, hash_table_iter *iter)
{
    unsigned	idx = 0;
    const void	*val = 0;
    while (idx < ht->limit && !(val = *ht->i->val(ht, idx))) idx++;
    if (iter) *iter = idx;
    return val;
}

const void *hashmap_last(hash_table *ht, hash_table_iter *iter)
{
    unsigned	idx = ht->limit;
    const void	*val = 0;
    while (idx > 0 && !(val = *ht->i->val(ht, --idx)));
    if (iter) *iter = idx;
    return val;
}

const void *hashmap_next(hash_table *ht, hash_table_iter *iter)
{
    unsigned idx = *iter + 1;
    const void *val = 0;
    while (idx < ht->limit && !(val = *ht->i->val(ht, idx))) idx++;
    *iter = idx;
    return val;
}

const void *hashmap_prev(hash_table *ht, hash_table_iter *iter)
{
    unsigned idx = *iter;
    const void *val = 0;
    while (idx > 0 && !(val = *ht->i->val(ht, --idx)));
    *iter = idx;
    return val;
}

const void *hashiter_key(hash_table *ht, hash_table_iter *iter)
{
    return *ht->i->key(ht, *iter);
}

#ifdef DEBUG
void dump_hash_table(FILE *fp, hash_table *ht,
		     void (*pr)(FILE *, void *, void *))
{
    size_t i;
    int fs = 4, ls = 18;
    fprintf(fp, "hashtable %p: %s%d\n", ht, ht->i->ismap ? "map" : "set",
	    ht->i->hashelsize);
    fprintf(fp, "hashsize=%zd, size=%d, limit=%d, use=%d, collisions=%d",
	    ht->hashsize, ht->size, ht->limit, ht->use, ht->collisions);
    if (ht->limit > 999999) {
	fs = 8; ls = 9;
    } else if (ht->limit > 99999) {
	fs = 7; ls = 10;
    } else if (ht->limit > 9999) {
	fs = 6; ls = 12;
    } else if (ht->limit > 999) {
	fs = 5; ls = 15;
    }
    for (i=0; i<ht->hashsize; i++) {
	if (i%ls == 0) fprintf(fp, "\n");
	fprintf(fp, "%*i", fs, ht->i->gethash(ht, i)); }
    for (i=0; i<ht->limit; i++) {
	if (!*ht->i->val(ht, i)) continue;
	fprintf(fp, "\n%*zi: ", fs, i+1);
	pr(fp, *ht->i->key(ht, i), *ht->i->val(ht, i)); }
    fprintf(fp, "\n");
}
#endif /* DEBUG */

static size_t strhash1(const void *_p)
{
    size_t		h = 0;
    const unsigned char	*p = _p;
    while (*p)
	h = (h << 5) + (h >> (sizeof(size_t)*CHAR_BIT - 5)) + *p++;
    return h;
}

/* One-at-a-time hash from <http://burtleburtle.net/bob/hash/doobs.html> */
static size_t strhash2(const void *_p)
{
    size_t		h = 0;
    const unsigned char	*p = _p;
    while (*p) {
	h += (h<<10) + *p++;
	h ^= h >> 6; }
    h += h << 3;
    h ^= h >> 11;
    h += h << 15;
    return h;
}

/* extracted from <http://burtleburtle.net/bob/c/lookup3.c> */
/*
 * My best guess at if you are big-endian or little-endian.  This may
 * need adjustment.
 */
#if (defined(__BYTE_ORDER) && defined(__LITTLE_ENDIAN) && \
     __BYTE_ORDER == __LITTLE_ENDIAN) || \
    (defined(i386) || defined(__i386__) || defined(__i486__) || \
     defined(__i586__) || defined(__i686__) || defined(vax) || defined(MIPSEL))
# define HASH_LITTLE_ENDIAN 1
# define HASH_BIG_ENDIAN 0
#elif (defined(__BYTE_ORDER) && defined(__BIG_ENDIAN) && \
       __BYTE_ORDER == __BIG_ENDIAN) || \
      (defined(sparc) || defined(POWERPC) || defined(mc68000) || defined(sel))
# define HASH_LITTLE_ENDIAN 0
# define HASH_BIG_ENDIAN 1
#else
# define HASH_LITTLE_ENDIAN 0
# define HASH_BIG_ENDIAN 0
#endif

#define hashsize(n) ((size_t)1<<(n))
#define hashmask(n) (hashsize(n)-1)
#define rot(x,k) (((x)<<(k)) | ((x)>>(32-(k))))

#define mix(a,b,c) \
{ \
  a -= c;  a ^= rot(c, 4);  c += b; \
  b -= a;  b ^= rot(a, 6);  a += c; \
  c -= b;  c ^= rot(b, 8);  b += a; \
  a -= c;  a ^= rot(c,16);  c += b; \
  b -= a;  b ^= rot(a,19);  a += c; \
  c -= b;  c ^= rot(b, 4);  b += a; \
}

#define final(a,b,c) \
{ \
  c ^= b; c -= rot(b,14); \
  a ^= c; a -= rot(c,11); \
  b ^= a; b -= rot(a,25); \
  c ^= b; c -= rot(b,16); \
  a ^= c; a -= rot(c,4);  \
  b ^= a; b -= rot(a,14); \
  c ^= b; c -= rot(b,24); \
}

#include <stdint.h>

static size_t strhash3(const void *key)
{
  uint32_t a,b,c;                                          /* internal state */
  size_t length = strlen((char *)key);
  union { const void *ptr; size_t i; } u;     /* needed for Mac Powerbook G4 */

  /* Set up the internal state */
  a = b = c = 0xdeadbeef + ((uint32_t)length);

  u.ptr = key;
  if (HASH_LITTLE_ENDIAN && ((u.i & 0x3) == 0)) {
    const uint32_t *k = (const uint32_t *)key;         /* read 32-bit chunks */
#ifdef VALGRIND
    const uint8_t  *k8;
#endif // VALGRIND

    /*------ all but last block: aligned reads and affect 32 bits of (a,b,c) */
    while (length > 12)
    {
      a += k[0];
      b += k[1];
      c += k[2];
      mix(a,b,c);
      length -= 12;
      k += 3;
    }

    /*----------------------------- handle the last (probably partial) block */
    /*
     * "k[2]&0xffffff" actually reads beyond the end of the string, but
     * then masks off the part it's not allowed to read.  Because the
     * string is aligned, the masked-off tail is in the same word as the
     * rest of the string.  Every machine with memory protection I've seen
     * does it on word boundaries, so is OK with this.  But VALGRIND will
     * still catch it and complain.  The masking trick does make the hash
     * noticably faster for short strings (like English words).
     */
#ifndef VALGRIND

    switch(length)
    {
    case 12: c+=k[2]; b+=k[1]; a+=k[0]; break;
    case 11: c+=k[2]&0xffffff; b+=k[1]; a+=k[0]; break;
    case 10: c+=k[2]&0xffff; b+=k[1]; a+=k[0]; break;
    case 9 : c+=k[2]&0xff; b+=k[1]; a+=k[0]; break;
    case 8 : b+=k[1]; a+=k[0]; break;
    case 7 : b+=k[1]&0xffffff; a+=k[0]; break;
    case 6 : b+=k[1]&0xffff; a+=k[0]; break;
    case 5 : b+=k[1]&0xff; a+=k[0]; break;
    case 4 : a+=k[0]; break;
    case 3 : a+=k[0]&0xffffff; break;
    case 2 : a+=k[0]&0xffff; break;
    case 1 : a+=k[0]&0xff; break;
    case 0 : return c;              /* zero length strings require no mixing */
    }

#else /* make valgrind happy */

    k8 = (const uint8_t *)k;
    switch(length)
    {
    case 12: c+=k[2]; b+=k[1]; a+=k[0]; break;
    case 11: c+=((uint32_t)k8[10])<<16;  /* fall through */
    case 10: c+=((uint32_t)k8[9])<<8;    /* fall through */
    case 9 : c+=k8[8];                   /* fall through */
    case 8 : b+=k[1]; a+=k[0]; break;
    case 7 : b+=((uint32_t)k8[6])<<16;   /* fall through */
    case 6 : b+=((uint32_t)k8[5])<<8;    /* fall through */
    case 5 : b+=k8[4];                   /* fall through */
    case 4 : a+=k[0]; break;
    case 3 : a+=((uint32_t)k8[2])<<16;   /* fall through */
    case 2 : a+=((uint32_t)k8[1])<<8;    /* fall through */
    case 1 : a+=k8[0]; break;
    case 0 : return c;
    }

#endif /* !valgrind */

  } else if (HASH_LITTLE_ENDIAN && ((u.i & 0x1) == 0)) {
    const uint16_t *k = (const uint16_t *)key;         /* read 16-bit chunks */
    const uint8_t  *k8;

    /*--------------- all but last block: aligned reads and different mixing */
    while (length > 12)
    {
      a += k[0] + (((uint32_t)k[1])<<16);
      b += k[2] + (((uint32_t)k[3])<<16);
      c += k[4] + (((uint32_t)k[5])<<16);
      mix(a,b,c);
      length -= 12;
      k += 6;
    }

    /*----------------------------- handle the last (probably partial) block */
    k8 = (const uint8_t *)k;
    switch(length)
    {
    case 12: c+=k[4]+(((uint32_t)k[5])<<16);
             b+=k[2]+(((uint32_t)k[3])<<16);
             a+=k[0]+(((uint32_t)k[1])<<16);
             break;
    case 11: c+=((uint32_t)k8[10])<<16;     /* fall through */
    case 10: c+=k[4];
             b+=k[2]+(((uint32_t)k[3])<<16);
             a+=k[0]+(((uint32_t)k[1])<<16);
             break;
    case 9 : c+=k8[8];                      /* fall through */
    case 8 : b+=k[2]+(((uint32_t)k[3])<<16);
             a+=k[0]+(((uint32_t)k[1])<<16);
             break;
    case 7 : b+=((uint32_t)k8[6])<<16;      /* fall through */
    case 6 : b+=k[2];
             a+=k[0]+(((uint32_t)k[1])<<16);
             break;
    case 5 : b+=k8[4];                      /* fall through */
    case 4 : a+=k[0]+(((uint32_t)k[1])<<16);
             break;
    case 3 : a+=((uint32_t)k8[2])<<16;      /* fall through */
    case 2 : a+=k[0];
             break;
    case 1 : a+=k8[0];
             break;
    case 0 : return c;                     /* zero length requires no mixing */
    }

  } else {                        /* need to read the key one byte at a time */
    const uint8_t *k = (const uint8_t *)key;

    /*--------------- all but the last block: affect some 32 bits of (a,b,c) */
    while (length > 12)
    {
      a += k[0];
      a += ((uint32_t)k[1])<<8;
      a += ((uint32_t)k[2])<<16;
      a += ((uint32_t)k[3])<<24;
      b += k[4];
      b += ((uint32_t)k[5])<<8;
      b += ((uint32_t)k[6])<<16;
      b += ((uint32_t)k[7])<<24;
      c += k[8];
      c += ((uint32_t)k[9])<<8;
      c += ((uint32_t)k[10])<<16;
      c += ((uint32_t)k[11])<<24;
      mix(a,b,c);
      length -= 12;
      k += 12;
    }

    /*-------------------------------- last block: affect all 32 bits of (c) */
    switch(length)                   /* all the case statements fall through */
    {
    case 12: c+=((uint32_t)k[11])<<24;
    case 11: c+=((uint32_t)k[10])<<16;
    case 10: c+=((uint32_t)k[9])<<8;
    case 9 : c+=k[8];
    case 8 : b+=((uint32_t)k[7])<<24;
    case 7 : b+=((uint32_t)k[6])<<16;
    case 6 : b+=((uint32_t)k[5])<<8;
    case 5 : b+=k[4];
    case 4 : a+=((uint32_t)k[3])<<24;
    case 3 : a+=((uint32_t)k[2])<<16;
    case 2 : a+=((uint32_t)k[1])<<8;
    case 1 : a+=k[0];
             break;
    case 0 : return c;
    }
  }

  final(a,b,c);
  return c;
}

size_t (*strhash[])(const void *) = {
    strhash1, strhash2, strhash3, 0 };

static size_t ptrhash1(const void *p)
{
    uintptr_t h = (uintptr_t)p;
    h = (h >> 5) | (h << (sizeof(h)*CHAR_BIT - 5));
    return (size_t)h;
}

/* a random 8-bit permutation that spreads its output over every 4th bit */
static unsigned ptab[256] = {
    0x11101001, 0x10101011, 0x10111001, 0x00101000, 0x00110010, 0x10101101,
    0x01010011, 0x10100101, 0x01111001, 0x01101011, 0x00001101, 0x10010001,
    0x00000101, 0x11000011, 0x10011001, 0x10000011, 0x11000110, 0x10111110,
    0x01001011, 0x11011000, 0x11100000, 0x00000001, 0x01011110, 0x00000010,
    0x00000110, 0x01001111, 0x00011101, 0x11100110, 0x11011010, 0x11001111,
    0x01000000, 0x00001010, 0x10001010, 0x01100001, 0x00111111, 0x11101010,
    0x11110000, 0x11011011, 0x11010111, 0x11010011, 0x01011101, 0x11101000,
    0x11000001, 0x00010111, 0x00101011, 0x10100111, 0x00111010, 0x01010010,
    0x00010110, 0x10011010, 0x11001101, 0x10101111, 0x10011000, 0x11001100,
    0x11110111, 0x11101110, 0x00111110, 0x10111100, 0x11110101, 0x00101110,
    0x00001100, 0x11001110, 0x01001000, 0x00010001, 0x10010010, 0x01111101,
    0x01011010, 0x00010011, 0x11001011, 0x00111001, 0x01011001, 0x10110001,
    0x01100010, 0x00000100, 0x10001001, 0x00100001, 0x00111011, 0x11100111,
    0x11101101, 0x10100000, 0x10110110, 0x00101010, 0x00110001, 0x11111111,
    0x10000111, 0x00010100, 0x00000111, 0x00001000, 0x10010011, 0x01010110,
    0x00110110, 0x10010101, 0x00011001, 0x01001101, 0x10001100, 0x01001100,
    0x10100100, 0x11010001, 0x00010000, 0x10001011, 0x11110011, 0x10011110,
    0x11011101, 0x10110000, 0x01111110, 0x11000010, 0x10111111, 0x00001110,
    0x01101101, 0x01010101, 0x00010010, 0x01010001, 0x01101111, 0x01011111,
    0x01001010, 0x00100010, 0x11111010, 0x00011111, 0x00000000, 0x11011111,
    0x11001010, 0x10001111, 0x10011100, 0x00100011, 0x01100100, 0x00100111,
    0x01110011, 0x10000001, 0x11101011, 0x01111000, 0x01011100, 0x00101101,
    0x10011111, 0x10000010, 0x11100001, 0x01101001, 0x01100111, 0x00001001,
    0x01010000, 0x01001110, 0x01000111, 0x11111011, 0x10101100, 0x11100100,
    0x10100001, 0x11110010, 0x10011101, 0x11010101, 0x10111010, 0x10110010,
    0x11101111, 0x00001011, 0x11111001, 0x01100000, 0x01110110, 0x00110011,
    0x01110101, 0x00011011, 0x00101111, 0x00111100, 0x10100011, 0x00001111,
    0x00100100, 0x10100110, 0x11101100, 0x01110000, 0x10110011, 0x10110100,
    0x10101001, 0x10000101, 0x10010111, 0x01100110, 0x11011100, 0x00110101,
    0x00100000, 0x00110000, 0x11100010, 0x01110001, 0x01110111, 0x10000110,
    0x11100011, 0x00110111, 0x00100101, 0x01000010, 0x10010100, 0x11111110,
    0x11011001, 0x00111000, 0x10010000, 0x11110100, 0x00011010, 0x10000000,
    0x11000000, 0x01101100, 0x01101010, 0x11111100, 0x01000001, 0x00111101,
    0x10010110, 0x11001001, 0x11010110, 0x01011000, 0x10111011, 0x01110100,
    0x10110111, 0x11010100, 0x01111111, 0x10101010, 0x00000011, 0x11110110,
    0x11010010, 0x10101110, 0x00011000, 0x01111010, 0x10111000, 0x11110001,
    0x01001001, 0x01101110, 0x10101000, 0x01101000, 0x11000111, 0x11011110,
    0x00100110, 0x01000100, 0x01000011, 0x00110100, 0x11111101, 0x10001110,
    0x10111101, 0x01111011, 0x11001000, 0x10110101, 0x11000100, 0x00010101,
    0x01010100, 0x01011011, 0x01000101, 0x10001000, 0x11000101, 0x01010111,
    0x01100011, 0x10000100, 0x11100101, 0x01111100, 0x01100101, 0x10001101,
    0x00101100, 0x00011110, 0x01110010, 0x00101001, 0x00011100, 0x11010000,
    0x10011011, 0x10100010, 0x01000110, 0x11111000 };

static size_t ptrhash2(const void *p)
{
    uintptr_t v = (uintptr_t)p;
    size_t h = ptab[v & 0xff] +
        (ptab[(v >> 8) & 0xff] << 1) +
        (ptab[(v >> 16) & 0xff] << 2) +
        (ptab[(v >> 24) & 0xff] << 3);
    if (sizeof(unsigned) < sizeof(v)) {
	size_t x = ptab[(v >> 32) & 0xff] +
	    (ptab[(v >> 40) & 0xff] << 1) +
	    (ptab[(v >> 48) & 0xff] << 2) +
	    (ptab[(v >> 56) & 0xff] << 3);
	if (sizeof(h) < sizeof(v))
	    h ^= x;
	else
	    h += x << 32; }
    return h;
}

static size_t ptrhash3(const void *p)
{
    return ptrhash2((void *)(uintptr_t)ptrhash2(p));
}

size_t (*ptrhash[])(const void *) = {
    ptrhash1, ptrhash2, ptrhash3, 0 };

int ptrcmp(const void *a, const void *b)
{
    intptr_t rv = (intptr_t)b - (intptr_t)a;
    if (sizeof(intptr_t) > sizeof(int))
	rv |= rv >> (sizeof(int)*8);
    return (int)rv;
}
