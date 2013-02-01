#include <stdlib.h>
#include "vector.h"
#include "memalloc.h"

void init_raw_vector(void *vec, size_t elsize, int mincap)
{
    struct raw_vector *v = vec;
    v->size = 0;
    v->capacity = 32 / elsize;
    if (v->capacity < 4) v->capacity = 4;
    if (v->capacity < mincap) v->capacity = mincap;
    v->data = safe_malloc(elsize * v->capacity);
}

int expand_raw_vector(void *vec, size_t elsize)
{
    struct raw_vector *v = vec;
    v->capacity *= 2;
    v->data = safe_realloc(v->data, elsize * v->capacity);
    return 0;
}
