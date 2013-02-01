#ifndef _vector_h_
#define _vector_h_

struct raw_vector {
    int		capacity, size;
    void	*data;
};

#define VECTOR(NAME)	NAME##_VECTOR
#define DECLARE_VECTOR(TYPE)		\
typedef struct {			\
    int		capacity, size;		\
    TYPE	*data;			\
} TYPE##_VECTOR;
#define DECLARE_VECTOR2(NAME, ELTYPE) 	\
typedef struct {			\
    int		capacity, size;		\
    ELTYPE	*data;			\
} NAME##_VECTOR;

#define VECTOR_init(vec, ...) \
    init_raw_vector(&(vec), sizeof((vec).data[0]), __VA_ARGS__+0)
#define VECTOR_add(vec, val) \
    (((vec).size == (vec).capacity				\
      ? expand_raw_vector(&(vec), sizeof((vec).data[0])) : 0),	\
     (vec).data[(vec).size++] = (val))

extern void init_raw_vector(void *vec, size_t elsize, int mincap);
extern int expand_raw_vector(void *vec, size_t elsize);
#define VECTOR_free(vec)	safe_free((vec).data)

#endif /* _vector_h_ */
