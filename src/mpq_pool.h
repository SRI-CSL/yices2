#ifndef __MPQ_POOL_H
#define __MPQ_POOL_H

#include <gmp.h>

/*
 *  Initialize the pool, must be done once per process. Prior
 *  to using any of the routines below.
 *
 *  Returns 0 on success, nonzero on error.
 *
 */
extern int mpq_pool_init(void);

/*
 * Fetch an mpq by its index
 */
extern mpq_ptr fetch_mpq(int32_t i);

/*
 * Borrow an mpq from the pool, the mpq will be *qp
 * and it's index will be *indexp. The index is used to
 * return the mpq to the pool. qp can be NULL, in which case
 * only the index is returned.
 *
 * Returns 0 on success, nonzero on error.
 *
 */
extern int mpq_pool_borrow(int32_t* indexp, mpq_ptr* qp);

/*
 * Return the mpq with that index to the pool.
 *
 *  Returns 0 on success, nonzero on error.
 *
 */
extern int mpq_pool_return(int32_t index);

/*
 * Reclaim all the memory used by the pool. Using the pool
 * after this is an error.
 *
 *  Returns 0 on success, nonzero on error.
 *
 */
extern int mpq_pool_shutdown(void);


#endif /* __MPQ_POOL_H */


