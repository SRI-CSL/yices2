#ifndef __MPZ_POOL_H
#define __MPZ_POOL_H

#include <gmp.h>

/*
 *  Initialize the pool, must be done once per process. Prior
 *  to using any of the routines below.
 *
 *  Returns 0 on success, nonzero on error.
 *
 */
extern int mpz_pool_init(void);

/*
 * Fetch an mpz by its index
 */
extern mpz_ptr fetch_mpz(int32_t i);

/*
 * Borrow an mpz from the pool, the mpz will be *qp
 * and it's index will be *indexp. The index is used to
 * return the mpz to the pool. qp can be NULL, in which case
 * only the index is returned.
 *
 *  Returns 0 on success, nonzero on error.
 *
 */
extern int mpz_pool_borrow(int32_t* indexp,  mpz_ptr* zp);

/*
 * Return the mpz with that index to the pool.
 *
 *  Returns 0 on success, nonzero on error.
 *
 */
extern int mpz_pool_return(int32_t index);

/*
 * Reclaim all the memory used by the pool. Using the pool
 * after this is an error.
 *
 *  Returns 0 on success, nonzero on error.
 *
 */
extern int mpz_pool_shutdown(void);


#endif /* __MPZ_POOL_H */


