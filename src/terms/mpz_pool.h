/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Pool for allocating mpz numbers in a thread-safe manner.
 */
#ifndef __MPZ_POOL_H
#define __MPZ_POOL_H

#include <stdint.h>
#include <gmp.h>


/*
 * Initialize the pool.
 *
 * This must be done once per process and before calling any of the functions below.
 * This will abort if the pool can't be initialized.
 */
extern void mpz_pool_init(void);

/*
 * Borrow an mpz from the pool:
 * - return a fresh index to an pool element
 * - if z isn't NULL, also returns a pointer to the pool element in *z
 */
extern int32_t mpz_pool_borrow(mpz_ptr *z);

/*
 * Fetch an mpz by its index i
 */
extern mpz_ptr fetch_mpz(int32_t i);

/*
 * Return the mpz of index i to the pool.
 */
extern void mpz_pool_return(int32_t i);

/*
 * Reclaim all the memory used by the pool. Using the pool
 * after this is an error.
 */
extern void mpz_pool_shutdown(void);


#endif /* __MPZ_POOL_H */


