/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Pool for allocating mpq numbers in a thread-safe manner.
 */
#ifndef __MPQ_POOL_H
#define __MPQ_POOL_H

#include <stdint.h>
#include <gmp.h>

/*
 * Initialize the pool.
 *
 * This must be done once per process and before calling any of the functions below.
 * This will abort if the pool can't be initialized.
 */
extern void mpq_pool_init(void);

/*
 * Borrow an mpq from the pool:
 * - return a fresh index to an pool element
 * - if q isn't NULL, also return a pointer to the pool element in *q
 */
extern int32_t mpq_pool_borrow(mpq_ptr *q);

/*
 * Fetch an mpq by its index i
 */
extern mpq_ptr fetch_mpq(int32_t i);

/*
 * Return the mpq of index i to the pool.
 */
extern void mpq_pool_return(int32_t i);

/*
 * Reclaim all the memory used by the pool. Using the pool
 * after this is an error.
 */
extern void mpq_pool_shutdown(void);


#endif /* __MPQ_POOL_H */


