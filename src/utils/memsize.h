/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * OS-DEPENDENT FUNCTION TO ESTIMATE MEMORY USAGE
 */

#ifndef __MEMSIZE_H
#define __MEMSIZE_H

/*
 * Return memory used by the current process, measured in bytes.
 * - return 0 if that can't be determined
 */
extern double mem_size(void);


#endif /* __MEM_SIZE_H */
