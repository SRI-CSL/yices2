/*
 * OS-dependent function to determine memory usage
 */

#ifndef __MEMSIZE_H
#define __MEMSIZE_H

/*
 * Return memory used by the current process, measured in bytes.
 * - return 0 if that can't be determined
 */
extern double mem_size(void);


#endif /* __MEM_SIZE_H */
