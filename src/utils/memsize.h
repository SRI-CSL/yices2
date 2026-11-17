/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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
