/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * ERROR MESSAGE BASED ON THE CURRENT ERROR REPORT
 */

#ifndef __YICES_ERROR_H

#include <stdio.h>
#include <stdint.h>

/*
 * Print an error message for the internal error report structure.
 * - print the message on stream f
 * - return 0 on success
 * - return -1 if something went wrong when trying to write to f
 *
 * If there's an error, then 'errno' can be used to get details
 * on what went wrong.
 */
extern int32_t print_error(FILE *f);

/*
 * Construct an error message and return it as a string.
 * - the returned string must be freed when no-longer needed
 *   by calling safe_free.
 */
extern char* error_string(void);


#endif  /* __YICES_ERROR_H */
