/*
 * Print an error message based on the current error report
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

#endif  /* __YICES_ERROR_H */
