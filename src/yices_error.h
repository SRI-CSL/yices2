/*
 * Print an error message based on the current error report
 */

#ifndef __YICES_ERROR_H

#include <stdio.h>

/*
 * Print an error message for the internal error report structure.
 * - print the message on stream f
 */
extern void yices_print_error(FILE *f);

#endif  /* __YICES_ERROR_H */
