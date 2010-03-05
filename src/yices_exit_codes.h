/*
 * On non-recoverable errors, Yices calls exit with a non-zero status.
 * The status values are defined here for different error conditions
 * (incomplete).
 *
 * TODO: check portability, check conventions if any.
 */

#ifndef __YICES_EXIT_CODES_H
#define __YICES_EXIT_CODES_H

#include <stdlib.h>

#define YICES_EXIT_OUT_OF_MEMORY   16
#define YICES_EXIT_SYNTAX_ERROR    17
#define YICES_EXIT_FILE_NOT_FOUND  18
#define YICES_EXIT_USAGE           19
#define YICES_EXIT_ERROR           20
#define YICES_EXIT_INTERRUPTED     21
#define YICES_EXIT_INTERNAL_ERROR  22

#define YICES_EXIT_SUCCESS         EXIT_SUCCESS

#endif /* __YICES_EXIT_CODES_H */
