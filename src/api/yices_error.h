/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * ERROR MESSAGE BASED ON THE CURRENT ERROR REPORT
 */

#ifndef __YICES_ERROR_H
#define __YICES_ERROR_H

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
