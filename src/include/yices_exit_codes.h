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
 * On non-recoverable errors, the Yices binary exits with a non-zero status.
 * The status values are defined here for different error conditions.
 * - code = 0 means success
 * - code != 0 means error
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
#define YICES_EXIT_SYSTEM_ERROR    23

#define YICES_EXIT_SUCCESS         EXIT_SUCCESS

#endif /* __YICES_EXIT_CODES_H */
