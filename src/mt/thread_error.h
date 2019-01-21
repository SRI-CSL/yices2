/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2019 SRI International.
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

#ifndef __THREAD_ERRORS_H
#define __THREAD_ERRORS_H
#include <stdint.h>

#include "yices_types.h"

extern void set_tl_error(int32_t code);

extern int32_t get_tl_error(void);

extern void set_yices_error_code(error_code_t code);

extern error_code_t get_yices_error_code();


#endif /* __THREAD_ERRORS_H */

