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
 
#ifndef BOOL_PLUGIN_TYPES_H_
#define BOOL_PLUGIN_TYPES_H_

#include <stdint.h>

/** Literal is just a variable that might be negated */
typedef int32_t mcsat_literal_t;

/** Null literal */
#define mcsat_literal_null 0

/** Type of clause references */
typedef int32_t clause_ref_t;

/** Null clause */
#define clause_ref_null 0

#endif /* BOOL_PLUGIN_TYPES_H_ */
