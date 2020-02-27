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

/*
 * PRETTY PRINTER FOR TYPES USING THE SMT2 FORMAT
 */

#ifndef __SMT2_TYPE_PRINTER_H
#define __SMT2_TYPE_PRINTER_H

#include "frontend/smt2/smt2_printer.h"
#include "terms/types.h"

/*
 * Print type tau using the given pretty printer
 * - this is equivalent to pp_type in the default type_printer
 * - tau must be defined in tbl
 */
extern void smt2_pp_type(smt2_pp_t *printer, type_table_t *tbl, type_t tau);

#endif

