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
 * PRINT BOOLEAN GATE STRUCTURES
 */

#ifndef __GATES_PRINTER_H
#define __GATES_PRINTER_H

#include <stdio.h>

#include "solvers/cdcl/gates_hash_table.h"

extern void print_boolgate(FILE *f, boolgate_t *g);
extern void print_boolgate_list(FILE *f, lnkgate_t *list);
extern void print_boolgate_levlist(FILE *f, levlist_t *lv);
extern void print_gate_table_stack(FILE *f, gate_table_t *tbl);
extern void print_gate_table_htbl(FILE *f, gate_table_t *tbl);
extern void print_gate_table(FILE *f, gate_table_t *tbl);

#endif /* __GATES_PRINTER_H */
