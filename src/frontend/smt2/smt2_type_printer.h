/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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

