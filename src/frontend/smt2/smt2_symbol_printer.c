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

#include "frontend/smt2/smt2_lexer.h"
#include "frontend/smt2/smt2_symbol_printer.h"

void smt2_pp_symbol(smt2_pp_t *printer, const char *name) {
  if (symbol_needs_quotes(name)) {
    pp_qstring(&printer->pp, '|', '|', name);
  } else {
    pp_string(&printer->pp, name);
  }
}
