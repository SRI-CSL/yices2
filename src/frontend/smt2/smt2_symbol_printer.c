/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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
