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

#include "options.h"

#include <stddef.h>

extern void init_mcsat_options(mcsat_options_t *opts) {
  opts->na_nlsat = false;
  opts->na_mgcd = false;
  opts->na_bound = false;
  opts->na_bound_min = -1;
  opts->na_bound_max = -1;
  opts->bv_var_size = -1;
  opts->model_interpolation = false;
  opts->partial_restart = false;
}

