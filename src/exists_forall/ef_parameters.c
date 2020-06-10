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
 * Parameters for the EF client.
 */

#include "exists_forall/ef_parameters.h"

void init_ef_params(ef_param_t *p) {
  p->flatten_iff = false;
  p->flatten_ite = false;
  p->gen_mode = EF_GEN_AUTO_OPTION;
  p->max_samples = 0;
  p->max_iters = 10000;
  p->max_numlearnt = 10;
}

