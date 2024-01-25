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

#ifndef FF_PLUGIN_EXPLAIN_H
#define FF_PLUGIN_EXPLAIN_H

#include "utils/int_vectors.h"

typedef struct ff_plugin_s ff_plugin_t;

void ff_plugin_check_conflict(ff_plugin_t* ff, ivector_t* core);

void ff_plugin_explain_conflict(ff_plugin_t* ff, const ivector_t* core, const ivector_t* lemma_reasons, ivector_t* conflict);

#endif /* FF_PLUGIN_EXPLAIN_H */
