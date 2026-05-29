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
 
#ifndef BOOL_PLUGIN_H_
#define BOOL_PLUGIN_H_

#include "mcsat/plugin.h"

/** Allocate a new bool plugin and setup the plugin-interface method */
plugin_t* bool_plugin_allocator(void);

/*
 * Append the variables of var's reason clause (other than var) to out_vars.
 * Side-effect free: no activity or clause-score bumping. var must be a
 * Boolean propagation owned by this plugin (caller guarantees this).
 */
void bool_plugin_get_reason_vars(plugin_t* plugin, variable_t var, ivector_t* out_vars);

#endif /* BOOL_PLUGIN_H_ */
