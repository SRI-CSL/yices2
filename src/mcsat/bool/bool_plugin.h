/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#ifndef BOOL_PLUGIN_H_
#define BOOL_PLUGIN_H_

#include "mcsat/plugin.h"

/** Allocate a new bool plugin and setup the plugin-interface method */
plugin_t* bool_plugin_allocator(void);

#endif /* BOOL_PLUGIN_H_ */
