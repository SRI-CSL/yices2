/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#ifndef BV_PLUGIN_H_
#define BV_PLUGIN_H_

#include "mcsat/plugin.h"

/** Allocate a new BV plugin and setup the plugin-interface method */
plugin_t* bv_plugin_allocator(void);

#endif /* BV_PLUGIN_H_ */
