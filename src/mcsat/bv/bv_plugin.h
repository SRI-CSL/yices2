/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#pragma once

#include "mcsat/plugin.h"

/** Allocate a new BV plugin and setup the plugin-interface method */
plugin_t* bv_plugin_allocator(void);

