/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */
 
#ifndef BOOL_PLUGIN_H_
#define BOOL_PLUGIN_H_

#include "mcsat/plugin.h"

/** Allocate a new bool plugin and setup the plugin-interface method */
plugin_t* bool_plugin_allocator(void);

#endif /* BOOL_PLUGIN_H_ */
