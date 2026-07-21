/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */
 
#ifndef NA_PLUGIN_H_
#define NA_PLUGIN_H_

#include "mcsat/plugin.h"

/** Allocate a new na plugin and setup the plugin-interface method */
plugin_t* na_plugin_allocator(void);

#endif /* NA_PLUGIN_H_ */
