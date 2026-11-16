/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef FF_PLUGIN_H_
#define FF_PLUGIN_H_

#include "mcsat/plugin.h"

/** Allocate a new ff plugin and setup the plugin-interface method */
plugin_t* ff_plugin_allocator(void);

#endif /* FF_PLUGIN_H_ */
