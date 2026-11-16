/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */
 
#ifndef ITE_PLUGIN_H_
#define ITE_PLUGIN_H_

#include "mcsat/plugin.h"

/** Allocate a new bool plugin and setup the plugin-interface method */
plugin_t* ite_plugin_allocator(void);

#endif /* ITE_PLUGIN_H_ */
