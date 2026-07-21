/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */
 
#ifndef UF_PLUGIN_H_
#define UF_PLUGIN_H_

#include "mcsat/plugin.h"

/** Allocate a new UF plugin and setup the plugin-interface method */
plugin_t* uf_plugin_allocator(void);

#endif /* UF_PLUGIN_H_ */
