/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */
 
#pragma once

#include "mcsat/plugin.h"

/** Allocate a new BV plugin and setup the plugin-interface method */
plugin_t* bv_plugin_allocator(void);

