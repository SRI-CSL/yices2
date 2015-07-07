/*
 * cnf_plugin.h
 *
 *  Created on: May 13, 2014
 *      Author: dejan
 */

#ifndef BOOL_PLUGIN_H_
#define BOOL_PLUGIN_H_

#include "mcsat/plugin.h"

/** Allocate a new bool plugin and setup the plugin-interface method */
plugin_t* bool_plugin_allocator();

#endif /* BOOL_PLUGIN_H_ */
