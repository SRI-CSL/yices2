/*
 * nra_plugin.h
 *
 *  Created on: Feb 1, 2015
 *      Author: dejan
 */

#ifndef NRA_PLUGIN_H_
#define NRA_PLUGIN_H_

#include "mcsat/plugin.h"

/** Allocate a new nra plugin and setup the plugin-interface method */
plugin_t* nra_plugin_allocator();

#endif /* NRA_PLUGIN_H_ */
