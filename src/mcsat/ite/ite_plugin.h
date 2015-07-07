/*
 * ite_plugin.h
 *
 *  Created on: May 20, 2014
 *      Author: dejan
 */

#ifndef ITE_PLUGIN_H_
#define ITE_PLUGIN_H_

#include "mcsat/plugin.h"

/** Allocate a new bool plugin and setup the plugin-interface method */
plugin_t* ite_plugin_allocator();

#endif /* ITE_PLUGIN_H_ */
