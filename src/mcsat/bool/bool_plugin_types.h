/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */
 
#ifndef BOOL_PLUGIN_TYPES_H_
#define BOOL_PLUGIN_TYPES_H_

#include <stdint.h>

/** Literal is just a variable that might be negated */
typedef int32_t mcsat_literal_t;

/** Null literal */
#define mcsat_literal_null 0

/** Type of clause references */
typedef int32_t clause_ref_t;

/** Null clause */
#define clause_ref_null 0

#endif /* BOOL_PLUGIN_TYPES_H_ */
