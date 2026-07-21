/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef FF_PLUGIN_EXPLAIN_H
#define FF_PLUGIN_EXPLAIN_H

#include "utils/int_vectors.h"

typedef struct ff_plugin_s ff_plugin_t;

void ff_plugin_explain_conflict(ff_plugin_t* ff, const ivector_t* core, const ivector_t* lemma_reasons, ivector_t* conflict);

#endif /* FF_PLUGIN_EXPLAIN_H */
