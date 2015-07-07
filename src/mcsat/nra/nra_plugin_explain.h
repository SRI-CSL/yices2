/*
 * nra_plugin_explain.h
 *
 *  Created on: May 28, 2015
 *      Author: dejan
 */

#pragma once

#include "nra_plugin_internal.h"
#include "utils/int_vectors.h"

/**
 * Explain the core in the conflict. Core is a set of constraint variables,
 * and conflict will a set if terms. */
void nra_plugin_explain_conflict(nra_plugin_t* nra, const ivector_t* core, const ivector_t* lemma_reasons, ivector_t* conflict);
