/*
 * EXPORT CLAUSES IN DIMACS FORMAT
 */

#ifndef __SMT_CORE_EXPORTER_H
#define __SMT_CORE_EXPORTED_H

#include <stdint.h>

#include "smt_core.h"


/*
 * Export the clauses of core into the given file:
 * - use the DIMACs CNF format
 * - don't export the learned clauses
 * - return 0 if this works
 * - return -1 if the file can't be opened
 */
extern int32_t smt_core_export(smt_core_t *core, const char *filename);

#endif
