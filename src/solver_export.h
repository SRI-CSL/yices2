/*
 * Support to export a solver state in Yices 1 format
 */

#ifndef __SOLVER_EXPORT_H
#define __SOLVER_EXPORT_H

#include <stdio.h>

#include "smt_core.h"
#include "egraph_types.h"
#include "idl_floyd_warshall.h"
#include "rdl_floyd_warshall.h"
#include "simplex_types.h"
#include "context.h"

extern void export_simplex(FILE *f, simplex_solver_t *solver);
extern void export_idl(FILE *f, idl_solver_t *solver);
extern void export_rdl(FILE *f, rdl_solver_t *solver);


#endif /* __SOLVER_EXPORT_H */
