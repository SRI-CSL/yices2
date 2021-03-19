/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */


#include "context/context_types.h"
#include "exists_forall/efsolver.h"
#include "exists_forall/ef_analyze.h"
#include "exists_forall/ef_client.h"
#include "frontend/common/tables.h"


/*
 * Table to convert  smt_status to a string
 */
const char* const status2string[NUM_SMT_STATUSES] = {
  "idle",
  "searching",
  "unknown",
  "sat",
  "unsat",
  "interrupted",
  "error",
};


/*
 * Conversion of EF preprocessing codes to string
 */
const char * const efcode2error[NUM_EF_CODES] = {
  "no error",
  "uninterpreted functions are not supported by the exists/forall solver",
  "invalid quantifier nesting (not an exists/forall problem)",
  "non-atomic universal variables",
  "non-atomic existential variables",
  "skolemization failed",
  "internal error",
};


/*
 * Table to convert  ef-solver status to a string
 */
const char* const ef_status2string[NUM_EF_STATUSES] = {
  "idle",
  "searching",
  "unknown",
  "sat",
  "unsat",
  "interrupted",
  // error codes:
  "subst error",
  "tval error",
  "check error",
  "assert error",
  "model error",
  "implicant error", 
  "projection error",
  "status error",
};

/*
 * Conversion of internalization code to an error message
 */
const char * const code2error[NUM_INTERNALIZATION_ERRORS] = {
  "no error",
  "internal error",
  "type error",
  "formula contains free variables",
  "logic not supported",
  "the context does not support uninterpreted functions",
  "the context does not support scalar types",
  "the context does not support tuples",
  "the context does not support uninterpreted types",
  "the context does not support arithmetic",
  "the context does not support bitvectors",
  "the context does not support function equalities",
  "the context does not support quantifiers",
  "the context does not support lambdas",
  "not an IDL formula",
  "not an RDL formula",
  "non-linear arithmetic not supported",
  "division by zero is not supported",
  "too many variables for the arithmetic solver",
  "too many atoms for the arithmetic solver",
  "arithmetic solver exception",
  "bitvector solver exception",
  "formula not supported by the mc-sat solver",
};

/*
 * Why model construction failed in the exists/forall solver.
 */
const char *const efmodelcode2error[NUM_EFMODEL_ERROR_CODES] = {
  "No error",
  "No model, did not find a solution",
  "Can't build a model. Call the exists forall solver first"
};

