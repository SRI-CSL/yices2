/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * TABLES TO CONVERT CODES TO STRINGS
 */
#ifndef __FRONTEND_COMMON_TABLES_H
#define __FRONTEND_COMMON_TABLES_H


/*
 * smt_status to string
 */
extern const char* const status2string[];

/*
 * EF preprocessing error codes to string
 */
extern const char * const efcode2error[];

/*
 * ef-solver status to string
 */
extern const char* const ef_status2string[];

/*
 * internalization code to an error message
 */
extern const char * const code2error[];

/*
 * error in ef model construction
 */
extern const char *const efmodelcode2error[];

#endif /* __FRONTEND_COMMON_TABLES_H */
