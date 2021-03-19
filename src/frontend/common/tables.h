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
