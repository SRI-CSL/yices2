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
 * Top-level call to yices_main:
 * - this is used to call yices_main from Lisp
 *   using a foreign function mechanism.
 */

#ifndef __YICES_REVAL_H
#define __YICES_REVAL_H


/*
 * Yices-main: takes two arguments like an ordinary main
 */
extern int yices_main(int argc, char *argv[]);


/*
 * Run-yices: like yices_main with no arguments
 */
extern int run_yices(void);


#endif
