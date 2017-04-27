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
 * Help command for Yices
 */

#ifndef __YICES_HELP_H
#define __YICES_HELP_H

#include <stdio.h>

/*
 * Print help on the given topic (on file f)
 * - f must be open and writable
 * - if topic is NULL, a generic help is printed
 */
extern void show_help(FILE *f, const char *topic);

#endif /* __YICES_HELP_H */
