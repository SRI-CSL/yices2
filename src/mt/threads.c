/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2019 SRI International.
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

#include <stdio.h>

#include "threads.h"

#ifndef MINGW
#include "threads_posix.c"
#else
#include "threads_win.c"
#endif

void mt_test_usage(int32_t argc, char* argv[]){
  fprintf(stdout, "usage:\n%s <number of threads>\n", argv[0]);
  fprintf(stdout,"\tnumber of threads = 0: single threaded output to stdout\n"
          "\tnumber of threads > 0: each thread logs to a separate file\n");
}



