/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifdef THREAD_SAFE

#ifndef MINGW
#include "yices_locks_posix.c"
#else
#include "yices_locks_win.c"
#endif

#endif
