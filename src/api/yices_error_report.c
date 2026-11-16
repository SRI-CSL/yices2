/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */


#include "api/yices_error_report.h"

#ifndef MINGW
#include "yices_error_report_posix.c"
#else
#include "yices_error_report_win.c"
#endif
