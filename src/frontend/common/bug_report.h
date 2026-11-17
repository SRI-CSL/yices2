/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * ERROR MESSAGE WHEN SOMETHING GOES BADLY WRONG.
 */
#ifndef __FRONTEND_COMMON_BUG_REPORT_H
#define __FRONTEND_COMMON_BUG_REPORT_H

#include <stdio.h>

extern void __attribute__((noreturn)) freport_bug(FILE *fp, const char *format, ...);

#endif /* __FRONTEND_COMMON_BUG_REPORT_H */
