/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <stdarg.h>

#include "yices.h"
#include "yices_exit_codes.h"


void __attribute__((noreturn)) freport_bug(FILE *fp, const char *format, ...) {
  va_list p;

  fprintf(fp, "\n*************************************************************\n");
  fprintf(fp, "FATAL ERROR: ");
  va_start(p, format);
  (void) vfprintf(fp, format, p); // added void to shush coverity
  va_end(p);
  fprintf(fp, "\n*************************************************************\n");
  fprintf(fp, "Please report this bug to yices-bugs@csl.sri.com.\n");
  fprintf(fp, "To help us diagnose this problem, please include the\n"
                  "following information in your bug report:\n\n");
  fprintf(fp, "  Yices version: %s\n", yices_version);
  fprintf(fp, "  Build date: %s\n", yices_build_date);
  fprintf(fp, "  Platform: %s (%s)\n", yices_build_arch, yices_build_mode);
  fprintf(fp, "\n");
  fprintf(fp, "Thank you for your help.\n");
  fprintf(fp, "*************************************************************\n\n");
  fflush(fp);

  exit(YICES_EXIT_INTERNAL_ERROR);
}


