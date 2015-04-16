/*
 * For compilation on MacOS X versions that support the -m32 and -m64 options.
 * We build and install the GMP libraries:
 * - for 32bits: GMP is configured using ABI=32
 * - for 64bits: GMP is configured using ABI=64
 *
 * On Mac OS X, we use fat libraries to store 64bit/32bit versions in the same file.
 *
 * But the header files for 32bit and 64bit GMP are different, and we must
 * use the right one depending on whether we compile with option -m32 or -m64.
 *
 * One option is to keep two copies of gmp.h in different locations and play
 * with -I .... 
 *
 * Alternative supported by this hack file:
 * - rename gmp.h (32bit) to gmp32.h
 * - rename gmp.h (64bit) to gmp64.h
 * - copy the current file to /usr/local/lib/gmp.h
 * This is a wrapper that attempts to determine the compilation mode then
 * include either gmp32.h or gmp64.h
 *
 * NOTE: This file is not expected/intended to work on other systems
 * than MacOS X. The tests (ULONG_MAX == 0xFFFFFFFFu) and (ULONG_MAX
 * == 0xFFFFFFFFFFFFFFFFu) may not evaluate properly depending on the
 * preprocessor. The C standard says that constant expressions in #if
 * and #elif are evaluated as if all unsigned constants have type
 * uintmax_t (defined in <stdint.h>).
 */

#ifndef __GMP_HACK_H
#define __GMP_HACK_H

#include <limits.h>

#if (ULONG_MAX == 0xFFFFFFFFu)
// #warning "including 32bit '<gmp.h>'"
#include <gmp32.h>
#elif (ULONG_MAX == 0xFFFFFFFFFFFFFFFFu)
// #warning "including 64bit '<gmp.h>'"
#include <gmp64.h>
#else
#error "Could not determine which <gmp.h> to use"
#endif

#endif /* __GMP_HACK_H */
