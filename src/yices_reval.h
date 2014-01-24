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
