 /*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * ANSI escape codes (mostly colors)
 *
 * Define 'COLORS' if you want them enabled.
 */

#ifdef COLORS
    #define KRST "\x1B[00m"
    #define KBLD "\x1B[1m"
    #define KITC "\x1B[3m"
    #define KBLK "\x1B[5m"
    #define KRED "\x1B[31m"
    #define KGRN "\x1B[32m"
    #define KYLW "\x1B[33m"
    #define KBLU "\x1B[34m"
    #define KMAJ "\x1B[35m"
    #define KCYN "\x1B[36m"
    #define KWHT "\x1B[37m"
#else
    #define KRST ""
    #define KBLD ""
    #define KITC ""
    #define KBLK ""
    #define KRED ""
    #define KGRN ""
    #define KYLW ""
    #define KBLU ""
    #define KMAJ ""
    #define KCYN ""
    #define KWHT ""
#endif
