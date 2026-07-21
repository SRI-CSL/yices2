dnl========================================================================
dnl Copyright (c) 2026, SRI International
dnl SPDX-License-Identifier: BSD-3-Clause
dnl
dnl========================================================================

dnl
dnl Configure for Yices
dnl
dnl This builds a platform-dependent configuration
dnl file stored in configs/Makefile.$ARCH
dnl

AC_PREREQ(2.60)
AC_INIT([Yices],[2])

dnl
dnl Our public repository (used if ./configure fails)
dnl
repo_url="https://github.com/SRI-CSL/yices2"

dnl
dnl Save CFLAGS (AC_PROC_CC modifies it)
dnl
saved_cflags=$CFLAGS


dnl
dnl Build platform
dnl --------------
dnl
dnl Changed this (07/12/2012) to allow cross-compilation (patch from
dnl Dave Vitek, from Grammatch).
dnl  build = platform on which we run the build
dnl  host = platform for which we build
dnl
dnl Also changed AC_CHECK_PROG(LD, ..) to AC_CHECK_TOOL(LD, ...) etc.
dnl
AC_CANONICAL_BUILD

AC_SUBST(ARCH)
AC_SUBST(POSIXOS)
POSIXOS=$host_os
ARCH=$host

if test "$POSIXOS" = unknown ; then
   AC_MSG_ERROR([Unknown operating system])
fi


dnl
dnl define SET_MAKE if needed
dnl -------------------------
dnl
AC_PROG_MAKE_SET


dnl
dnl Tools for building Yices
dnl ------------------------
dnl
AC_PROG_SED
AC_PROG_LN_S
AC_PROG_MKDIR_P
AC_PROG_INSTALL

AC_PROG_CC

AC_PROG_RANLIB
AC_PROG_EGREP
AC_CHECK_TOOL(LD,ld,ld)
AC_CHECK_TOOL(AR,ar,ar)
AC_CHECK_TOOL(STRIP,strip,strip)

#
# gperf generates source files. Better
# to keep AC_CHECK_PROG rather than AC_CHECK_TOOL
#
AC_CHECK_PROG(GPERF,gperf,gperf,nogperf)



#
# CHECK GPERF
# -----------
# the src/Makefile uses command-line options that appeared in version 3.0
# of gperf
#
if test "$GPERF" = nogperf; then
  AC_MSG_ERROR([*** gperf not found. gperf version 3.0 or higher is required to build Yices ***])
else
  AC_MSG_CHECKING([gperf version])
  gperfversion=`"$GPERF" --version 2>&1 | awk '/^GNU/ { print $3 }'`
  case $gperfversion in
  0.* | 1.* | 2.* )
     AC_MSG_RESULT([${gperfversion}])
     AC_MSG_ERROR([*** found $GPERF version $gperfversion but version 3.0 or higher is required ***])
     ;;
   3.*)
     AC_MSG_RESULT([${gperfversion}])
     ;;
  *)
     AC_MSG_RESULT([${gperfversion}])
     AC_MSG_WARN([*** Unexpected $GPERF output. Cannot determine version. Continuing anyway ***]);;
  esac
fi



dnl
dnl Check whether the C compiler accepts the flag -fno-stack-protector
dnl -------------------------------------------------------------------
dnl
dnl Several Linux distributions (also Darwin) come with GCC that has
dnl -fstack-protector enabled by default. This may cause problems at
dnl link time on the user machine (if the user doesn't have the right
dnl runtime libraries). The symptom is:
dnl    undefined reference to '__stack_chk_fail'
dnl To avoid this, we try to give flag -fno-stack-protector when
dnl compiling Yices in release mode. However, this flag is not supported
dnl by older versions of GCC (e.g., gcc-4.0.x don't seem to have it)
dnl
dnl The following test attempts to determine whether the C compiler
dnl supports -fno-stack-protector. If it does, we set variable
dnl NO_STACK_PROTECTOR to -fno-stack-protector.  Otherwise, we leave
dnl NO_STACK_PROTECTOR empty
dnl
NO_STACK_PROTECTOR=""
AC_MSG_CHECKING([whether $CC accepts option -fno-stack-protector])
if $CC -fno-stack-protector -c -xc - -o /dev/null < /dev/null > /dev/null 2>&1 ; then
   NO_STACK_PROTECTOR="-fno-stack-protector"
   AC_MSG_RESULT(yes)
else
   AC_MSG_RESULT(no)
fi;
AC_SUBST(NO_STACK_PROTECTOR)


dnl
dnl Check for endianness
dnl --------------------
dnl
WORDS_BIGENDIAN=""
AC_C_BIGENDIAN([WORDS_BIGENDIAN=yes],[WORDS_BIGENDIAN=no],[WORDS_BIGENDIAN=yes])
AC_SUBST(WORDS_BIGENDIAN)

dnl
dnl CHECK_THREAD_LOCAL
dnl ------------------
dnl check whether we can declare variables with the __thread
dnl attribute. If not we assume the platform doesn't support
dnl thread-local storage.
dnl
dnl result: $has_tls is "yes" if the __thread attribute is supported
dnl         $has_tls is "no" otherwise
dnl
AC_DEFUN([CSL_CHECK_THREAD_LOCAL],
[
save_cppflags=$CPPFLAGS
save_libs=$LIBS
AC_MSG_CHECKING([for thread-local storage support])
AC_RUN_IFELSE(
[AC_LANG_PROGRAM([[__thread int test;]],
                 [[]])],
has_tls=yes,has_tls=no,has_tls=no)
AC_MSG_RESULT([$has_tls])
#
# restore CPPFLAGS and LIBS
#
CPPFLAGS=$save_cppflags
LIBS=$save_libs
])



dnl
dnl GMP Libraries
dnl -------------
dnl
dnl We need as many as three different versions of GMP:
dnl
dnl To build static executables and libraries, we link with the
dnl default libgmp.a (usually /usr/local/lib/libgmp.a).
dnl
dnl To construct the yices library (libyices.so) with GMP included,
dnl we need a version of libgmp.a that's position independent code.
dnl On systems where -fPIC is not the default, we must build
dnl a specific version of GMP from the source, using option CFLAG=-fPIC.
dnl
dnl To build dynamic executables and libraries without GMP included,
dnl we need a a dynamic version of the GMP library (e.g., /usr/local/lib/libgmp.so).
dnl
dnl On mingw and cygwin, dynamic and static GMP libraries do not coexist well.
dnl They must be installed in different locations and use different gmp.h files.
dnl
dnl To deal with this, the build Makefiles use the following variables:
dnl   STATIC_GMP = full path to a static version of gmp (e.g., /usr/local/lib/libgmp.a)
dnl   STATIC_GMP_INCLUDE_DIR = directory where a 'gmp.h' compatible with STATIC_GMP is located
dnl                            (or empty if 'gmp.h' is in a standard place)
dnl
dnl   PIC_GMP = full path to a libgmp.a that's PIC code
dnl   PIC_GMP_INCLUDE_DIR = directory where a 'gmp.h' header file compatible with PIC_GMP
dnl                         is located
dnl
dnl By default, the configure script searches for a usable STATIC_GMP in default
dnl locations and sets PIC_GMP to the same thing as STATIC_GMP.
dnl
dnl If the configure script does not find STATIC_GMP or if the defaults are
dnl incorrect, the right libraries can be given as options to ./configure:
dnl
dnl --with-static-gmp=full-path-to-libgmp.a for static linking
dnl --with-static-gmp-include-dir=corresponding directory for gmp.h
dnl
dnl --with-pic-gmp=full-path-to-relocatable-libgmp.a
dnl --with-pic-gmp-include-dir=directory where the corresponding gmp.h resides
dnl
static_libgmp=""
AC_ARG_WITH([static-gmp],
   [AS_HELP_STRING([--with-static-gmp=<path>],[Full path to a static GMP library (e.g., libgmp.a)])],
   [if test "x$withval" = x; then
      AC_MSG_WARN([--with-static-gmp was used but no path was given. Using defaults])
    else
      static_libgmp=$withval
    fi
   ],
   [])

static_includegmp=""
AC_ARG_WITH([static-gmp-include-dir],
   [AS_HELP_STRING([--with-static-gmp-include-dir=<directory>],
            [Directory of include file "gmp.h" compatible with static GMP library])],
   [if test "x$withval" = x; then
      AC_MSG_WARN([--with-static-gmp-include-dir was used but no directory was given. Using defaults])
    else
      static_includegmp=$withval
    fi
   ],
   [])


pic_libgmp=""
AC_ARG_WITH([pic-gmp],
   [AS_HELP_STRING([--with-pic-gmp=<path>],[Full path to a relocatable GMP library (e.g., libgmp.a)])],
   [if test "x$withval" = x; then
      AC_MSG_WARN([--with-pic-gmp was used but no path was given. Using defaults])
    else
      pic_libgmp=$withval
    fi
   ],
   [])

pic_includegmp=""
AC_ARG_WITH([pic-gmp-include-dir],
   [AS_HELP_STRING([--with-pic-gmp-include-dir=<directory>],
            [Directory of include file "gmp.h" compatible with relocatable GMP library])],
   [if test "x$withval" = x; then
      AC_MSG_WARN([--with-pic-gmp-include-dir was used but no directory was given. Using defaults])
    else
      pic_includegmp=$withval
    fi
   ],
   [])


dnl
dnl Options for mcsat and the libpoly library
dnl -----------------------------------------
dnl --enable-mcsat: add support for MCSAT
dnl
dnl If mcsat is emabled, we provide options to specify
dnl the static libraries, using the same conventions as for GMP.
dnl
use_mcsat="no"
AC_ARG_ENABLE([mcsat],
   [AS_HELP_STRING([--enable-mcsat],[Enable support for MCSAT. This requires the LibPoly library and the CUDD library.])],
   [if test "$enableval" = yes ; then 
      use_mcsat="yes"
      AC_MSG_NOTICE([Enabling support for MCSAT])
    fi],
   [])


static_lpoly=""
AC_ARG_WITH([static-libpoly],
   [AS_HELP_STRING([--with-static-libpoly=<path>],[Full path to libpoly.a])],
   [if test $use_mcsat = "no" ; then
      AC_MSG_WARN([Ignoring option --with-static-libpoly since MCSAT support is disabled])
    else
      if test "x$withval" = x; then
        AC_MSG_WARN([--with-static-poly was used but no path was given. Using defaults])
      else
        static_lpoly=$withval
      fi
    fi
   ],
   [])

static_includelpoly=""
AC_ARG_WITH([static-libpoly-include-dir],
   [AS_HELP_STRING([--with-static-libpoly-include-dir=<directory>],
            [Path to include files compatible with libpoly.a (e.g., /usr/local/include)])],
   [if test $use_mcsat = "no" ; then
      AC_MSG_WARN([Ignoring option --with-static-libpoly-include-dir since MCSAT support is disabled])
    else
      if test "x$withval" = x; then
         AC_MSG_WARN([--with-static-libpoly-include-dir was used but no directory was given. Using defaults])
      else
        static_includelpoly=$withval
      fi
    fi
   ],
   [])


pic_lpoly=""
AC_ARG_WITH([pic-libpoly],
   [AS_HELP_STRING([--with-pic-libpoly=<path>],[Full path to a relocatable libpoly.a])],
   [if test $use_mcsat = "no" ; then
      AC_MSG_WARN([Ignoring option --with-pic-libpoly since MCSAT support is disabled])
    else
      if test "x$withval" = x; then
         AC_MSG_WARN([--with-pic-libpoly was used but no path was given. Using defaults])
      else
         pic_lpoly=$withval
      fi
    fi
   ],
   [])

pic_includelpoly=""
AC_ARG_WITH([pic-libpoly-include-dir],
   [AS_HELP_STRING([--with-pic-libpoly-include-dir=<directory>],
            [Path to include files compatible with the relocatable libpoly.a])],
   [if test $use_mcsat = "no" ; then
      AC_MSG_WARN([Ignoring option --with-pic-libpoly-include-dir since MCSAT support is disabled])
    else
      if test "x$withval" = x; then
         AC_MSG_WARN([--with-pic-libpoly-include-dir was used but no directory was given. Using defaults])
      else
         pic_includelpoly=$withval
      fi
    fi
   ],
   [])


dnl
dnl Static delegate archive inputs
dnl ------------------------------
dnl Delegate selection is still controlled by CPPFLAGS=-DHAVE_...
dnl in this release. These options only provide the raw static
dnl delegate archives and headers needed by static delegate builds.
dnl
static_depdir='$(BUILD)/static_deps'
AC_ARG_WITH([static-dep-dir],
   [AS_HELP_STRING([--with-static-dep-dir=<directory>],
            [Directory where make writes generated static dependency artifacts])],
   [if test "x$withval" = x; then
      AC_MSG_WARN([--with-static-dep-dir was used but no directory was given. Using defaults])
    else
      case "$withval" in
        /*) static_depdir=$withval ;;
        *) static_depdir=`pwd`/$withval ;;
      esac
    fi
   ],
   [])

static_delegates=""
AC_ARG_WITH([static-delegates],
   [AS_HELP_STRING([--with-static-delegates=<directory>],
            [Directory containing raw static delegate archives])],
   [if test "x$withval" = x; then
      AC_MSG_WARN([--with-static-delegates was used but no directory was given. Ignoring])
    else
      case "$withval" in
        /*) static_delegates=$withval ;;
        *) static_delegates=`pwd`/$withval ;;
      esac
    fi
   ],
   [])

static_include_delegates=""
AC_ARG_WITH([static-delegates-include-dir],
   [AS_HELP_STRING([--with-static-delegates-include-dir=<directory>],
            [Directory containing delegate headers for static builds])],
   [if test "x$withval" = x; then
      AC_MSG_WARN([--with-static-delegates-include-dir was used but no directory was given. Ignoring])
    else
      case "$withval" in
        /*) static_include_delegates=$withval ;;
        *) static_include_delegates=`pwd`/$withval ;;
      esac
    fi
   ],
   [])


dynamic_delegates_assume_hidden_kitten="no"
AC_ARG_ENABLE([dynamic-delegates-assuming-hidden-kitten],
   [AS_HELP_STRING([--enable-dynamic-delegates-assuming-hidden-kitten],
            [Allow dynamic CaDiCaL+Kissat targets assuming delegate shared libraries hide private Kitten symbols])],
   [if test "$enableval" = yes ; then
      dynamic_delegates_assume_hidden_kitten="yes"
      AC_MSG_NOTICE([Assuming dynamic delegate libraries hide private Kitten symbols])
    fi],
   [])



dnl
dnl Option to enable thread-safety
dnl ------------------------------
dnl --enable-thread-safety
dnl
dnl The default is don't build thread safe. If the --enable-thread-safety 
dnl is given, we check whether thread-local storage is supported.
dnl
thread_safe="no"
AC_ARG_ENABLE([thread-safety],
   [AS_HELP_STRING([--enable-thread-safety],[Build in thread-safe mode.])],
   [if test "$enableval" = yes ; then
      thread_safe="yes"
      AC_MSG_NOTICE([Enabling thread-safe build])
    fi],
   [])




dnl
dnl CSL_COLLECT_LIBRARY_PATHS
dnl -------------------------
dnl Sets variable search_libs to a default list of directories in which to search for libraries.
dnl The list include /usr/local/lib /usr/lib /lib + directories found by
dnl ld --verbose + LD_LIBRARY_PATH + DYLD_LIBRARY_PATH + LDFLAGS if non-empty.
dnl
AC_DEFUN([CSL_COLLECT_LIBRARY_PATHS],
[
#
# Some (non-GNU) versions of ld do not recognize --verbose
#
# Also, some versions of GNU ld have things like SEARCH_DIR(=/usr/local/lib32)
# and the '=' causes us trouble.
#
# man ld says
#   If searchdir begins with "=", then the "=" will be replaced by the
#   sysroot prefix, a path specified when the linker is configured.
#
# We ignore this here. If the search dir starts with =, we remove =
#
# NOTE: this sed command uses \? which, is a GNU extension.
#
if ld --verbose > /dev/null 2>&1; then
   base_libs=`ld --verbose | grep SEARCH_DIR | sed -e 's,SEARCH_DIR(\"\?=\?,,g' -e 's,\"\?);,,g' | sed -e 's,SEARCH_DIR(\",,g' -e 's,\");,,g' `
else
   base_libs=""
fi
#
# Add LD_LIBRARY_PATH or DYLD_LIBRARY_PATH if they are defined
#
if test "x$LD_LIBRARY_PATH" != x; then
   aux_libs=`echo $LD_LIBRARY_PATH | sed -e 's,:, ,g'`
else
   if test "x$DYLD_LIBRARY_PATH" != x; then
      aux_libs=`echo $DYLD_LIBRARY_PATH | sed -e 's,:, ,g'`
   else
      aux_libs=""
   fi
fi
search_libs="$aux_libs $base_libs /usr/local/lib /usr/lib /lib"
#
# Add other libraries from $LDFLAGS
#
prev_l_opt=false
for ld_arg in $LDFLAGS; do
  if test "$prev_l_opt" = "true"; then
     search_libs=" $ld_arg $search_libs"
  else
     if test "$ld_arg" = "-L"; then
        prev_l_opt=true
     else
        libprefix=`echo $ld_arg | cut -c -2`
        body=`echo $ld_arg | cut -c 3-`
        if test "$libprefix" = "-L"; then
          search_libs=" $body $search_libs"
        else
          libprefix=`echo $ld_arg | cut -c -15`
          body=`echo $ld_arg | cut -c 16-`
          if test "$libprefix" = "--library-path"; then
            search_libs=" $body $search_libs"
          fi
        fi
     fi
  fi
done
])


dnl
dnl CSL_CHECK_LIB_PATH(path,option)
dnl ----------------------------------
dnl path should be the full path to a static library.
dnl this checks whether the given file exists. Prints an
dnl error and exit otherwise.
dnl
dnl If the test succeeds, set variable testlib to path.
dnl
AC_DEFUN([CSL_CHECK_LIB_PATH],
[
testlib=""
AC_MSG_CHECKING([for $1])
if test -f $1; then
  AC_MSG_RESULT(found)
  testlib=$1
else
  AC_MSG_RESULT(no)
  AC_MSG_ERROR([*** $1 was not found: Check option $2 ***])
fi
])


dnl
dnl CSL_CHECK_HEADER(header,includedir,option)
dnl ----------------------------------------
dnl check whether a header file like 'gmp.h' is present in includedir
dnl set variable $testincludedir to includedir if so
dnl exit otherwise.
dnl if includedir is empty, just set testincludedir to empty string too
dnl
dnl option must be the '--with-...-include-dir from which includedir was given
dnl it's used to print the error message.
dnl
AC_DEFUN([CSL_CHECK_HEADER],
[
testincludedir=""
if test "x$2" != x; then
   if test -d "$2" ; then
     if test -f "$2/$1" ; then
        testincludedir="$2"
     else
        AC_MSG_ERROR([*** $1 not found in $2. Check option $3 ***])
     fi
  else
     AC_MSG_ERROR([*** directory $2 not found. Check option $3 ***])
  fi
fi
])


dnl
dnl CSL_DELEGATE_ENABLED(symbol)
dnl ----------------------------
dnl Check whether CPPFLAGS contains -Dsymbol or -Dsymbol=value.
dnl Sets delegate_enabled to yes or no.
dnl
AC_DEFUN([CSL_DELEGATE_ENABLED],
[
delegate_enabled=no
prev_d_opt=no
for cpp_arg in $CPPFLAGS; do
  if test "$prev_d_opt" = yes; then
     if test "$cpp_arg" = "$1"; then
        delegate_enabled=yes
     else
        case "$cpp_arg" in
          $1=*) delegate_enabled=yes ;;
        esac
     fi
     prev_d_opt=no
  else
     case "$cpp_arg" in
       -D$1|-D$1=*) delegate_enabled=yes ;;
       -D) prev_d_opt=yes ;;
     esac
  fi
done
])


dnl
dnl CSL_CHECK_STATIC_DELEGATE_ARCHIVE(directory,archive)
dnl ----------------------------------------------------
dnl Check that directory/archive exists and set testlib to the full path.
dnl
AC_DEFUN([CSL_CHECK_STATIC_DELEGATE_ARCHIVE],
[
testlib="$1/$2"
AC_MSG_CHECKING([for $2 in $1])
if test -f "$testlib"; then
   AC_MSG_RESULT(found)
else
   AC_MSG_RESULT(no)
   AC_MSG_ERROR([*** $testlib was not found: check option --with-static-delegates ***])
fi
])



dnl
dnl CSL_CHECK_GMP(libgmp,includedir)
dnl --------------------------------
dnl attempt to compile a test program that calls a gmp function
dnl set run_ok to "yes" if the program executes and exits with 0
dnl set run_ok to "no" otherwise
dnl
dnl libgmp must be the full-path name to the library to test
dnl includedir must be the directory where the corresponding 'gmp.h'
dnl can be found
dnl
AC_DEFUN([CSL_CHECK_GMP],
[
save_cppflags=$CPPFLAGS
save_libs=$LIBS
#
# Add -I option to CPPFLAGS (it must be first)
# Add $1 to LIBS
#
if test "x$2" != x ; then
   CPPFLAGS="-I$2 $CPPFLAGS"
fi
LIBS="$1 -lm"
AC_MSG_CHECKING([whether $1 is usable])
#
# Test program: check whether the GMP version is recent enough
#
AC_RUN_IFELSE(
[AC_LANG_PROGRAM([[
#include <gmp.h>

mpz_t tst;
]],
[[
mpz_init(tst);
mpz_clear(tst);
if ((__GNU_MP_VERSION < 4) ||
    ((__GNU_MP_VERSION == 4) && (__GNU_MP_VERSION_MINOR < 1))) {
    return 1;
  }
]])

],run_ok=yes,run_ok=no,run_ok=yes)
AC_MSG_RESULT([$run_ok])
#
# restore CPPFLAGS and LIBS
#
CPPFLAGS=$save_cppflags
LIBS=$save_libs
])



dnl
dnl CSL_CHECK_STATIC_GMP(libgmp,includedir)
dnl ------------------------------------
dnl try to find the full path to a usable libgmp.a, use $1 if not empty.
dnl if $2 is not empty, then the checks are compiled with -I$2
dnl if everything works, then set STATIC_GMP to the fullpath for libgmp.a
dnl and set STATIC_GMP_INCLUDE_DIR to $2
dnl
dnl
AC_DEFUN([CSL_CHECK_STATIC_GMP],
[
AC_MSG_NOTICE([Trying to find a usable libgmp.a])
CSL_CHECK_HEADER([gmp.h],$2,--with-static-gmp-include-dir)
#
# if $1 is not given, search for it in library paths
#
if test -z "$1"; then
   CSL_COLLECT_LIBRARY_PATHS
   #
   # now $search_libs contains all the directories to search
   #
   AC_MSG_NOTICE([Searching in $search_libs])
   for ldir in $search_libs; do
       AC_MSG_CHECKING([for libgmp.a in $ldir])
       if test -f $ldir/libgmp.a; then
          AC_MSG_RESULT(found)
          testlib=$ldir/libgmp.a
          CSL_CHECK_GMP($testlib,$testincludedir)
          if test $run_ok = yes; then
            STATIC_GMP=$testlib
            STATIC_GMP_INCLUDE_DIR=$testincludedir
            break
          fi
       else
         AC_MSG_RESULT(no)
       fi
   done
#
#
else
  #
  # User gave option --with-static-gmp=xxx
  # Check whether the specified xxx actually works
  #
  CSL_CHECK_LIB_PATH($1,--with-static-gmp)
  CSL_CHECK_GMP($testlib,$testincludedir)
  if test $run_ok = yes; then
     STATIC_GMP=$testlib
     STATIC_GMP_INCLUDE_DIR=$testincludedir
  else
     AC_MSG_ERROR([*** $1 does not appear to be usable: check option --with-static-gmp ***])
  fi
fi

if test "x$STATIC_GMP" = x; then
   AC_MSG_WARN([*** No usable libgmp.a library was found ***])
fi
])



dnl
dnl CSL_CHECK_LIBPOLY(libpoly,includedir,libs)
dnl ------------------------------------------
dnl attempt to compile and run a test program that calls libpoly
dnl set run_ok to "yes" if the program executes and exits with 0.
dnl set run_ok to "no" otherwise.
dnl
dnl libpoly must be the full-path name to the library to test.
dnl includedir must be a directory with 'poly/polyn.h' can be found.
dnl libs may contain GMP libraries to use
dnl
AC_DEFUN([CSL_CHECK_LIBPOLY],
[
save_cppflags=$CPPFLAGS
save_libs=$LIBS
#
# Add the -I option to CPPFLAGS
# Add $1 then $3 to LIBS
#
if test "x$2" != x ; then
   CPPFLAGS="-I$2 $CPPFLAGS"
fi
LIBS="$1"
if test "x$3" != x ; then
   LIBS="$LIBS $3"
fi
AC_MSG_CHECKING([whether $1 is usable])
#
# Test program
#
AC_RUN_IFELSE(
[AC_LANG_PROGRAM([[
#include <poly/variable_db.h>
#include <poly/variable_order.h>
#include <poly/polynomial_context.h>
#include <poly/polynomial.h>
]],
[[
lp_variable_db_t* var_db = lp_variable_db_new();
lp_variable_order_t* var_order = lp_variable_order_new();
lp_polynomial_context_t* ctx = lp_polynomial_context_new(lp_Z, var_db, var_order);
lp_polynomial_t* p = lp_polynomial_new(ctx);
lp_polynomial_delete(p);
lp_polynomial_context_detach(ctx);
lp_variable_order_detach(var_order);
lp_variable_db_detach(var_db);
]])

],run_ok=yes,run_ok=no,run_ok=no)
AC_MSG_RESULT([$run_ok])
#
# restore CPPFLAGS and LIBS
#
CPPFLAGS=$save_cppflags
LIBS=$save_libs
])


dnl
dnl CSL_CHECK_STATIC_LIBPOLY(libpoly,includedir)
dnl --------------------------------------------
dnl Try to find a usable libpoly.a.
dnl If $1 is not empty, it's assumed to be the full path to libpoly.a
dnl If $2 is not empty, it's assumed to be the path to the
dnl corresponding include directory (i.e., the relevant headers are
dnl assumed to be in $2/poly/...
dnl If $3 is not empty, it's the GMP library to use
dnl
dnl If the test succeeds. then this macro sets STATIC_LIBPOLY to
dnl the full path for libpoly.a and STATIC_LIBPOLY_INCLUDE_DIR to $2.
dnl
AC_DEFUN([CSL_CHECK_STATIC_LIBPOLY],
[
AC_MSG_NOTICE([Searching for a usable libpoly.a])
CSL_CHECK_HEADER([poly/polynomial.h],$2,--with-static-libpoly-include-dir)
#
# If $1 is empty search for it in the
#
if test -z "$1" ; then
   CSL_COLLECT_LIBRARY_PATHS
   #
   # $search_libs contains the directories to search
   #
   AC_MSG_NOTICE([Searching in $search_libs])
   for ldir in $search_libs ; do
      AC_MSG_CHECKING([for libpoly.a in $ldir])
      if test -f $ldir/libpoly.a ; then
         AC_MSG_RESULT(found)
         testlib=$ldir/libpoly.a
         CSL_CHECK_LIBPOLY($testlib,$testincludedir,$3)
         if test $run_ok = yes ; then
            STATIC_LIBPOLY=$testlib
            STATIC_LIBPOLY_INCLUDE_DIR=$testincludedir
            break
         fi
      else
         AC_MSG_RESULT(no)
      fi
   done
#
else
  # got --with-static-libpoly=xxxx
  CSL_CHECK_LIB_PATH($1,--with-static-libpoly)
  CSL_CHECK_LIBPOLY($testlib,$testincludedir,$3)
  if test $run_ok = yes; then
     STATIC_LIBPOLY=$testlib
     STATIC_LIBPOLY_INCLUDE_DIR=$testincludedir
  else
     AC_MSG_ERROR([*** $1 does not appear to be usable: check option --with-static-libpoly ***])
  fi
fi

if test "x$STATIC_LIBPOLY" = x; then
   AC_MSG_WARN([*** No usable libpoly.a library was found ***])
fi
])


#
# CHECK LIBRARIES
# ---------------
#
AC_LANG([C])

#
# We must search for the static versions first
# since other tests may modify $LIBS and $CPPFLAGS
#
STATIC_GMP=""
STATIC_GMP_INCLUDE_DIR=""
AC_SUBST(STATIC_GMP)
AC_SUBST(STATIC_GMP_INCLUDE_DIR)
CSL_CHECK_STATIC_GMP($static_libgmp,$static_includegmp)

#
# Position-independent static version of GMP
#
PIC_GMP="$STATIC_GMP"
PIC_GMP_INCLUDE_DIR="$STATIC_GMP_INCLUDE_DIR"
AC_SUBST(PIC_GMP)
AC_SUBST(PIC_GMP_INCLUDE_DIR)
if test "x$pic_libgmp" != x ; then
  #
  # --with-pic-gmp was given on the command line
  #
  CSL_CHECK_HEADER([gmp.h],$pic_includegmp,--with-pic-gmp-include-dir)
  CSL_CHECK_LIB_PATH($pic_libgmp,--with-pic-gmp)
  CSL_CHECK_GMP($testlib,$testincludedir)
  if test $run_ok = yes; then
    PIC_GMP=$testlib
    PIC_GMP_INCLUDE_DIR=$testincludedir
  else
    AC_MSG_ERROR([*** $testlib does not appear to be usable: check option --with-pic-gmp ***])
  fi
fi


#
# We need -lm (for fclassify)
#
AC_CHECK_LIB([m], [main], [], [])

#
# MCSAT SUPPORT
# -------------
ENABLE_MCSAT="$use_mcsat"
AC_SUBST(ENABLE_MCSAT)

#
# libpoly.a
#
STATIC_LIBPOLY=""
STATIC_LIBPOLY_INCLUDE_DIR=""
AC_SUBST(STATIC_LIBPOLY)
AC_SUBST(STATIC_LIBPOLY_INCLUDE_DIR)
if test $use_mcsat = yes ; then
  if test "x$STATIC_GMP" = x ; then
    auxlibs="-lgmp"
  else
    auxlibs="$STATIC_GMP"
  fi
  CSL_CHECK_STATIC_LIBPOLY($static_lpoly,$static_includelpoly,$auxlibs)
fi

#
# Position-independent static version of LIBPOLY
#
PIC_LIBPOLY="$STATIC_LIBPOLY"
PIB_LIBPOLY_INCLUDE_DIR="$STATIC_LIBPOLY_INCLUDE_DIR"
AC_SUBST(PIC_LIBPOLY)
AC_SUBST(PIC_LIBPOLY_INCLUDE_DIR)
if test $use_mcsat = yes ; then
  if test "x$pic_lpoly" != x ; then
     CSL_CHECK_HEADER([poly/polynomial.h],$pic_includelpoly,--with-pic-libpoly-include-dir)
     CSL_CHECK_LIB_PATH($pic_lpoly,--with-pic-lpoly)
     if test "x$PIC_GMP" != x ; then
        auxlibs="$PIC_GMP"
     else
       if test "x$STATIC_GMP" != x ; then
         auxlibs="$STATIC_GMP"
       else
         auxlibs="-lgmp"
       fi
     fi
     CSL_CHECK_STATIC_LIBPOLY($pic_lpoly,$pic_includelpoly,$auxlibs)
     if test $run_ok = yes; then
       PIC_LIBPOLY=$testlib
       PIC_LIBPOLY_INCLUDE_DIR=$testincludedir
     else
       AC_MSG_ERROR([*** $testlib does not appear to be usable: check option --with-pic-libpoly ***])
     fi
  fi
fi

#
# Static delegate archive inputs
#
HAVE_CADICAL_DELEGATE=no
HAVE_CRYPTOMINISAT_DELEGATE=no
HAVE_KISSAT_DELEGATE=no

CSL_DELEGATE_ENABLED([HAVE_CADICAL])
if test $delegate_enabled = yes ; then
   HAVE_CADICAL_DELEGATE=yes
fi

CSL_DELEGATE_ENABLED([HAVE_CRYPTOMINISAT])
if test $delegate_enabled = yes ; then
   HAVE_CRYPTOMINISAT_DELEGATE=yes
fi

CSL_DELEGATE_ENABLED([HAVE_KISSAT])
if test $delegate_enabled = yes ; then
   HAVE_KISSAT_DELEGATE=yes
fi

STATIC_DEPDIR="$static_depdir"
STATIC_DELEGATES_INCLUDE_DIR=""
STATIC_CADICAL_RAW=""
STATIC_CRYPTOMINISAT_RAW=""
STATIC_KISSAT_RAW=""
STATIC_KISSAT_YICES=""
DYNAMIC_DELEGATES_ASSUME_HIDDEN_KITTEN="$dynamic_delegates_assume_hidden_kitten"

AC_SUBST(HAVE_CADICAL_DELEGATE)
AC_SUBST(HAVE_CRYPTOMINISAT_DELEGATE)
AC_SUBST(HAVE_KISSAT_DELEGATE)
AC_SUBST(STATIC_DEPDIR)
AC_SUBST(STATIC_DELEGATES_INCLUDE_DIR)
AC_SUBST(STATIC_CADICAL_RAW)
AC_SUBST(STATIC_CRYPTOMINISAT_RAW)
AC_SUBST(STATIC_KISSAT_RAW)
AC_SUBST(STATIC_KISSAT_YICES)
AC_SUBST(DYNAMIC_DELEGATES_ASSUME_HIDDEN_KITTEN)

if test "x$static_include_delegates" != x ; then
   if test -d "$static_include_delegates" ; then
      STATIC_DELEGATES_INCLUDE_DIR="$static_include_delegates"
   else
      AC_MSG_ERROR([*** directory $static_include_delegates not found. Check option --with-static-delegates-include-dir ***])
   fi
fi

if test "x$static_delegates" != x ; then
   if test ! -d "$static_delegates" ; then
      AC_MSG_ERROR([*** directory $static_delegates not found. Check option --with-static-delegates ***])
   fi

   if test $HAVE_CADICAL_DELEGATE = yes ; then
      CSL_CHECK_STATIC_DELEGATE_ARCHIVE([$static_delegates],[libcadical.a])
      STATIC_CADICAL_RAW=$testlib
      CSL_CHECK_HEADER([ccadical.h],$static_include_delegates,--with-static-delegates-include-dir)
   fi

   if test $HAVE_CRYPTOMINISAT_DELEGATE = yes ; then
      CSL_CHECK_STATIC_DELEGATE_ARCHIVE([$static_delegates],[libcryptominisat5.a])
      STATIC_CRYPTOMINISAT_RAW=$testlib
      CSL_CHECK_HEADER([cryptominisat5/cmsat_c.h],$static_include_delegates,--with-static-delegates-include-dir)
   fi

   if test $HAVE_KISSAT_DELEGATE = yes ; then
      CSL_CHECK_STATIC_DELEGATE_ARCHIVE([$static_delegates],[libkissat.a])
      STATIC_KISSAT_RAW=$testlib
      STATIC_KISSAT_YICES='$(STATIC_DEPDIR)/libkissat_yices.a'
      CSL_CHECK_HEADER([kissat.h],$static_include_delegates,--with-static-delegates-include-dir)
   fi
else
   if test $HAVE_CADICAL_DELEGATE = yes && test $HAVE_KISSAT_DELEGATE = yes ; then
      AC_MSG_WARN([CaDiCaL and Kissat both export private Kitten symbols. Static builds must configure --with-static-delegates=DIR so make can generate libkissat_yices.a.])
   fi
fi

#
# Default GMP
#
AC_CHECK_LIB(gmp, __gmpz_cmp, [],
    [AC_MSG_ERROR([*** GMP library not found. Try to set LDFLAGS ***])])


#
# Default libpoly
#
if test $use_mcsat = yes ; then
   AC_CHECK_LIB([poly],[lp_polynomial_new], [], [AC_MSG_ERROR([*** libpoly library not found. Try to set LDFLAGS ***])])
fi

#
# Default CUDD
#
if test $use_mcsat = yes ; then 
   AC_CHECK_LIB([cudd],[Cudd_Init], [], [AC_MSG_ERROR([*** CUDD library not found. Try to set LDFLAGS ***])])   
fi


#
# Fix MKDIR_P to an absolute path if it's set to './install-sh -c -d'
# because the Makefiles import its definition via ./configs/make.include.
# This may be unreliable (it won't handle spaces in directory names).
#
# case "$MKDIR_P" in
#   ./install-sh*)
#      curdir=`pwd`
#      new_mkdir_p="$curdir/$MKDIR_P"
#     AC_MSG_WARN([*** MKDIR_P is relative: converting $MKDIR_P to $new_mkdir_p ***])
#     MKDIR_P=$new_mkdir_p
#     ;;
# esac
#

#
# THREAD-SAFE OPTION
# ------------------
#
AC_SUBST(THREAD_SAFE)
if test "x$thread_safe" = xyes ; then
   THREAD_SAFE=1
fi

dnl
dnl Test support for thread-local storage
dnl -------------------------------------
dnl
AC_SUBST(HAVE_TLS)
if test "x$thread_safe" = xyes ; then
   has_tls=""
   CSL_CHECK_THREAD_LOCAL
   if test "x$has_tls" = xyes; then
      HAVE_TLS=1
   else
      AC_MSG_ERROR([Building with --enable-thread-safety requires thread-local storage])
   fi
fi




dnl AC_CHECK_HEADERS([poly/poly.h], [], [AC_MSG_ERROR([*** libpoly headers not found. Try to set CPPFLAGS ***])])


#
# Restore CFLAGS
#
CFLAGS=$saved_cflags

#
# Store config data in ./configs/make.include.$(ARCH)
#
AC_CONFIG_FILES([make.include])
AC_OUTPUT

if test ! -d configs ; then
  AC_MSG_NOTICE([Creating the configs directory])
  AS_MKDIR_P([configs])
fi

if test "x$host" = x ; then
  AC_MSG_NOTICE([Moving make.include to configs/make.include.$build])
  mv make.include "configs/make.include.$build"
else
  AC_MSG_NOTICE([Moving make.include to configs/make.include.$host])
  mv make.include "configs/make.include.$host"
fi
