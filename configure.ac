dnl
dnl Configure for Yices
dnl
dnl This builds a platform-dependent configuration
dnl file stored in configs/Makefile.$ARCH
dnl

AC_PREREQ(2.60)
AC_INIT([Yices],[2])

dnl
dnl Save CFLAGS (AC_PROC_CC modifies it)
dnl
saved_cflags=$CFLAGS

dnl
dnl Build platform
dnl --------------
dnl
AC_CANONICAL_BUILD

AC_SUBST(ARCH)
AC_SUBST(POSIXOS)
POSIXOS=$build_os
ARCH=$build

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

AC_PROG_CC
AC_PROG_RANLIB
AC_CHECK_PROG(LD,ld,ld)
AC_CHECK_PROG(AR,ar,ar)
AC_CHECK_PROG(STRIP,strip,strip)
AC_CHECK_PROG(GPERF,gperf,gperf,nogperf)



#
# CHECK GPERF
# -----------
# the src/Makefile uses command-line options that appeared in version 3.0
# of gperf
#
if test "$GPERF" = nogperf; then
  AC_MSG_ERROR([*** gperf not found. It is required to build Yices (Version 3.0 or higher) ***])
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
dnl GMP Libraries
dnl -------------
dnl On some systems, dynamic and static GMP libraries do not coexist well.
dnl They must be installed in different locations and used different gmp.h
dnl files. To deal with this, we allow the following command-line options
dnl
dnl --with-gmp=full-path-to-gmplib to used by default
dnl --with-gmp-include-dir=directory for corresponding gmp.h
dnl
dnl --with-static-gmp=full-path-to-libgmp.a for static linking
dnl --with-static-gmp-include-dir=corresponding directory for gmp.h
dnl
dnl If these are not used, configure tries to find usable GMP libraries.
dnl

libgmp=""
AC_ARG_WITH([gmp],
   [AS_HELP_STRING([--with-gmp=<path>],[Full path to a default GMP library])],
   [if test "x$withval" == x; then
      AC_MSG_WARN([--with-gmp was used but no path was given. Using defaults])
    else
      libgmp=$withval
    fi
   ])

includegmp=""
AC_ARG_WITH([gmp-include-dir],
   [AS_HELP_STRING([--with-gmp-include-dir=<directory>],
            [Directory of include file "gmp.h" compatible with default GMP library])],
   [if test "x$withval" == x; then
      AC_MSG_WARN([--with-gmp-include-dir was used but no directory was given. Using defaults])
    else 
      includegmp=$withval
    fi
   ])

static_libgmp=""
AC_ARG_WITH([static-gmp], 
   [AS_HELP_STRING([--with-static-gmp=<path>],[Full path to a static GMP library (e.g., libgmp.a)])],
   [if test "x$withval" == x; then
      AC_MSG_WARN([--with-static-gmp was used but no path was given. Using defaults])
    else
      static_libgmp=$withval
    fi
   ])

static_includegmp=""
AC_ARG_WITH([static-gmp-include-dir],
   [AS_HELP_STRING([--with-static-gmp-include-dir=<directory>],
            [Directory of include file "gmp.h" compatible with static GMP library])],
   [if test "x$withval" == x; then
      AC_MSG_WARN([--with-static-gmp-include-dir was used but no directory was given. Using defaults])
    else 
      static_includegmp=$withval
    fi
   ])




dnl
dnl CSL_CHECK_STATIC_GMP(ligmp,includedir)
dnl ------------------------------------
dnl try to find the full path to a usable libgmp.a, use $1 if not empty.
dnl if $2 is not empty, then the checks are compiled with -I$2 
dnl if everything works, then set STATIC_GMP to the fullpath for libgmp.a
dnl and set STATIC_GMP_INCLUDE_DIR to $2
dnl
dnl Based on CSL_CHECK_DOT_A_LIB
dnl
AC_DEFUN([CSL_CHECK_STATIC_GMP],
[
AC_MSG_NOTICE([Trying to find a usable ligmp.a])
save_cppflags=$CPPFLAGS
save_libs=$LIBS
#
# add extra -I option, must be first in CPPFLAGS
#
testincludedir=""
if test "x$2" != x; then
   if test -f $2/gmp.h; then
      CPPFLAGS="-I$2 $CPPFLAGS"
      testincludedir=$2
   else
      AC_MSG_ERROR([*** gmp.h not found in $2. Check --with-static-gmp-include-dir option ***])
   fi
fi
#
# if $1 is not given, search for it in library paths
# 
if test -z "$1"; then
   #
   # Some (non-GNU) versions of ld do not recognize --verbose
   # use LD_LIBRARY_PATH as default in such cases.
   #
   if ld --verbose > /dev/null 2>&1; then 
      aux_libs=`ld --verbose | grep SEARCH_DIR | sed -e 's,SEARCH_DIR(\"\?,,g' -e 's,\"\?);,,g'`
   else
     if test "x$LD_LIBRARY_PATH" != x; then 
        aux_libs=`echo $LD_LIBRARY_PATH | sed -e 's,:, ,g'`
     else
        aux_libs=""
     fi
   fi
   search_libs="$auxlibs /usr/local/lib /usr/lib /lib"
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
   #
   # now $search_libs contain all the directories to search
   #
   AC_MSG_NOTICE([Searching in $search_libs])
   for ldir in $search_libs; do
       AC_MSG_CHECKING([for libgmp.a in $ldir])
       if test -f $ldir/libgmp.a; then
          AC_MSG_RESULT(found)
          testlib=$ldir/libgmp.a
          LIBS="$testlib -lm"
          AC_MSG_CHECKING([whether $testlib is usable])
          AC_RUN_IFELSE([

#include <gmp.h>
int main() {
   mpz_t tst;
   mpz_init(tst);
   mpz_clear(tst);
   if ((__GNU_MP_VERSION < 4) || (__GNU_MP_VERSION_MINOR < 1)) {
     return 1;
   }
   return 0;
}
         ],run_ok=yes,run_ok=no,run_ok=no)
         #
         AC_MSG_RESULT([$run_ok])
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
  testlib=$1
  AC_MSG_CHECKING([for $testlib])
  if test -f $testlib; then
     AC_MSG_RESULT(found)
     LIBS="$testlib -lm"
     AC_MSG_CHECKING([whether $testlib is usable])
     AC_RUN_IFELSE([

#include <gmp.h>
int main() {
   mpz_t tst;
   mpz_init(tst);
   mpz_clear(tst);
   if ((__GNU_MP_VERSION < 4) || (__GNU_MP_VERSION_MINOR < 1)) {
     return 1;
   }
   return 0;
}
     ],run_ok=yes,run_ok=no,run_ok=no)
     #
     AC_MSG_RESULT([$run_ok])
     if test $run_ok = yes; then
        STATIC_GMP=$testlib
        STATIC_GMP_INCLUDE_DIR=$testincludedir
     else        
        AC_MSG_ERROR([*** $testlib does not appear to be usable: check option --with-static-gmp ***])
     fi
   else
     AC_MSG_RESULT(no)
     AC_MSG_ERROR([*** $testlib was not found: check option --with-static-gmp ***])
   fi
fi
if test "x$STATIC_GMP" = x; then
   AC_MSG_WARN([*** No usable libgmp.a library was found ***])
fi
#
# restore CPPFLAGS and LIBS
#
CPPFLAGS=$save_cppflags
LIBS=$save_libs
])




#
# CHECK GMP LIBRARIES
# -------------------
#
AC_LANG([C])

# Need to search for the static version first
# since other test may modify $LIBS and $CPPFLAGS

STATIC_GMP=""
STATIC_GMP_INCLUDE_DIR=""
AC_SUBST(STATIC_GMP)
AC_SUBST(STATIC_GMP_INCLUDE_DIR)
CSL_CHECK_STATIC_GMP($static_libgmp,$static_includegmp)

#
# Now check default library and include file
#
if test "x$includegmp" != x ; then
   if test -f $includegmp/gmp.h ; then
      CPPFLAGS="-I$includegmp $CPPFLAGS"
   else
      AC_MSG_ERROR([*** gmp.h not found in $includegmp. Check --with-gmp-include-dir option ***])
   fi
else
   AC_CHECK_HEADER([gmp.h],[],
      [AC_MSG_ERROR([*** gmp.h not found. Try --with-gmp-include-dir or set CPPFLAGS ***])])
fi

AC_CHECK_LIB(gmp, __gmpz_cmp, [],
      [AC_MSG_ERROR([*** GMP library not found. Try --with-gmp or set LDFLAGS ***])])



#
# Restore CFLAGS
#
CFLAGS=$saved_cflags

#
# Restore CFLAGS
#
CFLAGS=$saved_cflags

#
# Store config data in ./configs/make.include.$(ARCH)
#
AC_OUTPUT([make.include])

AC_MSG_NOTICE([Moving make.include to configs/make.include.$build])
mv make.include "configs/make.include.$build"
