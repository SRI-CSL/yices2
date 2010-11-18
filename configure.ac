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
AC_PROG_INSTALL

AC_PROG_CC
AC_PROG_RANLIB
AC_PROG_EGREP
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
dnl GMP Libraries
dnl -------------
dnl
dnl We need as many as three different versions of GMP:
dnl
dnl To build static executables and libraries, we link with the
dnl default libgmp.a (usually /usr/local/libgmp.a).
dnl 
dnl To construct the yices library (libyices.so) with GMP included,
dnl we need a version of libgmp.a that's position independent code.
dnl On systems where -fPIC is not the default, we must build
dnl a specific version of GMP from the source, using option CFLAG=-fPIC.
dnl
dnl To build dynamic executables and libraries without GMP included,
dnl we need a a dynamic version of the GMP library (e.g., /usr/local/libgmp.so). 
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
dnl By default, the configure script search for a usable STATIC_GMP in default
dnl locations and set PIC_GMP to the same thing as STATIC_GMP.
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
   [if test "x$withval" == x; then
      AC_MSG_WARN([--with-static-gmp was used but no path was given. Using defaults])
    else
      static_libgmp=$withval
    fi
   ] 
   [])

static_includegmp=""
AC_ARG_WITH([static-gmp-include-dir],
   [AS_HELP_STRING([--with-static-gmp-include-dir=<directory>],
            [Directory of include file "gmp.h" compatible with static GMP library])],
   [if test "x$withval" == x; then
      AC_MSG_WARN([--with-static-gmp-include-dir was used but no directory was given. Using defaults])
    else 
      static_includegmp=$withval
    fi
   ]
   [])


pic_libgmp=""
AC_ARG_WITH([pic-gmp], 
   [AS_HELP_STRING([--with-pic-gmp=<path>],[Full path to a relocatable GMP library (e.g., libgmp.a)])],
   [if test "x$withval" == x; then
      AC_MSG_WARN([--with-pic-gmp was used but no path was given. Using defaults])
    else
      pic_libgmp=$withval
    fi
   ]
   [])

pic_includegmp=""
AC_ARG_WITH([pic-gmp-include-dir],
   [AS_HELP_STRING([--with-pic-gmp-include-dir=<directory>],
            [Directory of include file "gmp.h" compatible with relocatable GMP library])],
   [if test "x$withval" == x; then
      AC_MSG_WARN([--with-pic-gmp-include-dir was used but no directory was given. Using defaults])
    else 
      pic_includegmp=$withval
    fi
   ]
   [])




dnl
dnl CSL_CHECK_GMP_HEADER(includedir,option)
dnl ----------------------------------------
dnl check whether 'gmp.h' is present in includedir
dnl set variable $testincludedir to includedir if so
dnl exit otherwise.
dnl if includedir is empty, just set testincludedir to empty string too
dnl
dnl option must be the '--with-...-include-dir from which includedir was given
dnl it's used to print the error message.
dnl
AC_DEFUN([CSL_CHECK_GMP_HEADER],
[
testincludedir=""
if test "x$1" != x; then
   if test -d $1 ; then
     if test -f $1/gmp.h; then
        testincludedir=$1
     else
        AC_MSG_ERROR([*** gmp.h not found in $1. Check option $2 ***])
     fi
  else 
     AC_MSG_ERROR([*** directory $1 not found. Check option $2 ***])
  fi
fi
])


dnl
dnl CSL_CHECK_LIBGMP_PATH(path,option)
dnl -------------------------------
dnl path should be the full path to a static GMP library.
dnl this checks whether the given file exists. Print an
dnl error and exit otherwise.
dnl
dnl If the test succeeds, set variable testlib to path
dnl
AC_DEFUN([CSL_CHECK_LIBGMP_PATH],
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
AC_RUN_IFELSE([

#include <gmp.h>
int main() {
   mpz_t tst;
   mpz_init(tst);
   mpz_clear(tst);
   if ((__GNU_MP_VERSION < 4) || 
       ((__GNU_MP_VERSION == 4) && (__GNU_MP_VERSION_MINOR < 1))) {
     return 1;
   }
   return 0;
}

],run_ok=yes,run_ok=no,run_ok=no)
AC_MSG_RESULT([$run_ok])
#
# restore CPPFLAGS and LIBS
#
CPPFLAGS=$save_cppflags
LIBS=$save_libs
])



dnl
dnl CSL_CHECK_STATIC_GMP(ligmp,includedir)
dnl ------------------------------------
dnl try to find the full path to a usable libgmp.a, use $1 if not empty.
dnl if $2 is not empty, then the checks are compiled with -I$2 
dnl if everything works, then set STATIC_GMP to the fullpath for libgmp.a
dnl and set STATIC_GMP_INCLUDE_DIR to $2
dnl
dnl
AC_DEFUN([CSL_CHECK_STATIC_GMP],
[
AC_MSG_NOTICE([Trying to find a usable ligmp.a])
CSL_CHECK_GMP_HEADER($2,--with-static-gmp-include-dir)
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
  CSL_CHECK_LIBGMP_PATH($1,--with-static-gmp)
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




#
# CHECK GMP LIBRARIES
# -------------------
#
AC_LANG([C])

#
# We must search for the static version first
# since other tests may modify $LIBS and $CPPFLAGS
#
STATIC_GMP=""
STATIC_GMP_INCLUDE_DIR=""
AC_SUBST(STATIC_GMP)
AC_SUBST(STATIC_GMP_INCLUDE_DIR)
CSL_CHECK_STATIC_GMP($static_libgmp,$static_includegmp)

#
# Relocatable static version of GMP
#
PIC_GMP="$STATIC_GMP"
PIC_GMP_INCLUDE_DIR="$STATIC_GMP_INCLUDE_DIR"
AC_SUBST(PIC_GMP)
AC_SUBST(PIC_GMP_INCLUDE_DIR)
if test "x$pic_libgmp" != x ; then
  #
  # --with-pic-gmp was given on the command line
  #
  CSL_CHECK_GMP_HEADER($pic_includegmp,--with-pic-gmp-include-dir) 
  CSL_CHECK_LIBGMP_PATH($pic_libgmp,--with-pic-gmp)
  CSL_CHECK_GMP($testlib,$testincludedir)
  if test $run_ok = yes; then 
    PIC_GMP=$testlib
    PIC_GMP_INCLUDE_DIR=$testincludedir
  else
    AC_MSG_ERROR([*** $testlib does not appear to be usable: check option --with-pic-gmp ***])
  fi
fi


#
# Default GMP
#
AC_CHECK_LIB(gmp, __gmpz_cmp, [],
    [AC_MSG_ERROR([*** GMP library not found. Try to set LDFLAGS ***])])


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
