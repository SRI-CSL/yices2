#########################################################################
#
#  This file is part of the Yices SMT Solver.
#  Copyright (C) 2017 SRI International.
#
#  Yices is free software: you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation, either version 3 of the License, or
#  (at your option) any later version.
#
#  Yices is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with Yices.  If not, see <http://www.gnu.org/licenses/>.
#
#########################################################################

#
# Top-level Makefile
#
# Determine the architecture and top directory.
# Import architecture files from top-dir/configs/make.include.$(ARCH)
#

SHELL=/bin/sh

YICES_TOP_DIR=$(shell pwd)

#
# Version numbers: <version>.<minor>.<patch-level>
# - this determines the name of the distribution tarfile
# - the number is also used in the shared library
#   for linux:  the soname is libyices.so.<major>.<minor>
#   for darwin: the compatibility version is <major>.<minor>.0
#               the version is set to <major>.<minor>.<patch-level>
#
# Conventions we should follow:
# <major> increases for major new releases.
# <minor> increases when we make changes that loose
#         backward compatibility.
# <patch-level> increases for bug fixes or other improvements
#         that maintain backward compatibility.
#
# Example: if P is linked against libyices.so version 2.0.0
# - P should still work (without recompliling) with libyices 2.0.1
# - P should not work anymore with libyices 2.1.0 or 3.0.0
#
# N.B There are also an occurrences in:
# src/include/yices.h
# doc/manual/manual.tex
# doc/sphinx/source/conf.py
# doc/yices*.1 man files
#
MAJOR = 2
MINOR = 6
PATCH_LEVEL = 2

YICES_VERSION = $(MAJOR).$(MINOR).$(PATCH_LEVEL)


#
# Find platform (also default configuration)
#
ARCH=$(shell ./config.sub `./config.guess`)
POSIXOS=$(shell ./autoconf/os)

ifeq (,$(POSIXOS))
  $(error "Problem running ./autoconf/os")
else
ifeq (unknown,$(POSIXOS))
  $(error "Unknown OS")
endif
endif


#
# OPTION: select an alternative configuration file
#
# 1) On Mac OS X Leopard/intel (darwin9.X.Y), the default configuration is
#    in file  make.include.i386-apple-darwin9.X.Y
#    This builds Yices as a 32bit executable.
#
#    It's possible to use an alternative configuration file
#       make.include.x86_64-apple-darwin9.Y.Z on the same system.
#    This is intended to build Yices as 64bit code.
#
#    To select the alternative configuration use 'make OPTION=64bits ..'
#
# 1a) Since Mac OS X Snow Leopard (darwin10.X.Y) and newer, the default
#     is reversed. The default configuration is in file
#        make.include.x86_64-apple-darwin10.X.Y
#     This builds Yices for 64bit by default.
#
#     To build for 32bit on the same system, use the alternative
#     configuration file  make.include.i386-apple-darwin10.X.Y
#
#     To select the alternative configuration use 'make OPTION=32bits ...'
#
# 2) On Linux/x86_64, we compile in 64 bit mode by default,
#    using configuration file make.include.x86_64-unknown-linux-gnu
#
#    It may be possible to build in 32 bit mode on the same machine,
#    provided the compiler understand option -m32 and the necessary
#    32bit libraries are present. The corresponding Yices configuration
#    is make.include.i686-unknown-linux-gnu
#
#    To select this 32bit configuration, use 'make OPTION=32bits ...'
#
# 3) On cygwin, the default configuration is make.include.i686-pc-cygwin.
#    Two alternatives are supported:
#         make.include.i686-pc-mingw32    (mingw32/Windows 32bit native)
#    and  make.include.x86_64-pc-mingw32  (Windows 64bit native)
#
#    To select the Windows 32bit configuration, use
#          'make OPTION=no-cygwin ...'
#       or 'make OPTION=mingw32 ...'
#
#    To select the Windows 64bit configuration, use
#         'make OPTION=mingw64'
#
#    Issue: 2013/12/11: this Makefile is not robust for
#    cross-compilation on Cygwin (to produce Windows 64 code).
#    The simplest way to configure for this cross-compilation is
#       ./configure --host=x86_64-w64-mingw32 ....
#
#    This generates ./configs/makefile.include.x86_64-w64-mingw32.
#    But OPTION=mingw64 gives ./configs/makefile.include.x86_64-pc-mingw32
#
#
# 4) On solaris, the default is make.include.sparc-sun-solaris2.x
#    (should be 32bits).
#
#    The alternative is make.include.sparc64-sun-solaris2.x
#    (should be for 64bits build). To select it, give OPTION=64bits.
#
# Check README for details on generating these alternative configurations.
#
ifneq ($(OPTION),)
  ifeq ($(POSIXOS),linux)
    ifeq ($(OPTION),32bits)
      newarch=$(subst x86_64,i686,$(ARCH))
    else
    ifeq ($(OPTION),mingw32)
      newarch=i686-w64-mingw32
      POSIXOS=mingw
    endif
    endif
  else
  ifeq ($(POSIXOS),darwin)
    ifeq ($(OPTION),64bits)
      newarch=$(subst i386,x86_64,$(ARCH))
    else
    ifeq ($(OPTION),32bits)
      newarch=$(subst x86_64,i386,$(ARCH))
    endif
    endif
  else
  ifeq ($(POSIXOS),cygwin)
    ifeq ($(OPTION),32bits)
      newarch=$(subst x86_64,i686,$(ARCH))
    else
    ifeq ($(OPTION),no-cygwin)
      newarch=$(subst cygwin,mingw32,$(subst x86_64,i686,$(ARCH)))
      alternate=$(subst pc,w64,$(subst unknown,w64,$(newarch)))
      POSIXOS=mingw
    else
    ifeq ($(OPTION),mingw32)
      newarch=$(subst cygwin,mingw32,$(subst x86_64,i686,$(ARCH)))
      alternate=$(subst pc,w64,$(subst unknown,w64,$(newarch)))
      POSIXOS=mingw
    else
    ifeq ($(OPTION),mingw64)
      newarch=$(subst cygwin,mingw32,$(subst i686,x86_64,$(ARCH)))
      alternate=$(subst pc,w64,$(subst unknown,w64,$(newarch)))
      POSIXOS=mingw
    endif
    endif
    endif
    endif
  else
  ifeq ($(POSIXOS),sunos)
    ifeq ($(OPTION),64bits)
      newarch=$(subst sparc,sparc64,$(ARCH))
    endif
  endif
  ifeq ($(POSIXOS),freebsd)
    ifeq ($(OPTION),32bits)
      newarch=$(subst x86_64,i386,$(ARCH))
    endif
  endif
  endif
  endif
  endif

  ifeq ($(newarch),)
    $(error "option $(OPTION) not supported on platform $(ARCH)")
  endif
  ARCH := $(newarch)
endif


#
# Check whether make.include exists
#
# Note: we don't want to run ./configure from here.
# The user may need to give options to the ./configure
# script.
#
make_include = configs/make.include.$(ARCH)
known_make_includes = $(filter-out %.in, $(wildcard configs/make.include.*))

YICES_MAKE_INCLUDE := $(findstring $(make_include), $(known_make_includes))

ifeq (,$(YICES_MAKE_INCLUDE))
  #
  # Try alternate name (--host= ...)
  #
  ifneq (,$(alternate))
     make_alternate = configs/make.include.$(alternate)
     YICES_MAKE_INCLUDE := $(findstring $(make_alternate), $(known_make_includes))
     ifeq (,$(YICES_MAKE_INCLUDE))
        $(error Could not find $(make_include) nor $(make_alternate). Run ./configure)
     else
        $(info Could not find $(make_include). Using $(make_alternate) instead)
     endif
  else
    $(error Could not find $(make_include). Run ./configure)
  endif
endif


#
# Check build mode
#
default_mode=release
allowed_modes=release debug devel profile gcov valgrind purify quantify gperftools sanitize
MODE ?= $(default_mode)

YICES_MODE := $(filter $(allowed_modes), $(MODE))

ifeq (,$(YICES_MODE))
  $(error "Invalid build mode: $(MODE)")
endif


#
# Default target: build binaries/libraries
#
default: dist

#
# Just print the configuration
#
show-config: checkgmake
	@ echo "ARCH is $(ARCH)"
	@ echo "POSIXOS is $(POSIXOS)"
	@ echo "YICES_TOP_DIR is $(YICES_TOP_DIR)"
	@ echo "YICES_MAKE_INCLUDE is $(YICES_MAKE_INCLUDE)"
	@ echo "YICES_MODE is $(YICES_MODE)"
	@ echo "YICES_VERSION is $(YICES_VERSION)"

checkgmake:
	@ ./gmaketest --make=$(MAKE) || \
	  (echo "GNU-Make is required to compile Yices. Aborting."; exit1)


#
# Invoke submake that will do the real work
# the quotes around the 'YICES_TOP_DIR= ...' help if the directory
# name include spaces
#
# We must have doc as an explicit target since we have a ./doc directory.
# Without it 'make doc' does nothing. To be safe, I've also added bin,
# lib, obj, etc. so that the Makefile will work event if directories
# or files with these names are present.
#
.DEFAULT doc all bin lib obj dist static-bin static-lib static-obj static-dist install test static-test \
   check static-check check-api static-check-api: checkgmake
	@ echo "Mode:     $(YICES_MODE)"
	@ echo "Platform: $(ARCH)"
	@ $(MAKE) -f Makefile.build \
	'YICES_MODE=$(YICES_MODE)' \
	'ARCH=$(ARCH)' \
	'POSIXOS=$(POSIXOS)' \
	'YICES_TOP_DIR=$(YICES_TOP_DIR)' \
	'YICES_MAKE_INCLUDE=$(YICES_MAKE_INCLUDE)' \
	'YICES_VERSION=$(YICES_VERSION)' \
	'MAJOR=$(MAJOR)' \
	'MINOR=$(MINOR)' \
	'PATCH_LEVEL=$(PATCH_LEVEL)' \
	$@


.PHONY: checkgmake show-config doc all bin lib obj dist static-bin static-lib static-obj static-dist install \
        test static-test default check static-check chesk-api static-check-api
