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
# Conventions we should follow: increase 'minor' when we make 
# changes that are not backward compatible.
#
# <major> increases when the new version is not binary
#         compatible with older versions (i.e., a program
#         linked to the old library can't use the new library).
# <minor> increases when the library's API changes but 
#         binary compatibility is preserved (e.g., new
#         functionalities added)
# <patch-level> increases for bug fixes or other improvements
#         that don't change the interface.
#
MAJOR = 2
MINOR = 0
PATCH_LEVEL = 0

YICES_VERSION = $(MAJOR).$(MINOR).$(PATCH_LEVEL)


#
# Find platform
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
# OPTIONS: use alternative configuration files
#
# 1) On Mac OS X/intel, we compile in 32 bit mode by default.
# It's possible to build in 64 bit mode on the same machine.
# - To select 64bit mode, type 'make MODE=... OPTION=64bits'
# - This changes ARCH from 
#     i386-apple-darwin9.x.y to x86_64-apple-darwin9.x.y
#   and the corresponding make.include should be constructed using 
#   ./configure --build=x86_64-apple-darwin.x.y CFLAGS=-m64
#
# 2) On Linux/x86_64, we compile in 64 bit mode by default.
# It may be possible to build in 32 bit mode on the same machine.
# - To select 32bit mode, type 'make MODE=... OPTION=32bits'
# - This changes ARCH from
#     x86_64-unknown-linux-gnu to i686-unknown-linux-gnu
#   and there must be a corresponding make.include file in 
#   ./configs
# - To construct this config file use
#   ./configure --build=i686-unknown-linux-gnu CFLAGS=-m32
#
# 3) On cygwin, it may be possible to build a mingw version (compilation
#  with flag -mno-cygwin)
#  - To select that mode, type 'make MODE=... OPTION=no-cygwin
#  - This changes ARCH from i686-pc-cygwin to i686-pc-mingw32.
#  - There must be a corresponding make.include.i686-pc-mingw32 in ./configs
#  - To construct this config file, use
#     ./configure --build=i686-pc-mingw32 CFLAGS=-mno-cygwin
#
ifneq ($(OPTION),)
ifeq ($(OPTION),32bits)
  newarch=$(subst x86_64,i686,$(ARCH))
else
ifeq ($(OPTION),64bits) 
  newarch=$(subst i386,x86_64,$(ARCH))
else
ifeq ($(OPTION),no-cygwin)
  newarch=$(subst cygwin,mingw32,$(ARCH))
  POSIXOS=mingw
else
  $(error "Invalid option: $(OPTION)")
endif
endif
endif
ifeq ($(newarch),$(ARCH))
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
  $(error Could not find $(make_include). Run ./configure)
endif


#
# Check build mode
#
default_mode=release
allowed_modes=release debug profile gcov valgrind purify quantify
MODE ?= $(default_mode)

YICES_MODE := $(filter $(allowed_modes), $(MODE))

ifeq (,$(YICES_MODE))
  $(error "Invalid build mode: $(MODE)")
endif


#
# Just print the configuration
#
check: checkgmake
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
.DEFAULT: checkgmake
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




.PHONY: checkgmake check source-distribution


#
# Source distribution
#
distdir=./distributions
tmpdir=./yices-$(YICES_VERSION)
srctarfile=$(distdir)/yices-$(YICES_VERSION)-src.tar.gz


#
# Build the source tar file
# - the sleep 10 is a hack intended to work around
#   some bugs in the nfs client on some versions of Linux
# - without it, we get an error from tar:
#   'file xxx changed as we read it'
#
source-distribution:
	rm -f -r $(tmpdir)
	mkdir $(tmpdir)
	mkdir $(tmpdir)/autoconf
	mkdir $(tmpdir)/configs
	mkdir $(tmpdir)/src
	mkdir $(tmpdir)/tests
	mkdir $(tmpdir)/doc
	mkdir $(tmpdir)/examples
	cp install-sh config.guess configure configure.ac config.sub gmaketest $(tmpdir)
	cp README Makefile Makefile.build make.include.in $(tmpdir)
	cp autoconf/* $(tmpdir)/autoconf
	cp src/Makefile src/*.h src/*.c src/yices_keywords.txt \
	  src/yices_version_template.txt $(tmpdir)/src
	cp tests/Makefile tests/*.c $(tmpdir)/tests
	cp doc/NOTES doc/YICES-LANGUAGE doc/yices_parser.txt doc/yices_parser_tables.h \
	  doc/table_builder.c $(tmpdir)/doc
	for file in `ls examples | grep -e '*.ys|*.txt|*.smt|*.c' ` ; do \
	  cp examples/$$file $(tmpdir)/examples ; \
        done
	chmod -R og+rX $(tmpdir)
	mkdir -p $(distdir)
	sleep 10
	tar -czf $(srctarfile) $(tmpdir)
	chmod -R og+rX $(distdir)
	rm -f -r $(tmpdir)


