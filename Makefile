#
# Top-level Makefile
#
# Determine the architecture and top directory
# Import architecture files from top-dir/configs/make.include.$(ARCH)
#

SHELL=/bin/sh

YICES_TOP_DIR=$(PWD)

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
allowed_modes=release static debug profile gcov valgrind purify quantify
MODE ?= $(default_mode)

YICES_MODE := $(filter $(allowed_modes), $(MODE))

ifeq (,$(YICES_MODE))
  $(error "Invalid build mode: $(MODE)")
endif


#
# Source distribution
#
distdir=./distributions
tmpdir=./yices2
srctarfile=$(distdir)/yices2-src.tar.gz

#
# Just print configuration
#
check: checkgmake
	@ echo "ARCH is $(ARCH)"
	@ echo "POSIXOS is $(POSIXOS)"
	@ echo "YICES_TOP_DIR is $(YICES_TOP_DIR)"
	@ echo "YICES_MAKE_INCLUDE is $(YICES_MAKE_INCLUDE)"
	@ echo "YICES_MODE is $(YICES_MODE)"

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
	$@




#
# Build the source tar file
# - the sync; sync; sleep 20 is a hack intended to work around
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
	mkdir $(tmpdir)/sat_solver
	mkdir $(tmpdir)/tests
	mkdir $(tmpdir)/doc
	mkdir $(tmpdir)/examples
	cp install-sh config.guess configure configure.ac config.sub gmaketest $(tmpdir)
	cp README Makefile Makefile.build make.include.in $(tmpdir)
	cp autoconf/* $(tmpdir)/autoconf
	cp src/Makefile src/*.h src/*.c src/yices_keywords.txt src/smt_keywords.txt \
	  src/yices_exports.def src/yices_version_template.txt $(tmpdir)/src
	rm -f $(tmpdir)/src/yices_hash_keywords.h $(tmpdir)/src/smt_hash_keywords.h
	cp tests/Makefile tests/*.c $(tmpdir)/tests
	cp sat_solver/Makefile sat_solver/*.h sat_solver/*.c $(tmpdir)/sat_solver
	cp doc/NOTES doc/SMT-LIB-LANGUAGE doc/smt_parser.txt doc/yices_parser.txt doc/table_builder.c \
	  doc/smt-grammar $(tmpdir)/doc
	cp examples/*.ys examples/*.smt examples/*.txt $(tmpdir)/examples
	chmod -R og+rX $(tmpdir)
	mkdir -p $(distdir)
	sync
	sync
	sleep 20
	tar -czf $(srctarfile) $(tmpdir)
	chmod -R og+rX $(distdir)
	rm -f -r $(tmpdir)


.PHONY: checkgmake check source-distribution
