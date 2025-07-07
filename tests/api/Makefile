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
# tests/unit/Makefile
#
# Must be invoked with the following variables set
#
#   YICES_TOP_DIR = top-level directory for Yices
#   YICES_MODE = build mode
#   YICES_MAKE_INCLUDE = configuration file to include
#   ARCH = architecture (e.g, i686-pc-linux-gnu)
#   POSIXOS = OS (e.g., linux)
#   BUILD = target build director (normally build/$(ARCH)-$(YICES_MODE))
#
# Config variables are imported by including the file
#   $(YICES_TOP_DIR)/$(YICES_MAKE_INCLUDE)
#

SHELL=/bin/sh

ifeq (,$(YICES_TOP_DIR))
 $(error "YICES_TOP_DIR is undefined")
endif

ifeq (,$(YICES_MAKE_INCLUDE))
 $(error "YICES_MAKE_INCLUDE is undefined")
endif

conf=$(YICES_TOP_DIR)/$(YICES_MAKE_INCLUDE)

include $(conf)



#
# build subdirectories
#
objdir := $(BUILD)/obj
libdir := $(BUILD)/lib
bindir := $(BUILD)/bin

static_objdir := $(BUILD)/static_obj
static_libdir := $(BUILD)/static_lib
static_bindir := $(BUILD)/static_bin


#
# All source files in this directory
#
src_c := $(wildcard *.c)

#
# Dependencies and binaries
#
dep := $(src_c:%.c=$(objdir)/%.d)
static_dep := $(src_c:%.c=$(static_objdir)/%.d)

tests := $(src_c:%.c=$(bindir)/%$(EXEEXT))
static_tests := $(src_c:%.c=$(static_bindir)/%$(EXEEXT))

#
# Archives to link with:
# - libyices: objects compiled with the PIC option
# - static_libyices: compiled without the PIC option
#
libyices := $(libdir)/libyices.a
static_libyices := $(static_libdir)/libyices.a

#
# Whether we are building for a big endian architecture
#
ifeq ($(WORDS_BIGENDIAN),yes)
  CPPFLAGS += -DWORDS_BIGENDIAN
endif

#
# Whether we have support for mcsat
#
ifeq ($(ENABLE_MCSAT),yes)
  CPPFLAGS+=-DHAVE_MCSAT
endif

#
# Whether we have thread safety
# If so on Unix systems, we must add -pthread to CFLAGS
#
PTRHEAD=
ifeq ($(THREAD_SAFE),1)
  CPPFLAGS += -DTHREAD_SAFE
  PTHREAD= -pthread
endif


#
# OS-dependent compilation flags
# -fPIC: default on Darwin/Cygwin/Mingw (and causes
#  compilation warning if present)
# -static: not supported by Darwin and our Solaris2.10
# matchine
#
# All tests are linked with libyices.a
# so we don't want any dllimport/export in yices.h
# So we use -DNOYICES_DLL on cygwin and mingw
#
ifeq ($(POSIXOS),cygwin)
  CPPFLAGS := $(CPPFLAGS) -DCYGWIN -DNOYICES_DLL
  PIC=
  STATIC=-static -static-libgcc
  LDFLAGS += -Wl,--stack,8388608
else
ifeq ($(POSIXOS),mingw)
  CPPFLAGS := $(CPPFLAGS) -DMINGW -DNOYICES_DLL -D__USE_MINGW_ANSI_STDIO
  PIC=
  STATIC=-static
  LDFLAGS += -Wl,--stack,8388608
else
ifeq ($(POSIXOS),darwin)
  CPPFLAGS := $(CPPFLAGS) -DMACOSX
  CFLAGS += -fvisibility=hidden $(PTHREAD)
  PIC=-fPIC
  STATIC=
else
ifeq ($(POSIXOS),sunos)
  CPPFLAGS := $(CPPFLAGS) -DSOLARIS
  CFLAGS += -fvisibility=hidden $(PTHREAD)
  PIC=-fPIC
  STATIC=
else
ifeq ($(POSIXOS),linux)
  CPPFLAGS := $(CPPFLAGS) -DLINUX
  CFLAGS += -fvisibility=hidden $(PTHREAD)
  PIC=-fPIC
  STATIC=-static
  LIBS+=$(PTHREAD)
else
ifeq ($(POSIXOS),freebsd)
  CPPFLAGS := $(CPPFLAGS) -DFREEBSD
  CFLAGS += -fvisibility=hidden $(PTHREAD)
  PIC=-fPIC
  STATIC=-static
ifeq ($(POSIXOS),netbsd)
  PIC=-fPIC
  STATIC=-static
  CPPFLAGS := $(CPPFLAGS) -DNETBSD
  CFLAGS += -fvisibility=hidden $(PTHREAD)
  BIN_LDFLAGS=
  libyices_dynamic=$(libdir)/$(libyices_so)
  static_libyices_dynamic=$(static_libdir)/$(libyices_so)
else
ifeq ($(POSIXOS),unix)
  PIC=-fPIC
  STATIC=-static
  CPPFLAGS := $(CPPFLAGS) -DLINUX
  CFLAGS += -fvisibility=hidden $(PTHREAD)
  BIN_LDFLAGS=
  libyices_dynamic=$(libdir)/$(libyices_so)
  static_libyices_dynamic=$(static_libdir)/$(libyices_so)
else
 $(error "Don't know how to compile on $(POSIXOS)")
endif
endif
endif
endif
endif
endif
endif
endif


#
# Warning levels
#
CFLAGS += -Wall -Wredundant-decls -Wextra -Wpedantic
ifeq ($(POSIXOS),mingw)
  CFLAGS += -Wno-format
endif


#
# Compilation flags dependent on MODE
#
ifeq ($(YICES_MODE),release)
  CFLAGS := $(CFLAGS) -O3 -fomit-frame-pointer $(NO_STACK_PROTECTOR)
  CPPFLAGS := $(CPPFLAGS) -DNDEBUG
else
ifeq ($(YICES_MODE),devel)
  CFLAGS := $(CFLAGS) -O3 -fomit-frame-pointer $(NO_STACK_PROTECTOR)
  CPPFLAGS := $(CPPFLAGS) -DNDEBUG
else
ifeq ($(YICES_MODE),profile)
  CFLAGS := $(CFLAGS) -O3 -pg
  CPPFLAGS := $(CPPFLAGS) -DNDEBUG
else
ifeq ($(YICES_MODE),gcov)
  CFLAGS := $(CFLAGS) -fprofile-arcs -ftest-coverage
  CPPFLAGS := $(CPPFLAGS) -DNDEBUG
else
ifeq ($(YICES_MODE),sanitize)
CFLAGS := $(CFLAGS) -O3 -g -fsanitize=address,undefined -fno-omit-frame-pointer
CPPFLAGS := $(CPPFLAGS) -DNDEBUG
else
ifeq ($(findstring $(YICES_MODE),valgrind quantify purify),$(YICES_MODE))
  CFLAGS := $(CFLAGS) -O3 -g
  CPPFLAGS := $(CPPFLAGS) -DNDEBUG
else
ifeq ($(YICES_MODE),gperftools)
CFLAGS := $(CFLAGS) -O3 -g
CPPFLAGS := $(CPPFLAGS) -DNDEBUG
ifeq ($(POSIXOS),linux)
  LIBS += -Wl,--no-as-needed -lprofiler
else
  LIBS += -lprofiler
endif
else
#
# debug mode
#
CFLAGS := $(CFLAGS) -g
endif
endif
endif
endif
endif
endif
endif

#
# Link command for purify/quantify
#
ifeq ($(POSIXOS),sunos)
ifeq ($(YICES_MODE),purify)
LNK := purify $(CC)
else
ifeq ($(YICES_MODE),quantify)
LNK := quantify $(CC)
else
LNK := $(CC)
endif
endif
else
# not solaris
LNK := $(CC)
endif


#
# Include path: -I../../src must be first in case there
# are other -I in CPPFLAGS
#
CPPFLAGS := -I../../src -I../../src/include $(CPPFLAGS)


#
# More CPPFLAGS for compiling static objects
#
ifneq ($(STATIC_GMP_INCLUDE_DIR),)
  STATIC_CPP_GMP := -I$(STATIC_GMP_INCLUDE_DIR)
endif

ifneq ($(STATIC_LIBPOLY_INCLUDE_DIR),)
  STATIC_CPP_LIBPOLY := -I$(STATIC_LIBPOLY_INCLUDE_DIR)
endif

STATIC_CPPFLAGS := $(STATIC_CPP_GMP) $(STATIC_CPP_LIBPOLY) $(CPPFLAGS)

#
# These are not needed for the tests -DNOYICES_DLL is already
# in CPPFLAGS
#
# ifeq ($(POSIXOS),cygwin)
#   STATIC_CPPFLAGS += -DNOYICES_DLL
# else
# ifeq ($(POSIXOS),mingw)
#   STATIC_CPPFLAGS += -DNOYICES_DLL
# endif
# endif


#
# LIBS for compiling in static mode
#
# We need to remove -lgmp from LIBS in static mode, otherwise adding
# $(STATIC_GMP) does not work on Darwin and cygwin
#
# Also, we want $(STATIC_GMP) last in this list
#
NOGMP_LIBS := $(subst -lpoly,,$(subst -lgmp,,$(LIBS)))
STATIC_LIBS := $(NOGMP_LIBS) $(STATIC_LIBPOLY) $(STATIC_GMP)


# Dependency file
$(objdir)/%.d: %.c
	@ echo Building dependency file $@
	@ $(CC) -MM $(CPPFLAGS) $< > $@.tmp
	@ $(SED) 's,\($*\).o[ :]*,$(objdir)/\1.o $@ : , g' < $@.tmp > $@
	@ rm -f $@.tmp

$(static_objdir)/%.d: %.c
	@ echo Building dependency file $@
	@ $(CC) -MM $(STATIC_CPPFLAGS) $< > $@.tmp
	@ $(SED) 's,\($*\).o[ :]*,$(static_objdir)/\1.o $@ : , g' < $@.tmp > $@
	@ rm -f $@.tmp

#
# Dependency files
#
$(objdir)/%.d: %.c
	@set -e; echo Building dependency file $@ ; \
	$(CC) -MM -MG -MT $*.o $(CFLAGS) $(CPPFLAGS) $< > $@.$$$$ ; \
	$(SED) 's,\($*\).o[ :]*,$(objdir)/\1.o $@ : , g' < $@.$$$$ > $@ ; \
	rm -f $@.$$$$

$(static_objdir)/%.d: %.c
	@set -e; echo Building dependency file $@ ; \
	$(CC) -MM -MG -MT $*.o $(CFLAGS) $(STATIC_CPPFLAGS) $< > $@.$$$$ ; \
	$(SED) 's,\($*\).o[ :]*,$(static_objdir)/\1.o $@ : , g' < $@.$$$$ > $@ ; \
	rm -f $@.$$$$


static_goals := $(filter %-static,$(MAKECMDGOALS))
dyn_goals := $(filter-out %-static,$(MAKECMDGOALS))

ifneq ($(dyn_goals),)
 include $(dep)
 include $(bin_dep)
 include $(version_dep)
endif

ifneq ($(static_goals),)
 include $(static_dep)
 include $(static_bin_dep)
 include $(static_version_dep)
endif


# Objects
$(objdir)/%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) $(PIC) -c $< -o $@

$(static_objdir)/%.o: %.c
	$(CC) $(STATIC_CPPFLAGS) $(CFLAGS) -c $< -o $@


# All test binaries, using dynamic GMP library
all: $(tests)
	@ echo === Running tests ===
	@ rm -f *.log
	@ for test in $^ ; do ./run_test.sh $$test || exit 1 ; done
	@ echo
	@ ./print_summary.sh tests.log

$(bindir)/%$(EXEEXT): $(objdir)/%.o $(libyices)
	$(LNK) $(CFLAGS) $(LDFLAGS) -o $@ $<  $(libyices) $(LIBS)


# Test binaries compiled statically
all-static: $(static_tests)
	@ echo === Running tests ===
	@ rm -f *.log
	@ for test in $^ ; do ./run_test.sh $$test || exit 1 ; done
	@ echo
	@ ./print_summary.sh tests.log

$(static_bindir)/%$(EXEEXT): $(static_objdir)/%.o $(static_libyices)
	$(LNK) $(CFLAGS) $(LDFLAGS) $(STATIC) -o $@ $<  $(static_libyices) $(STATIC_LIBS)


.PHONY: all all-static


#
# rules to avoid triggering the .DEFAULT rule if .h or .c files have been deleted
#
%.h:
	@ echo
	@ echo "$@ missing"
	@ echo

%.c:
	@ echo
	@ echo "Missing source file: $@"
	@ echo




# For debugging
.DEFAULT:
	@ echo
	@ echo "*** src/Mafefile ***"
	@ echo
	@ echo "target is $@"
	@ echo
	@ echo "ARCH is $(ARCH)"
	@ echo "POSIXOS is $(POSIXOS)"
	@ echo "YICES_TOP_DIR is $(YICES_TOP_DIR)"
	@ echo "YICES_MAKE_INCLUDE is $(YICES_MAKE_INCLUDE)"
	@ echo "YICES_MODE is $(YICES_MODE)"
	@ echo "BUILD is $(BUILD)"
	@ echo
	@ echo "Configuration"
	@ echo "  EXEEXT   = $(EXEEXT)"
	@ echo "  SED      = $(SED)"
	@ echo "  LN_S     = $(LN_S)"
	@ echo "  MKDIR_P  = $(MKDIR_P)"
	@ echo "  CC       = $(CC)"
	@ echo "  CPPFLAGS = $(CPPFLAGS)"
	@ echo "  CFLAGS   = $(CFLAGS)"
	@ echo "  LIBS     = $(LIBS)"
	@ echo "  LDFLAGS  = $(LDFLAGS)"
	@ echo "  LD       = $(LD)"
	@ echo "  AR       = $(AR)"
	@ echo "  RANLIB   = $(RANLIB)"
	@ echo "  STATIC_GMP = $(STATIC_GMP)"
	@ echo "  STATIC_GMP_INCLUDE_DIR = $(STATIC_GMP_INCLUDE_DIR)"
	@ echo

