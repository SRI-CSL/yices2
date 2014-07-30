#########################################################################
#  The Yices SMT Solver. Copyright 2014 SRI International.              #
#                                                                       #
#  This program may only be used subject to the noncommercial end user  #
#  license agreement which is downloadable along with this program.     #
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
  CPPFLAGS := $(CPPFLAGS) -DMINGW -DNOYICES_DLL
  PIC=
  STATIC=-static
  LDFLAGS += -Wl,--stack,8388608
else
ifeq ($(POSIXOS),darwin)
  CPPFLAGS := $(CPPFLAGS) -DMACOSX
  CFLAGS += -fvisibility=hidden
  PIC=-fPIC
  STATIC=
else
ifeq ($(POSIXOS),sunos)
  CPPFLAGS := $(CPPFLAGS) -DSOLARIS
  CFLAGS += -fvisibility=hidden
  PIC=-fPIC
  STATIC=
else
ifeq ($(POSIXOS),linux)
  CPPFLAGS := $(CPPFLAGS) -DLINUX
  CFLAGS += -fvisibility=hidden
  PIC=-fPIC
  STATIC=-static
else
ifeq ($(POSIXOS),freebsd)
  CPPFLAGS := $(CPPFLAGS) -DFREEBSD
  CFLAGS += -fvisibility=hidden
  PIC=-fPIC
  STATIC=-static
else
  PIC=-fPIC
  CFLAGS += -fvisibility=hidden
  STATIC=-static
endif
endif
endif
endif
endif
endif



#
# Warning levels
#
CFLAGS += -Wall -Winline -Wredundant-decls
ifeq ($(POSIXOS),mingw)
  ifeq ($(findstring -mno-cygwin, $(CFLAGS)), -mno-cygwin)
   #
   # compilation on mingw using the -mno-cygwin flag
   # We disable -Wformat because mingw uses non-standard
   # formats in printf/fprintf that do not seem to be
   # understood by gcc and cause useless warnings.
   #
   CFLAGS += -Wno-format
  endif
endif


#
# Compilation flags dependent on MODE
#
ifeq ($(YICES_MODE),release)
  CFLAGS := $(CFLAGS) -O3 -fomit-frame-pointer
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
ifeq ($(findstring $(YICES_MODE),valgrind quantify purify),$(YICES_MODE))
  CFLAGS := $(CFLAGS) -O3 -g
  CPPFLAGS := $(CPPFLAGS) -DNDEBUG
else
  CFLAGS := $(CFLAGS) -g
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
  STATIC_CPPFLAGS := -I$(STATIC_GMP_INCLUDE_DIR) $(CPPFLAGS)
else
  STATIC_CPPFLAGS := $(CPPFLAGS)
endif

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
STATIC_LIBS := $(STATIC_GMP) $(subst -lgmp,,$(LIBS))


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

include $(dep)
include $(static_dep)



# All test binaries, using dynamic GMP library
all: $(tests)

$(bindir)/%$(EXEEXT): %.c $(libyices)
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -o $@ $<  $(libyices) $(LIBS)


# Test binaries compiled statically
all-static: $(static_tests)

$(static_bindir)/%$(EXEEXT): %.c $(static_libyices)
	$(LNK) $(STATIC_CPPFLAGS) $(CFLAGS) $(LDFLAGS) $(STATIC) -o $@ $<  $(static_libyices) $(STATIC_LIBS)


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

