#
# tests/Makefile
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

include $(YICES_TOP_DIR)/$(YICES_MAKE_INCLUDE)


#
# build subdirectories
#
objdir := $(BUILD)/obj
libdir := $(BUILD)/lib
bindir := $(BUILD)/bin


# library
libyices := $(libdir)/libyices.a


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
  STATIC=-static
else
ifeq ($(POSIXOS),mingw)
  CPPFLAGS := $(CPPFLAGS) -DMINGW -DNOYICES_DLL
  PIC=
  STATIC=-static
else
ifeq ($(POSIXOS),darwin)
  CPPFLAGS := $(CPPFLAGS) -DMACOSX
  PIC=
  STATIC=
else
ifeq ($(POSIXOS),sunos)
  CPPFLAGS := $(CPPFLAGS) -DSOLARIS
  PIC=-fpic
  STATIC=
else
ifeq ($(POSIXOS),linux)
  CPPFLAGS := $(CPPFLAGS) -DLINUX
  PIC=-fPIC
  STATIC=-static
else
  PIC=-fPIC
  STATIC=-static
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
# TODO: fix LIBS in static mode. Need to remove -lgmp from LIBS
# otherwise adding $(STATIC_GMP) does not work on Darwin or cygwin
#
ifeq ($(YICES_MODE),release) 
CFLAGS := $(CFLAGS) -O3 -fomit-frame-pointer $(PIC)
CPPFLAGS := $(CPPFLAGS) -DNDEBUG
else 
ifeq ($(YICES_MODE),static)
ifneq ($(STATIC_GMP_INCLUDE_DIR),)
CPPFLAGS := -I$(STATIC_GMP_INCLUDE_DIR) $(CPPFLAGS)
endif
CFLAGS := $(CFLAGS) -O3 $(STATIC)
CPPFLAGS := $(CPPFLAGS) -DNDEBUG
LIBS := $(STATIC_GMP) $(subst $(LIBS),-lgmp,)
else
ifeq ($(YICES_MODE),profile)
CFLAGS := $(CFLAGS) -O3 $(PIC) -pg
CPPFLAGS := $(CPPFLAGS) -DNDEBUG
else
ifeq ($(YICES_MODE),gcov)
CFLAGS := $(CFLAGS) -fprofile-arcs -ftest-coverage $(PIC)
CPPFLAGS := $(CPPFLAGS) -DNDEBUG
else
ifeq ($(findstring $(YICES_MODE),valgrind quantify purify),$(YICES_MODE))
CFLAGS := $(CFLAGS) -O3 -fomit-frame-pointer -g $(PIC) 
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
ifeq ($(YICES_MODE),purify)
LNK := purify $(CC)
else
ifeq ($(YICES_MODE),quantify)
LNK := quantify $(CC)
else
LNK := $(CC)
endif
endif


#
# Need include path
#
CPPFLAGS := $(CPPFLAGS) -I../src


#
# All source files in this directory
#
src_c := $(wildcard *.c)
tests := $(src_c:%.c=$(bindir)/%$(EXEEXT))
dep := $(src_c:%.c=$(objdir)/%.d)

# library
libyices := $(libdir)/libyices.a


# All test binaries
all: $(tests)

$(bindir)/%$(EXEEXT): %.c $(libyices)
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -o $@ $<  $(libyices) $(LIBS) -lm 

# Dependency file
$(objdir)/%.d: %.c
	@ echo Building dependency file $@
	@ $(CC) -MM $(CPPFLAGS) $< > $@.tmp
	@ $(SED) 's,\($*\).o[ :]*,$(objdir)/\1.o $@ : , g' < $@.tmp > $@
	@ rm -f $@.tmp

include $(dep)

# avoid .DEFAULT when .h files have been deleted
%.h:
	@ echo "$@ missing"


.PHONY: all 

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

