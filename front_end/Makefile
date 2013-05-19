#
# front_end/Makefile
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


# all source files in the current directory
src_c := smt2-parse.c smt2-eval.c hash.c vector.c

obj := $(src_c:%.c=$(objdir)/%.o)
static_obj := $(src_c:%.c=$(static_objdir)/%.o)

# dependencies
dep := $(src_c:%.c=$(objdir)/%.d) $(objdir)/smt2-lex.d
static_dep := $(src_c:%.c=$(static_objdir)/%.d)


#
# Archives to link with:
# - libyices: objects compiled with the PIC option
# - static_libyices: compiled without the PIC option
#
libyices := $(libdir)/libyices.a
static_libyices := $(static_libdir)/libyices.a

#
# Binaries
#
binaries := $(bindir)/yices_smt2$(EXEEXT)
static_binaries := $(static_bindir)/yices_smt2$(EXEEXT)


#
# OS-dependent compilation flags
# -fPIC: default on Darwin/Cygwin/Mingw (and causes 
#  compilation warning if present)
# -static: not supported by Darwin and our Solaris2.10 
# matchine
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
  PIC=
  STATIC=
else
ifeq ($(POSIXOS),sunos)
  CPPFLAGS := $(CPPFLAGS) -DSOLARIS
  PIC=-fPIC
  STATIC=
else
ifeq ($(POSIXOS),linux)
  CPPFLAGS := $(CPPFLAGS) -DLINUX
  PIC=-fpic
  STATIC=-static
else
ifeq ($(POSIXOS),freebsd)
  CPPFLAGS := $(CPPFLAGS) -DFREEBSD
  PIC=-fpic
  STATIC=-static
else
ifeq ($(POSIXOS),unix)
  CPPFLAGS := $(CPPFLAGS) -DLINUX
  PIC=-fPIC
  STATIC=-static
else
 $(error  "Don't know how to compile on $(POSIXOS)")
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
CFLAGS += -Wall -Winline -Wredundant-decls
ifeq ($(POSIXOS),mingw)
  ifeq ($(findstring -mno-cygwin, $(CFLAGS)), -mno-cygwin)
   # compilation on mingw using the -mno-cygwin flag
   # we disable -Wformat warning because mingw uses non-standard
   # formats in printf that causes useless warnings.
   CFLAGS += -Wno-format
  endif
endif




#
# Compilation flags depending on MODE
#
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
CFLAGS := $(CFLAGS) $(PIC) -O3 -pg
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
# Need include path for yices.h
#
CPPFLAGS := -I../src $(CPPFLAGS)

#
# More CPPFLAGS for compiling static objects
#
ifneq ($(STATIC_GMP_INCLUDE_DIR),)
  STATIC_CPPFLAGS := -I$(STATIC_GMP_INCLUDE_DIR) $(CPPFLAGS)
else
  STATIC_CPPFLAGS := $(CPPFLAGS)
endif


#
# LIBS for compiling in static mode
#
# We need to remove -lgmp from LIBS in static mode, otherwise adding
# $(STATIC_GMP) does not work on Darwin and cygwin
#
STATIC_LIBS := $(STATIC_GMP) $(subst $(LIBS),-lgmp,)


#
# Dependency files
#
$(objdir)/%.d: %.c
	@ echo Building dependency file $@
	@ $(CC) -MM $(CPPFLAGS) $< > $@.tmp
	@ $(SED) 's,\($*\).o[ :]*,$(objdir)/\1.o $@ : , g' < $@.tmp > $@
	@ rm -f $@.tmp

$(static_objdir)/%.d: %.c
	@ echo Building dependency file $@
	@ $(CC) -MM $(CPPFLAGS) $< > $@.tmp
	@ $(SED) 's,\($*\).o[ :]*,$(static_objdir)/\1.o $@ : , g' < $@.tmp > $@
	@ rm -f $@.tmp


include $(dep)
include $(static_dep)



#
# bison/flex
# Note: $< must be last to work on FreeBSD
#
smt2-parse.c: smt2-parse.y smt2-lex.c
	$(YACC) -o smt2-parse.c $< 

smt2-lex.c: smt2-lex.l
	$(LEX) $< && mv lex.yy.c $@


# Object files
$(objdir)/%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(static_objdir)/%o: %c
	$(CC) $(STATIC_CPPFLAGS) $(CFLAGS) -c $< -o $@


# Binaries
$(bindir)/yices_smt2$(EXEEXT): $(obj) $(libyices)
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -o $@ $^ $(libyices) $(LIBS)

$(static_bindir)/yices_smt2$(EXEEXT): $(static_obj) $(static_libyices)
	$(LNK) $(STATIC_CPPFLAGS) $(CFLAGS) $(LDFLAGS) $(STATIC) -o $@ $^ $(static_libyices) $(STATIC_LIBS)


# All objects
obj: $(obj) $(bin_obj)

static-obj: $(static_obj) $(static_bin_obj)


#
# Top-level binaries
#
bin: $(binaries)


#
# Top-level static binaries
#
static-bin: $(static_binaries)




.PHONY: all objects bin clean static-bin

# For debugging
.DEFAULT:
	@ echo
	@ echo "*** front_end/Mafefile ***"
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
	@ echo "  LIBS     = $(LIBS)"
	@ echo "  LDFLAGS  = $(LDFLAGS)"
	@ echo "  LD       = $(LD)"
	@ echo "  AR       = $(AR)"
	@ echo "  RANLIB   = $(RANLIB)"
	@ echo "  STATIC_GMP = $(STATIC_GMP)"
	@ echo "  STATIC_GMP_INCLUDE_DIR = $(STATIC_GMP_INCLUDE_DIR)"
	@ echo

