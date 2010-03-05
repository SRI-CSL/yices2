#
# sat_solver/Makefile
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
bindir := $(BUILD)/bin


#
# OS-dependent compilation flags
# -fPIC: default on Darwin/Cygwin/Mingw (and causes 
#  compilation warning if present)
# -static: not supported by Darwin and our Solaris2.10 
# matchine
#
ifeq ($(POSIXOS),cygwin)
  CPPFLAGS := $(CPPFLAGS) -DCYGWIN
  PIC=
  STATIC=-static
else
ifeq ($(POSIXOS),mingw)
  CPPFLAGS := $(CPPFLAGS) -DMINGW
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
  PIC=-fpic
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
   # compilation on mingw using the -mno-cygwin flag
   # we disable -Wformat warning because mingw uses non-standard
   # formats in printf that causes useless warnings.
   CFLAGS += -Wno-format
  endif
endif




#
# Compilation flags depending on MODE
#
# We need to remove -lgmp from LIBS in static mode, otherwise adding
# $(STATIC_GMP) does not work on Darwin and cygwin
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
CFLAGS := $(CFLAGS) $(PIC) -O3 -pg
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

# all source files in directory
src_c := $(wildcard *.c)
src_h := $(wildcard *.h)

# dependencies
dep := $(src_c:%.c=$(objdir)/%.d)

# files to link against (we don't use Yices lib to avoid name clashes)
yices_obj := $(objdir)/memalloc.o $(objdir)/int_vectors.o $(objdir)/int_array_sort.o $(objdir)/memsize.o

# binaries
binaries := $(bindir)/sat_solver$(EXEEXT) $(bindir)/sat_solver2$(EXEEXT) \
            $(bindir)/sat_solver3$(EXEEXT) $(bindir)/sat_solver4$(EXEEXT) \
            $(bindir)/sat_solver5$(EXEEXT) $(bindir)/sat_solver6$(EXEEXT) \
            $(bindir)/sat_solver7$(EXEEXT) $(bindir)/sat_solver8$(EXEEXT) \
            $(bindir)/sat_solver9$(EXEEXT) $(bindir)/sat_solver10$(EXEEXT)

# Top-level binaries
bin: $(binaries)

$(bindir)/sat_solver$(EXEEXT): $(yices_obj) $(objdir)/sat_solver.o $(objdir)/test_sat_solver.o
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -o $@ $(objdir)/sat_solver.o $(objdir)/test_sat_solver.o \
	$(yices_obj) $(LIBS) -lm

$(bindir)/sat_solver2$(EXEEXT): $(yices_obj) $(objdir)/sat_solver2.o $(objdir)/test_sat_solver2.o
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -o $@ $(objdir)/sat_solver2.o $(objdir)/test_sat_solver2.o \
	$(yices_obj) $(LIBS) -lm

$(bindir)/sat_solver3$(EXEEXT): $(yices_obj) $(objdir)/sat_solver3.o $(objdir)/test_sat_solver3.o
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -o $@ $(objdir)/sat_solver3.o $(objdir)/test_sat_solver3.o \
	$(yices_obj) $(LIBS) -lm

$(bindir)/sat_solver4$(EXEEXT): $(yices_obj) $(objdir)/sat_solver4.o $(objdir)/test_sat_solver4.o
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -o $@ $(objdir)/sat_solver4.o $(objdir)/test_sat_solver4.o \
	$(yices_obj) $(LIBS) -lm

$(bindir)/sat_solver5$(EXEEXT): $(yices_obj) $(objdir)/sat_solver5.o $(objdir)/test_sat_solver5.o
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -o $@ $(objdir)/sat_solver5.o $(objdir)/test_sat_solver5.o \
	$(yices_obj) $(LIBS) -lm

$(bindir)/sat_solver6$(EXEEXT): $(yices_obj) $(objdir)/sat_solver6.o $(objdir)/test_sat_solver6.o
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -o $@ $(objdir)/sat_solver6.o $(objdir)/test_sat_solver6.o \
	$(yices_obj) $(LIBS) -lm

$(bindir)/sat_solver7$(EXEEXT): $(yices_obj) $(objdir)/sat_solver7.o $(objdir)/test_sat_solver7.o
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -o $@ $(objdir)/sat_solver7.o $(objdir)/test_sat_solver7.o \
	$(yices_obj) $(LIBS) -lm

$(bindir)/sat_solver8$(EXEEXT): $(yices_obj) $(objdir)/sat_solver8.o $(objdir)/test_sat_solver8.o
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -o $@ $(objdir)/sat_solver8.o $(objdir)/test_sat_solver8.o \
	$(yices_obj) $(LIBS) -lm

$(bindir)/sat_solver9$(EXEEXT): $(yices_obj) $(objdir)/sat_solver9.o $(objdir)/test_sat_solver9.o
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -o $@ $(objdir)/sat_solver9.o $(objdir)/test_sat_solver9.o \
	$(yices_obj) $(LIBS) -lm

$(bindir)/sat_solver10$(EXEEXT): $(yices_obj) $(objdir)/sat_solver10.o $(objdir)/test_sat_solver10.o
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -o $@ $(objdir)/sat_solver10.o $(objdir)/test_sat_solver10.o \
	$(yices_obj) $(LIBS) -lm



# All objects
objects: $(obj)

# Clean up
clean:
	rm -f $(objdir)/*
	rm -f $(bindir)/*


# Dependency files
$(objdir)/%.d: %.c
	@ echo Building dependency file $@
	@ $(CC) -MM $(CPPFLAGS) $< > $@.tmp
	@ $(SED) 's,\($*\).o[ :]*,$(objdir)/\1.o $@ : , g' < $@.tmp > $@
	@ rm -f $@.tmp

include $(dep)

# Object files
$(objdir)/%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@


.PHONY: all objects bin clean

# For debugging
.DEFAULT:
	@ echo
	@ echo "*** sat_solver/Mafefile ***"
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

