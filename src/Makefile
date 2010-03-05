#
# src/Makefile
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

conf=$(YICES_TOP_DIR)/$(YICES_MAKE_INCLUDE)

ifeq ($(conf),"/")
$(error "YICES_TOP_DIR and YICES_MAKE_INCLUDE are undefined")
else
include $(conf)
endif


#
# build subdirectories
#
objdir := $(BUILD)/obj
libdir := $(BUILD)/lib
bindir := $(BUILD)/bin

#
# distribution subdirectory: tarfiles are constructed
# via make binary-distribution or make smt-distribution
# 
# In this makefile, we just copy what needs to be included
# in the distribution tarfiles in $(BUILD)/dist
#
distdir := $(BUILD)/dist


#
# source files for the library
#
src_c := abstract_values.c arena.c arithmetic_variable_manager.c \
         arith_atomtable.c arith_vartable.c bit_blaster.c        \
	 bit_expr.c bit_solver.c bitvector_variable_manager.c    \
	 bv_constants.c bvarith_expr.c bvbound_cache.c           \
         bvlogic_expr.c bvpoly_buffer.c bvsolver.c cache.c       \
	 command_line.c composites.c concrete_values.c context.c \
	 context_solver.c diophantine_systems.c diseq_stacks.c   \
	 dsolver_printer.c egraph_assertion_queues.c             \
	 egraph_explanations.c egraph_utils.c egraph.c           \
	 eq_abstraction.c eq_learner.c extended_rationals.c      \
	 fun_maps.c fun_solver.c fun_trees.c gates_hash_table.c  \
	 gates_manager.c gcd.c generic_heap.c hash_functions.c   \
	 idl_floyd_warshall.c index_vectors.c int_array_sort.c   \
	 int_array_sort2.c int_bags.c int_bv_sets.c              \
         int_hash_classes.c int_hash_map.c int_hash_sets.c       \
         int_hash_tables.c int_heap.c int_heap2.c                \
         int_partitions.c int_powers.c int_queues.c int_stack.c  \
	 int_vectors.c internalization_map.c large_bvsets.c      \
         lexer.c matrices.c memalloc.c memsize.c mini_simplex.c  \
         models.c model_eval.c model_printer.c mpq_aux.c         \
         object_stores.c pair_hash_map.c pair_hash_sets.c        \
	 parser.c pointer_vectors.c poly_buffer.c                \
         polynomial_manager.c polynomials.c ptr_array_sort.c     \
         ptr_array_sort2.c ptr_hash_map.c ptr_heap.c             \
         ptr_partitions.c ptr_queues.c ptr_vectors.c             \
         rationals.c rb_bvsets.c rdl_floyd_warshall.c reader.c   \
	 refcount_strings.c remap_table.c simplex.c              \
         simplex_prop_table.c small_bvsets.c smt_core.c          \
         smt_lexer.c smt_parser.c solver_printer.c               \
         solver_export.c string_buffers.c symbol_tables.c        \
         term_api.c term_printer.c term_stack.c terms.c          \
         theory_explanations.c theory_tracer.c tree_stack.c      \
         types.c uint_rbtrees.c union_find.c use_vectors.c       \
         varproducts.c vsets.c yices_lexer.c yices_parser.c      \
         yices_reval.c yices_version.c


#
# additional source files for the binary
#
bin_src_c := yices_smt.c dl_profile.c yices_smtcomp.c yices_main.c

#
# Auto-generated version file
#
yices_version_c := yices_version.c
yices_version_o := $(objdir)/yices_version.o

#
# list of exported symbols for dynamic library
# this is used on cygwin/mingw only
#
yices_exports := yices_exports.def

# dependencies and object files to build
dep := $(src_c:%.c=$(objdir)/%.d)
obj := $(src_c:%.c=$(objdir)/%.o)

bin_dep := $(bin_src_c:%.c=$(objdir)/%.d)
bin_obj := $(bin_src_c:%.c=$(objdir)/%.o)

# static library
libyices := $(libdir)/libyices.a

# dynamic libraries
libyices_obj := $(objdir)/allyices.o
libyices_so := $(libdir)/libyices.so
libyices_dylib := $(libdir)/libyices.dylib
libyices_dll := $(libdir)/cygyices.dll
libyices_mingw_dll := $(libdir)/libyices.dll

# related files for cygwin and mingw
libyices_implib=$(libdir)/libyices.dll.a
libyices_def=$(libdir)/libyices.def


# binaries
binaries := $(bindir)/yices_smt$(EXEEXT) $(bindir)/dl_profile$(EXEEXT) \
	$(bindir)/yices_smtcomp$(EXEEXT) $(bindir)/yices_main$(EXEEXT)




#
# OS-dependent compilation flags + which dynamic libraries to build
# -fPIC: PIC is the default on Darwin/Cygwin/Mingw (and causes 
#  compilation warning if present)
# -static: is not supported by Darwin or our Solaris2.10 machine
#
ifeq ($(POSIXOS),cygwin)
  CPPFLAGS := $(CPPFLAGS) -DCYGWIN
  PIC=
  STATIC=-static
  libyices_dynamic=$(libyices_dll)
else
ifeq ($(POSIXOS),mingw)
  CPPFLAGS := $(CPPFLAGS) -DMINGW
  PIC=
  STATIC=-static
  libyices_dynamic=$(libyices_mingw_dll)
else
ifeq ($(POSIXOS),darwin)
  CPPFLAGS := $(CPPFLAGS) -DMACOSX
  CFLAGS += -fvisibility=hidden
  PIC=-fPIC
  STATIC=
  RANLIBFLAGS=-s
  libyices_dynamic=$(libyices_dylib)
else
ifeq ($(POSIXOS),sunos)
  PIC=-fpic
  STATIC=
  CPPFLAGS := $(CPPFLAGS) -DSOLARIS
  CFLAGS += -fvisibility=hidden
  libyices_dynamic=$(libyices_so)
else
ifeq ($(POSIXOS),linux)
  PIC=-fPIC
  STATIC=-static
  CPPFLAGS := $(CPPFLAGS) -DLINUX
  CFLAGS += -fvisibility=hidden
  libyices_dynamic=$(libyices_so)
else
  PIC=-fPIC
  STATIC=-static
  CFLAGS += -fvisibility=hidden
  libyices_dynamic=$(libyices_so)
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
# Compilation flags dependent on MODE
#
# We need to remove -lgmp from LIBS in static mode, otherwise adding
# $(STATIC_GMP) does not work on Darwin and cygwin
#
# Option -fomit-frame-pointer confuses the Mac OS profiling tools
# (don't use it if MODE=profile)
#
ifeq ($(YICES_MODE),release) 
CFLAGS := $(CFLAGS) -O3 -fomit-frame-pointer $(PIC)
CPPFLAGS := $(CPPFLAGS) -DNDEBUG
else 
ifeq ($(YICES_MODE),static)
ifneq ($(STATIC_GMP_INCLUDE_DIR),)
CPPFLAGS := -I$(STATIC_GMP_INCLUDE_DIR) $(CPPFLAGS)
endif
CFLAGS := $(CFLAGS) -O3 -fomit-frame-pointer $(STATIC)
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
CFLAGS := $(CFLAGS) -O3 -g $(PIC) 
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
# Which libraries to build
#
ifeq ($(YICES_MODE),release)
lib_targets=$(libyices)  $(libyices_dynamic)
else
lib_targets=$(libyices)
endif




################
#  Make rules  #
################

#
# Binaries: force generation of yices_version.c on every make bin
# 
bin: $(binaries) $(yices_version_o)
	rm -f $(yices_version_c)

# All objects
objects: $(obj) $(bin_obj)

# Static library
lib: $(lib_targets)

# Dependency files
$(objdir)/%.d: %.c
	@ echo Building dependency file $@
	@ $(CC) -MM -MG $(CPPFLAGS) $< > $@.tmp
	@ $(SED) 's,\($*\).o[ :]*,$(objdir)/\1.o $@ : , g' < $@.tmp > $@
	@ rm -f $@.tmp

ifneq ($@,clean)
include $(dep)
include $(bin_dep)
endif

# Object files
$(objdir)/%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

# static Library
$(libyices): $(obj)
	@ rm -f $(libyices)
	$(AR) cr $(libyices) $(obj)
	$(RANLIB) $(RANLIBFLAGS) $(libyices)


#
# We combine all objects into allyices.o then build the dynamic library 
# from allyices.o
#
$(libyices_obj): $(obj)
	$(LD) -r $(LDFLAGS) -o $(libyices_obj) $(obj)


#
# For dynamic libraries, the rules are platform dependent.
#

#
# linux + solaris
#
$(libyices_so): $(libyices_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -o $(libyices_so) $(libyices_obj) $(LIBS)
	$(STRIP) -x $(libyices_so)

#
# DLL on cygwin
# the DLL is called cygyices.dll
# the linker creates libyices.dll.a (import library)
# the flag --no-whole-archive suppresses inclusion of all objects
# stored in $(LIBS) in cygyices.dll
#
# To use these files on cygwin
# copy libyices.dll.a in /lib (or /usr/lib)
# copy cygyices.dll in /bin (or /usr/bin)
# link the code using the flags -lyices -lgmp
#
$(libyices_dll): $(libyices_obj) $(yices_exports)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -o $(libyices_dll) \
	-Wl,--out-implib=$(libyices_implib) --no-whole-archive $(libyices_obj) \
	$(LIBS) $(yices_exports)
	$(STRIP) $(libyices_dll)

#
# DLL on mingw: more-or-less like cygwin
# the DLL is called libyices.dll
# the --no-whole-archive file is removed so that libgmp.a gets included in libyices.dll
# the linker creates libyices.dll.a (import library) and libyices.def
#
# To use libyices.dll on windows
# construct libyices.lib from def using the Microsoft lib tool
#    lib /machine:i386 /def:libyices.def
#
$(libyices_mingw_dll): $(libyices_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -o $(libyices_mingw_dll) \
	-Wl,--out-implib=$(libyices_implib) -Wl,--output-def,$(libyices_def) \
	$(libyices_obj) $(LIBS) $(yices_exports)
	$(STRIP) $(libyices_mingw_dll)


#
# Special dynamic library tricks for Mac OS X:
# - give libyices.dylib as the install_name
# - for this to work, the dynamic library has to be copied into
#   the /usr/local/lib directory, with that exact name.
# - the user can change this by using install_name_tool
# - we give option -headerpad_max_install_names so that user can safely
# change the install name using install_name_tool.
# 
$(libyices_dylib): $(libyices_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -dynamiclib -current_version 2.0 -compatibility_version 2.0 \
	$(libyices_obj) $(LIBS) -o $(libyices_dylib) \
	-Wl,-install_name,libyices.dylib
	$(STRIP) -x $(libyices_dylib)



#
# Executables
#
$(bindir)/%$(EXEEXT): $(objdir)/%.o $(yices_version_o) $(libyices)
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -o $@ $< $(yices_version_o) $(libyices) $(LIBS)


#
# Gperf generated tables
# - we need to give different names to the yices and smt lookup functions
#
yices_hash_keywords.h: yices_keywords.txt
	$(GPERF) -C -G -L ANSI-C -W yices_kw --output-file=yices_hash_keywords.h \
	--lookup-function-name=in_yices_kw yices_keywords.txt

smt_hash_keywords.h: smt_keywords.txt
	$(GPERF) -C -G -L ANSI-C -W smt_kw --output-file=smt_hash_keywords.h \
	--lookup-function-name=in_smt_kw smt_keywords.txt


#
# Compilation date + svn repository and version
#
now := $(shell date)

url := $(shell ( svn info $(YICES_TOP_DIR) 2>&1 | grep URL ) || echo URL: unknown)
ifeq ($(url), URL: unknown) 
  rev := unknown
else 
  rev := $(shell ( svnversion $(YICES_TOP_DIR) 2>&1 ) )
endif

yices_version.c:
	$(SED) -e 's/YICES_COMPILATION_DATE/$(now)/g' -e 's;SVN_URL;$(url);g' -e 's/SVN_REVISION/$(rev)/g' \
	  -e 's/YICES_ARCH/$(ARCH)/g' -e 's/YICES_BUILD_MODE/$(YICES_MODE)/g' yices_version_template.txt > $@






##########################
#  BINARY DISTRIBUTIONS  #
##########################

#
# OS-dependent flags for strip + what needs to be copied
# into the lib directory
# TODO: adjust this depending on OS
#
ifeq ($(POSIXOS),linux)
  STRIPFLAGS= 
  libs_for_dist = $(lib_targets)
else 
  STRIPFLAGS=
  libs_for_dist = $(lib_targets)
endif

#
# Just copy the required binaries, libraries, include files into
# distdir
# 
binary-distribution: bin lib
	rm -r -f $(distdir)/*
	mkdir $(distdir)/bin
	cp $(bindir)/yices_main$(EXEEXT) $(distdir)/bin/yices$(EXEEXT)
	cp $(bindir)/yices_smt$(EXEEXT) $(distdir)/bin/yices_smt$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(distdir)/bin/yices$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(distdir)/bin/yices_smt$(EXEEXT)
	mkdir $(distdir)/lib
	cp $(lib_targets) $(distdir)/lib
	mkdir $(distdir)/include
	cp yices.h yices_types.h yices_limits.h yices_exit_codes.h $(distdir)/include


smt-distribution: bin
	rm -r -f $(distdir)/*
	mkdir $(distdir)/bin
	cp $(bindir)/yices_smtcomp$(EXEEXT) $(distdir)/bin/yices$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(distdir)/bin/yices$(EXEEXT)



############
#  OTHERS  #
############

#
# rules to avoid triggering the .DEFAULT rule if .h or .c files have been deleted
#
%.h:
	@ echo "$@ missing"

%.c:
	@ echo
	@ echo "Missing source file: $@"
	@ echo


#
# For debugging of Makefile and configuration:
# print the options as set by this Makefile
#
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
	@ echo "  LIBS     = $(LIBS)"
	@ echo "  LDFLAGS  = $(LDFLAGS)"
	@ echo "  LD       = $(LD)"
	@ echo "  AR       = $(AR)"
	@ echo "  RANLIB   = $(RANLIB)"
	@ echo "  STRIP    = $(STRIP)"
	@ echo "  STATIC_GMP = $(STATIC_GMP)"
	@ echo "  STATIC_GMP_INCLUDE_DIR = $(STATIC_GMP_INCLUDE_DIR)"
	@ echo



.PHONY: objects lib bin

