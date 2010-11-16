#
# src/Makefile
#
# Must be invoked with the following variables set
#
#   YICES_TOP_DIR = top-level directory for Yices
#   YICES_MODE = build mode
#   YICES_MAKE_INCLUDE = configuration file to include
#   YICES_VERSION = full version
#   MAJOR = major version number
#   MINOR = minor version number
#   PATCH_LEVEL = patch level
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
# Build subdirectories
# --------------------
# build/obj: object files, in a form suitable for the dynamic libraries
#            (e.g., compiled with option -fPIC)
# build/static_obj: object files compiled in a form suitable for libyices.a
#            (e.g., compiled without -fPIC)
#
# build/lib: libraries (GMP not included)
# build/bin: binaries (GMP not included)
#
# build/static_lib: libraries (GMP included)
# build/static_bin: binaries linked statically with GMP (and other libraries if possible)
#
objdir := $(BUILD)/obj
libdir := $(BUILD)/lib
bindir := $(BUILD)/bin

static_objdir := $(BUILD)/static_obj
static_libdir := $(BUILD)/static_lib
static_bindir := $(BUILD)/static_bin

#
# Distribution subdirectory: tarfiles are constructed
# via make binary-distribution or make smt-distribution
# 
# In this makefile, we just copy what needs to be included
# in the distribution tarfiles in $(BUILD)/dist or $(BUILD)/static_dist
#
distdir := $(BUILD)/dist
static_distdir := $(BUILD)/static_dist


#
# source files for libyices
#
src_c := abstract_values.c arena.c arith_atomtable.c arith_buffers.c \
         arith_buffer_terms.c arith_solver_codes.c arith_vartable.c  \
         backtrack_arrays.c bit_expr.c bit_term_conversion.c         \
         bvarith_buffers.c bvarith_buffer_terms.c                    \
         bvarith64_buffers.c bvarith64_buffer_terms.c                \
         bvlogic_buffers.c bv_constants.c bv64_constants.c           \
         bv_polynomials.c bv64_polynomials.c cache.c command_line.c  \
         composites.c concrete_values.c context.c context_printer.c  \
         context_solver.c diophantine_systems.c diseq_stacks.c       \
         dl_vartable.c dsolver_printer.c egraph_assertion_queues.c   \
         egraph_explanations.c egraph_utils.c egraph.c               \
         egraph_printer.c eq_abstraction.c eq_learner.c              \
         extended_rationals.c fun_maps.c fun_solver.c fun_trees.c    \
         gates_hash_table.c gates_manager.c gates_printer.c gcd.c    \
         generic_heap.c hash_functions.c idl_floyd_warshall.c        \
         idl_fw_printer.c index_vectors.c int_array_sort.c           \
         int_array_sort2.c int_bags.c int_bv_sets.c                  \
         int_hash_classes.c int_hash_map.c int_hash_map2.c           \
         int_hash_sets.c int_hash_tables.c int_heap.c int_heap2.c    \
         int_partitions.c int_powers.c int_queues.c int_stack.c      \
         int_vectors.c internalization_table.c                       \
         internalization_printer.c large_bvsets.c lexer.c            \
         mark_vectors.c matrices.c memalloc.c memsize.c models.c     \
         mpq_aux.c object_stores.c pair_hash_map.c pair_hash_map2.c  \
         pair_hash_sets.c parser.c pointer_vectors.c polynomials.c   \
         poly_buffer.c power_products.c pprod_table.c                \
         pretty_printer.c pseudo_subst.c ptr_array_sort.c            \
         ptr_array_sort2.c ptr_hash_map.c ptr_heap.c                 \
         ptr_partitions.c ptr_queues.c ptr_vectors.c rationals.c     \
	 rational_hash_maps.c rb_bvsets.c rdl_floyd_warshall.c       \
         rdl_fw_printer.c reader.c refcount_strings.c simplex.c      \
         simplex_printer.c simplex_prop_table.c small_bvsets.c       \
         smt_core.c smt_core_printer.c smt_lexer.c smt_logic_codes.c \
         smt_parser.c string_buffers.c symbol_tables.c terms.c       \
         term_printer.c term_stack.c term_stack_error.c term_utils.c \
         theory_explanations.c timeout.c types.c type_printer.c      \
         uint_rbtrees.c union_find.c use_vectors.c vsets.c           \
         yices_api.c yices_error.c yices_lexer.c yices_pp.c          \
         yices_parser.c yices_reval.c


#
# additional source files for the binaries
#
bin_src_c := yices_main.c yices_smtcomp.c yices_smt.c

#
# Auto-generated version file
#
version_c := yices_version.c

#
# Dependencies and object files
#
obj := $(src_c:%.c=$(objdir)/%.o)
dep := $(src_c:%.c=$(objdir)/%.d)
static_obj := $(src_c:%.c=$(static_objdir)/%.o)
static_dep := $(src_c:%.c=$(static_objdir)/%.d)

bin_obj := $(bin_src_c:%.c=$(objdir)/%.o)
bin_dep := $(bin_src_c:%.c=$(objdir)/%.d)
static_bin_obj = $(bin_src_c:%.c=$(static_objdir)/%.o)
static_bin_dep = $(bin_src_c:%.c=$(static_objdir)/%.d)

version_obj := $(objdir)/yices_version.o
version_dep := $(version_c:%.c=$(objdir)/%.d)
static_version_obj := $(static_objdir)/yices_version.o
static_version_dep := $(static_objdir)/yices_version.d


#
# Static libraries
#
libyices := $(libdir)/libyices.a
static_libyices := $(static_libdir)/libyices.a

#
# Binaries
#
binaries := $(bin_src_c:%.c=$(bindir)/%$(EXEEXT))
static_binaries := $(bin_src_c:%.c=$(static_bindir)/%$(EXEEXT))


#
# DYNAMIC LIBRARIES
#

#
# Linux:
# the library has full versioned name libyices.so.2.0.0
# soname: libyices.so.2.0
#
libyices_so := libyices.so.$(YICES_VERSION)
libyices_soname := libyices.so.$(MAJOR).$(MINOR)

# 
# Darwin
# library name: libyices.2.dylib
# version and compatibility numbers for Darwin
# install name: /usr/local/lib/libyices.2.dylib
#
libyices_dylib := libyices.$(MAJOR).dylib
libyices_curr_version := $(MAJOR).$(MINOR).$(PATCH_LEVEL)
libyices_compat_version := $(MAJOR).$(MINOR).0
libyices_install_name := /usr/local/lib/$(libyices_dylib)

#
# Cygwin and mingw:
# the DLL is called cygyices.dll on cygwin
#               and libyices.dll on mingw
# both systems use an import library called libyices.dll.a
#
# On mingw, we also produce libyices.def, which can be
# used to produce an import library compatible with the Microsoft
# compilation tools (and Visual Studio).
#
libyices_dll := cygyices.dll
libyices_mingw_dll := libyices.dll

libyices_implib=libyices.dll.a
libyices_def=libyices.def


#
# OS-dependent compilation flags + which dynamic libraries to build
#
# -fPIC: PIC is the default on Darwin/Cygwin/Mingw (and causes 
#  compilation warning on the latter two if present)
#
# -static: is not supported by Darwin or our Solaris2.10 machine
#
# BIN_LDFLAGS: LDFLAGS used when building executables 
#  this is used to increase the stack size on cygwin/mingw (to 8Mbytes)
#
ifeq ($(POSIXOS),cygwin)
  CPPFLAGS := $(CPPFLAGS) -DCYGWIN
  PIC=
  STATIC=-static -static-libgcc
  BIN_LDFLAGS= -Wl,--stack,8388608
  libyices_dynamic=$(libyices_dll)
else
ifeq ($(POSIXOS),mingw)
  CPPFLAGS := $(CPPFLAGS) -DMINGW
  PIC=
  STATIC=-static
  BIN_LDFLAGS= -Wl,--stack,8388608
  libyices_dynamic=$(libyices_mingw_dll)
else
ifeq ($(POSIXOS),darwin)
  CPPFLAGS := $(CPPFLAGS) -DMACOSX
  CFLAGS += -fvisibility=hidden
  PIC=-fPIC
  STATIC=
  BIN_LDFLAGS=
  libyices_dynamic=$(libyices_dylib)
else
ifeq ($(POSIXOS),sunos)
  PIC=-fPIC
  STATIC=
  CPPFLAGS := $(CPPFLAGS) -DSOLARIS
  CFLAGS += -fvisibility=hidden
  BIN_LDFLAGS=
  libyices_dynamic=$(libyices_so)
else
ifeq ($(POSIXOS),linux)
  PIC=-fPIC
  STATIC=-static
  CPPFLAGS := $(CPPFLAGS) -DLINUX
  CFLAGS += -fvisibility=hidden
  BIN_LDFLAGS=
  libyices_dynamic=$(libyices_so)
else
 $(error "Don't know how to compile on $(POSIXOS)")
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
   # For compilation on mingw using the -mno-cygwin flag,
   # we disable -Wformat warning because mingw uses non-standard
   # formats in printf that cause useless warnings.
   CFLAGS += -Wno-format
  endif
endif



#
# Compilation flags dependent on MODE
#
# Option -fomit-frame-pointer confuses the Mac OS profiling tools
# (don't use it if MODE=profile)
#
ifeq ($(YICES_MODE),release) 
CFLAGS := $(CFLAGS) -O3 -fomit-frame-pointer
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
# More CPPFLAGS for compiling static objects
#
ifneq ($(STATIC_GMP_INCLUDE_DIR),)
  STATIC_CPPFLAGS := -I$(STATIC_GMP_INCLUDE_DIR) $(CPPFLAGS)
else
  STATIC_CPPFLAGS := $(CPPFLAGS)
endif

ifeq ($(POSIXOS),cygwin)
  STATIC_CPPFLAGS += -DNOYICES_DLL
else
ifeq ($(POSIXOS),mingw)
  STATIC_CPPFLAGS += -DNOYICES_DLL
endif
endif


#
# LIBS for compiling in static mode
#
# We need to remove -lgmp from LIBS in static mode, otherwise adding
# $(STATIC_GMP) does not work on Darwin and cygwin
#
STATIC_LIBS := $(STATIC_GMP) $(subst $(LIBS),-lgmp,)




#################
#  BUILD RULES  #
#################

#
# Dependency files
#
$(objdir)/%.d: %.c
	@ echo Building dependency file $@
	@ $(CC) -MM -MG $(CPPFLAGS) $< > $@.tmp
	@ $(SED) 's,\($*\).o[ :]*,$(objdir)/\1.o $@ : , g' < $@.tmp > $@
	@ rm -f $@.tmp

$(static_objdir)/%.d: %.c
	@ echo Building dependency file $@
	@ $(CC) -MM -MG $(STATIC_CPPFLAGS) $< > $@.tmp
	@ $(SED) 's,\($*\).o[ :]*,$(static_objdir)/\1.o $@ : , g' < $@.tmp > $@
	@ rm -f $@.tmp

include $(dep)
include $(bin_dep)
include $(version_dep)
include $(static_dep)
include $(static_bin_dep)
include $(static_version_dep)



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
# Version file
# Compilation date and mode, svn repository and version, and version numbers
# are copied into yices_version.c.
#
now := $(shell date)

url := $(shell ( svn info $(YICES_TOP_DIR) 2>&1 | grep URL ) || echo URL: unknown)
ifeq ($(url), URL: unknown) 
  rev := unknown
else 
  rev := $(shell ( svnversion $(YICES_TOP_DIR) 2>&1 ) )
endif

yices_version.c: yices_version_template.txt
	$(SED) -e 's/YICES_VERSION/$(YICES_VERSION)/g' -e 's/YICES_COMPILATION_DATE/$(now)/g' \
               -e 's;SVN_URL;$(url);g' -e 's/SVN_REVISION/$(rev)/g' \
	       -e 's/YICES_ARCH/$(ARCH)/g' -e 's/YICES_BUILD_MODE/$(YICES_MODE)/g' \
               yices_version_template.txt > $@



#
# Object files
#
$(objdir)/%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) $(PIC) -c $< -o $@

$(static_version_obj): yices_version.c
	$(CC) -DYICES_STATIC $(STATIC_CPPFLAGS) $(CFLAGS) -c yices_version.c -o $(static_version_obj)

$(static_objdir)/%o: %c
	$(CC) $(STATIC_CPPFLAGS) $(CFLAGS) -c $< -o $@

#
# Static libraries
#
# Right now, the dynamic and static libyices.a are the same.
# I'd like to include libgmp.a in the static libyices.a but 
# I haven't found a good way to do it.
# 
$(libyices): $(obj) $(version_obj)
	@ rm -f $(libyices)
	$(AR) cr $(libyices) $(obj) $(version_obj)
	$(RANLIB) $(libyices)

$(static_libyices):  $(static_obj) $(static_version_obj)
	@ rm -f $(static_libyices)
	$(AR) cr $(static_libyices) $(static_obj) $(static_version_obj)
	$(RANLIB) $(static_libyices)


#
# Executables
#
$(bindir)/%$(EXEEXT): $(objdir)/%.o $(libyices)
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) $(BIN_LDFLAGS) \
           -o $@ $< $(libyices) $(LIBS)

$(static_bindir)/%$(EXEEXT): $(static_objdir)/%.o $(static_libyices)
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) $(BIND_LDFLAGS) $(STATIC) \
          -o $@ $< $(static_libyices) $(STATIC_LIBS)



#
# For dynamic libraries, the rules are platform-dependent.
#

#
# linux + solaris
#
$(libdir)/$(libyices_so): $(obj) $(version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -o $@ \
	-Wl,-soname,$(libyices_soname) $(obj) $(version_obj) $(LIBS)
	$(STRIP) -x $@

$(static_libdir)/$(libyices_so): $(obj) $(version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -o $@ \
	-Wl,-soname,$(libyices_soname) $(obj) $(version_obj) $(PIC_GMP)
	$(STRIP) -x $@


#
# DLL on cygwin
# the DLL is called cygyices.dll
# the linker creates libyices.dll.a (import library)
#
# To use these files on cygwin
# copy libyices.dll.a in /lib (or /usr/lib)
# copy cygyices.dll in /bin (or /usr/bin)
# link the code using the flags -lyices -lgmp
#
$(libdir)/$(libyices_dll): $(obj) $(version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -o $@ \
	-Wl,--out-implib=$(libdir)/$(libyices_implib) \
	$(obj) $(version_obj) $(LIBS)
	$(STRIP) $@

$(static_libdir)/$(libyices_dll): $(static_obj) $(static_version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -o $@ \
	-Wl,--out-implib=$(static_libdir)/$(libyices_implib) \
	$(static_obj) $(static_version_obj) $(PIC_GMP)
	$(STRIP) -x $@


#
# DLL on mingw: more-or-less like cygwin
# the DLL is called libyices.dll
# the linker creates libyices.dll.a (import library) and libyices.def
#
# To use libyices.dll on windows
# construct libyices.lib from libyices.def using the Microsoft lib tool
#    lib /machine:i386 /def:libyices.def
#
$(libdir)/$(libyices_mingw_dll): $(obj) $(version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -o $@ \
	-Wl,--out-implib=$(libdir)/$(libyices_implib) \
	-Wl,--output-def,$(libdir)/$(libyices_def) \
	$(obj) $(version_obj) $(LIBS)
	$(STRIP) $@

$(static_libdir)/$(libyices_mingw_dll): $(static_obj) $(static_version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -o $@ \
	-Wl,--out-implib=$(static_libdir)/$(libyices_implib) \
	-Wl,--output-def,$(static_libdir)/$(libyices_def) \
	$(static_obj) $(static_version_obj) $(PIC_GMP)
	$(STRIP) $@


#
# Special dynamic tricks for Mac OS X:
# - the compatibility version is MAJOR.MINOR.0
# - the current version is MAJOR.MINOR.PATCH_LEVEL
# - install name: /usr/local/lib/libyices.MAJOR.dylib
# - option -headerpad_max_install_names allows users to
#   safely change the install name using install_name_tool.
#
$(libdir)/$(libyices_dylib): $(obj) $(version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -dynamiclib -o $@ \
	-current_version $(libyices_curr_version) \
	-compatibility_version $(libyices_compat_version) \
	-Wl,-install_name,$(libyices_install_name) \
	-Wl,-headerpad_max_install_names \
	-Wl,-dead_strip \
	-Wl,-single_module \
	$(obj) $(version_obj) $(LIBS) 
	$(STRIP) -x $@

$(static_libdir)/$(libyices_dylib): $(obj) $(version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -dynamiclib -o $@ \
	-current_version $(libyices_curr_version) \
	-compatibility_version $(libyices_compat_version) \
	-Wl,-install_name,$(libyices_install_name) \
	-Wl,-headerpad_max_install_names \
	-Wl,-dead_strip \
	-Wl,-single_module \
	$(obj) $(version_obj) $(PIC_GMP)
	$(STRIP) -x $@



# All objects
obj: $(obj) $(bin_obj)

static-obj: $(static_obj) $(static_bin_obj)

# Binaries
bin: $(binaries)

static-bin: $(static_binaries)

# Libraries
lib: $(libyices) $(libdir)/$(libyices_dynamic)

static-lib: $(static_libyices) $(static_libdir)/$(libyices_dynamic)


.PHONY: obj static-obj bin static-bin lib static-lib




##########################
#  BINARY DISTRIBUTIONS  #
##########################

#
# OS-dependent flags for strip
# TODO: adjust this depending on OS
#
STRIPFLAGS= 

#
# Just copy the required binaries, libraries, include files into
# distdir
#
dist: bin lib
	rm -r -f $(distdir)/*
	mkdir $(distdir)/include
	cp yices.h yices_types.h yices_limits.h yices_exit_codes.h $(distdir)/include
	mkdir $(distdir)/bin
	cp $(bindir)/yices_main$(EXEEXT) $(distdir)/bin/yices$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(distdir)/bin/yices$(EXEEXT)
	mkdir $(distdir)/lib
	cp $(libdir)/* $(distdir)/lib
	$(STRIP) -x $(distdir)/lib/libyices.a

static-dist: static-bin static-lib
	rm -r -f $(static_distdir)/*
	mkdir $(static_distdir)/include
	cp yices.h yices_types.h yices_limits.h yices_exit_codes.h $(static_distdir)/include
	mkdir $(static_distdir)/bin
	cp $(static_bindir)/yices_main$(EXEEXT) $(static_distdir)/bin/yices$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(static_distdir)/bin/yices$(EXEEXT)
	mkdir $(static_distdir)/lib
	cp $(static_libdir)/* $(static_distdir)/lib
	$(STRIP) -x $(static_distdir)/lib/libyices.a


.PHONY: dist static-dist


############
#  OTHERS  #
############

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


