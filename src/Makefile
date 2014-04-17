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
#	    (e.g., compiled with option -fPIC)
# build/static_obj: object files compiled in a form suitable for libyices.a
#	    (e.g., compiled without -fPIC)
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
smt_distdir := $(BUILD)/smt_dist
static_smt_distdir := $(BUILD)/static_smt_dist



#
# SOURCE FILES
#

#
# Source files for the dynamic library (libyices.so)
#
base_src_c := abstract_values.c arena.c arith_atomtable.c		\
              arith_vartable.c attribute_values.c backtrack_arrays.c	\
              balanced_arith_buffers.c bit_blaster.c bit_expr.c		\
              bit_term_conversion.c bvarith_buffers.c			\
              bvarith_buffer_terms.c bvarith64_buffers.c		\
              bvarith64_buffer_terms.c bvlogic_buffers.c		\
              bv_atomtable.c bv_constants.c bv64_constants.c		\
              bvconst_hmap.c bv_intervals.c bv64_intervals.c		\
              bv_polynomials.c bv64_polynomials.c bvpoly_buffers.c	\
              bvpoly_compiler.c bvpoly_dag.c bvsolver.c bv_vartable.c	\
              bvexp_table.c cache.c composites.c concrete_values.c	\
              concrete_value_printer.c context.c context_config.c	\
              context_simplifier.c context_solver.c                     \
              context_statistics.c csets.c dep_tables.c                 \
              diophantine_systems.c diseq_stacks.c dl_vartable.c        \
              ef_analyze.c ef_problem.c efsolver.c	                \
              egraph_assertion_queues.c egraph_explanations.c		\
              egraph_utils.c egraph.c elim_subst.c eq_abstraction.c     \
              eq_learner.c extended_rationals.c flattening.c            \
              free_var_collector.c fresh_value_maker.c full_subst.c     \
              fun_maps.c fun_solver.c fun_trees.c gates_hash_table.c    \
              gates_manager.c gcd.c generic_heap.c hash_functions.c	\
              idl_floyd_warshall.c ilists.c index_vectors.c		\
              int_array_hsets.c int_array_sort.c int_array_sort2.c	\
              int_bags.c int_bv_sets.c int_hash_classes.c		\
              int_hash_map.c int_hash_map2.c int_hash_sets.c		\
              int_hash_tables.c int_heap.c int_heap2.c			\
              int_partitions.c int_powers.c int_queues.c int_stack.c	\
              int_vectors.c internalization_table.c lexer.c		\
              literal_collector.c map_to_model.c mark_vectors.c		\
              matrices.c memalloc.c merge_table.c models.c		\
              model_eval.c model_printer.c mpq_aux.c object_stores.c	\
              offset_equalities.c pair_hash_map2.c parser.c		\
              pointer_vectors.c polynomials.c poly_buffer.c		\
              poly_buffer_terms.c power_products.c pprod_table.c	\
              pretty_printer.c pseudo_subst.c ptr_array_sort.c		\
              ptr_array_sort2.c ptr_hash_classes.c ptr_hash_map.c	\
              ptr_heap.c ptr_partitions.c ptr_queues.c ptr_stack.c	\
              ptr_vectors.c rationals.c rational_hash_maps.c		\
              rba_buffer_terms.c rdl_floyd_warshall.c reader.c		\
              refcount_int_arrays.c refcount_strings.c remap_table.c	\
              renaming_context.c search_parameters.c simplex.c		\
              smt_core.c smt_logic_codes.c smt_term_stack.c		\
              sparse_arrays.c stable_sort.c string_buffers.c		\
              string_utils.c subst_cache.c subst_context.c		\
              symbol_tables.c symmetry_breaking.c terms.c		\
              term_manager.c term_printer.c term_sets.c term_stack2.c   \
              term_stack_error.c term_substitution.c term_to_val.c	\
              term_utils.c theory_explanations.c tracer.c		\
              tuple_hash_map.c types.c type_printer.c uint_rbtrees.c	\
              use_vectors.c val_to_term.c variable_renaming.c		\
              yices_api.c yices_error.c yices_lexer.c yices_pp.c	\
              yices_parser.c

#
# Other source files for libyices.a
# That's all the code needed by the main binaries
# + experimental/unfinished modules
# + functions for printing/debugging
# + old stuff not needed anymore (except for tests)
#
extra_src_c := arith_buffers.c arith_solver_codes.c			\
               bvsolver_printer.c bool_vartable.c booleq_table.c	\
               command_line.c cputime.c context_printer.c		\
               dimacs_printer.c dsolver_printer.c dump_context.c	\
               egraph_printer.c egraph_eq_stats.c			\
               fun_solver_printer.c gates_printer.c idl_fw_printer.c	\
               internalization_printer.c large_bvsets.c memsize.c	\
               pair_hash_map.c pair_hash_sets.c parenthesized_expr.c	\
               rb_bvsets.c rdl_fw_printer.c sat_solver.c		\
               simplex_printer.c simplex_prop_table.c small_bvsets.c	\
               smt_core_printer.c smt_lexer.c smt_parser.c		\
               smt2_commands.c smt2_expressions.c smt2_lexer.c		\
               smt2_model_printer.c smt2_parser.c smt2_printer.c	\
               smt2_term_stack.c string_hash_map.c tag_map.c		\
               timeout.c union_find.c update_graph.c yices_help.c	\
               yices_reval.c

src_c := $(base_src_c) $(extra_src_c)


#
# additional source files for the binaries
#
bin_src_c := yices_main.c yices_smtcomp.c yices_smt.c yices_sat.c yices_smt2.c

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
static_version_dep := $(version_c:%.c=$(static_objdir)/%.d)


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
# Linux/Solaris/FreeBSD
# the library has full versioned name libyices.so.2.X.Y
# soname: libyices.so.2.X
#
# For Free BSD: the convention seems to call the file libyices.so.2.X
#
ifeq ($(POSIXOS),freebsd)
libyices_so := libyices.so.$(MAJOR).$(MINOR)
else
libyices_so := libyices.so.$(YICES_VERSION)
endif

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
libyices_install_name := /usr/local/lib/libyices.$(MAJOR).dylib

#
# Cygwin and mingw:
# the DLL is called cygyices.dll on cygwin
#	       and libyices.dll on mingw
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




###########################
#   COMPILATION FLAGS     #
###########################

#
# OS-dependent compilation flags + which dynamic libraries to build
#    libyices_dynamic = dynamic library for make lib
#    static_libyices_dynamic = dynamic library for make static-lib
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
  libyices_dynamic=$(bindir)/$(libyices_dll)
  static_libyices_dynamic=$(static_bindir)/$(libyices_dll)
else
ifeq ($(POSIXOS),mingw)
  CPPFLAGS := $(CPPFLAGS) -DMINGW
  PIC=
  STATIC=-static -static-libgcc
  BIN_LDFLAGS= -Wl,--stack,8388608
  libyices_dynamic=$(bindir)/$(libyices_mingw_dll)
  static_libyices_dynamic=$(static_bindir)/$(libyices_mingw_dll)
else
ifeq ($(POSIXOS),darwin)
  CPPFLAGS := $(CPPFLAGS) -DMACOSX
  CFLAGS += -fvisibility=hidden
  PIC=-fPIC
  STATIC=
  BIN_LDFLAGS=
  libyices_dynamic=$(libdir)/$(libyices_dylib)
  static_libyices_dynamic=$(static_libdir)/$(libyices_dylib)
else
ifeq ($(POSIXOS),sunos)
  PIC=-fPIC
  STATIC=
  CPPFLAGS := $(CPPFLAGS) -DSOLARIS
  CFLAGS += -fvisibility=hidden
  BIN_LDFLAGS=
  libyices_dynamic=$(libdir)/$(libyices_so)
  static_libyices_dynamic=$(static_libdir)/$(libyices_so)
else
ifeq ($(POSIXOS),linux)
  PIC=-fPIC
  STATIC=-static
  CPPFLAGS := $(CPPFLAGS) -DLINUX
  CFLAGS += -fvisibility=hidden
  BIN_LDFLAGS=
  libyices_dynamic=$(libdir)/$(libyices_so)
  static_libyices_dynamic=$(static_libdir)/$(libyices_so)
else
ifeq ($(POSIXOS),freebsd)
  PIC=-fPIC
  STATIC=-static
  CPPFLAGS := $(CPPFLAGS) -DFREEBSD
  CFLAGS += -fvisibility=hidden
  BIN_LDFLAGS=
  libyices_dynamic=$(libdir)/$(libyices_so)
  static_libyices_dynamic=$(static_libdir)/$(libyices_so)

else
ifeq ($(POSIXOS),unix)
  PIC=-fPIC
  STATIC=-static
  CPPFLAGS := $(CPPFLAGS) -DLINUX
  CFLAGS += -fvisibility=hidden
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

#
# include dirs: we want -I. first
#
CPPFLAGS := -I. $(CPPFLAGS)

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
# (don't use it if MODE=profile).
#
# Option -fno-stack-protector is useful on Ubuntu (and probably other
# Linux distributions). On these distributions, gcc has
# -fstack-protector enabled by default. This can cause link-time
# errors on the user's systems:
#    undefined reference to '__stack_chk_fail'.
# However this option is not supported by older versions of GCC (before gcc-4.1?)
#
# Update: 02/16/2012: we check whether -fno-stack-protector is supported
# in the configure script. The script sets variable $(NO_STACK_PROTECTOR)
# properly.
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
# Object files to include in the dynamic libraries
#
ifeq ($(YICES_MODE),release)
base_obj := $(base_src_c:%.c=$(objdir)/%.o)
static_base_obj := $(base_src_c:%.c=$(static_objdir)/%.o)
else
base_obj := $(obj)
static_base_obj := $(static_obj)
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
LNK := $(CC)
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
# We also use $(NOGMP_LIBS) to build yices_sat.
#
NOGMP_LIBS := $(subst $(LIBS),-lgmp,)
STATIC_LIBS := $(STATIC_GMP) $(NOGMP_LIBS)




#################
#  BUILD RULES  #
#################

#
# Dependency files
#
$(objdir)/%.d: %.c
	@set -e; echo Building dependency file $@ ; \
	$(CC) -MM -MG $(CFLAGS) $(CPPFLAGS) $< > $@.$$$$ ; \
	$(SED) 's,\($*\).o[ :]*,$(objdir)/\1.o $@ : , g' < $@.$$$$ > $@ ; \
	rm -f $@.$$$$

$(static_objdir)/%.d: %.c
	@set -e; echo Building dependency file $@ ; \
	$(CC) -MM -MG $(CFLAGS) $(STATIC_CPPFLAGS) $< > $@.$$$$ ; \
	$(SED) 's,\($*\).o[ :]*,$(static_objdir)/\1.o $@ : , g' < $@.$$$$ > $@ ; \
	rm -f $@.$$$$


ifneq ($(MAKECMDGOALS),clean)

include $(dep)
include $(bin_dep)
include $(version_dep)
include $(static_dep)
include $(static_bin_dep)
include $(static_version_dep)

endif


#
# Gperf generated tables
# - we need to give different names to the yices and smt lookup functions
#
yices_hash_keywords.h: yices_keywords.txt
	$(GPERF) -C -L ANSI-C -W yices_kw --output-file=yices_hash_keywords.h \
	--lookup-function-name=in_yices_kw yices_keywords.txt

smt_hash_keywords.h: smt_keywords.txt
	$(GPERF) -C -L ANSI-C -W smt_kw --output-file=smt_hash_keywords.h \
	--lookup-function-name=in_smt_kw smt_keywords.txt

#
# Tables for SMT2:
# - we want to include three hash functions in the same file (smt2_lexer.c)
# - for this to work,
#   we need to give different names to the hash function (option -H ...)
#   we can't use -G and we must give -E
#
smt2_hash_tokens.h: smt2_tokens.txt
	$(GPERF) -C -L ANSI-C -W smt2_tk -H hash_tk -E --output-file=smt2_hash_tokens.h \
	--lookup-function-name=in_smt2_tk smt2_tokens.txt

smt2_hash_keywords.h: smt2_keywords.txt
	$(GPERF) -C -L ANSI-C -W smt2_kw -H hash_kw -E --output-file=smt2_hash_keywords.h \
	--lookup-function-name=in_smt2_kw smt2_keywords.txt

smt2_hash_symbols.h: smt2_symbols.txt
	$(GPERF) -C -L ANSI-C -W smt2_sym -H hash_sym -E --output-file=smt2_hash_symbols.h \
	--lookup-function-name=in_smt2_sym smt2_symbols.txt

#
# Object files
#
$(objdir)/%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) $(PIC) -c $< -o $@

$(static_version_obj): yices_version.c
	$(CC) -DYICES_STATIC $(STATIC_CPPFLAGS) $(CFLAGS) -c yices_version.c -o $(static_version_obj)

$(static_objdir)/%.o: %.c
	$(CC) $(STATIC_CPPFLAGS) $(CFLAGS) -c $< -o $@

#
# Static libraries
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

# for yices_sat: we don't need gmp
$(bindir)/yices_sat$(EXEEXT): $(objdir)/yices_sat.o $(libyices)
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) $(BIN_LDFLAGS) \
	   -o $@ $< $(libyices) $(NOGMP_LIBS)

$(static_bindir)/yices_sat$(EXEEXT): $(static_objdir)/yices_sat.o $(static_libyices)
	$(LNK) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) $(BIN_LDFLAGS) $(STATIC) \
	   -o $@ $< $(static_libyices) $(NOGMP_LIBS)

# for all other executables
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
# linux + solaris + FreeBSD
#
# NOTE: by passing flag --no-undefined to ld, we should
# get an error if something is missing in the base_obj
# list.  This flag causes problems on our Solaris 2.10
# machine, unless we also give -lc.
#
$(libdir)/$(libyices_so): $(base_obj) $(version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -o $@ \
	-Wl,-soname,$(libyices_soname) -Wl,--no-undefined \
	$(base_obj) $(version_obj) $(LIBS) -lc
	$(STRIP) -x $@

$(static_libdir)/$(libyices_so): $(base_obj) $(version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -o $@ \
	-Wl,-soname,$(libyices_soname) -Wl,--no-undefined \
	$(base_obj) $(version_obj) $(PIC_GMP) -lc
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
# Change: 2012/07/12 (following e-mail from Dave Vitek, Grammatech):
# build the DLLs in bindir or static_bindir, instead of libdir and
# static_libdir.
#
$(bindir)/$(libyices_dll): $(base_obj) $(version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -o $@ \
	-Wl,--out-implib=$(libdir)/$(libyices_implib) \
	-Wl,--no-undefined \
	$(base_obj) $(version_obj) $(LIBS)
	$(STRIP) $@

$(static_bindir)/$(libyices_dll): $(static_base_obj) $(static_version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -o $@ \
	-Wl,--out-implib=$(static_libdir)/$(libyices_implib) \
	-Wl,--no-undefined \
	$(static_base_obj) $(static_version_obj) $(PIC_GMP)
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
# Change: 2012/07/12 as above: build DLLs in bin directories.
# Change: 2013/07/12: added  -static-libgcc (otherwise the DLLs
# depend on libgcc_s_sjlj-1.dll)
#
$(bindir)/$(libyices_mingw_dll): $(base_obj) $(version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -static-libgcc -o $@ \
	-Wl,--out-implib=$(libdir)/$(libyices_implib) \
	-Wl,--output-def,$(libdir)/$(libyices_def) \
	-Wl,--no-undefined \
	$(base_obj) $(version_obj) $(LIBS)
	$(STRIP) $@

$(static_bindir)/$(libyices_mingw_dll): $(static_base_obj) $(static_version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -static-libgcc -o $@ \
	-Wl,--out-implib=$(static_libdir)/$(libyices_implib) \
	-Wl,--output-def,$(static_libdir)/$(libyices_def) \
	-Wl,--no-undefined \
	$(static_base_obj) $(static_version_obj) $(PIC_GMP)
	$(STRIP) $@


#
# Special dynamic tricks for Mac OS X:
# - the compatibility version is MAJOR.MINOR.0
# - the current version is MAJOR.MINOR.PATCH_LEVEL
# - install name: /usr/local/lib/libyices.MAJOR.dylib
# - option -headerpad_max_install_names allows users to
#   safely change the install name using install_name_tool.
#
$(libdir)/$(libyices_dylib): $(base_obj) $(version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -dynamiclib -o $@ \
	-current_version $(libyices_curr_version) \
	-compatibility_version $(libyices_compat_version) \
	-Wl,-install_name,$(libyices_install_name) \
	-Wl,-headerpad_max_install_names \
	-Wl,-dead_strip \
	$(base_obj) $(version_obj) $(LIBS)
	$(STRIP) -x $@

$(static_libdir)/$(libyices_dylib): $(base_obj) $(version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -dynamiclib -o $@ \
	-current_version $(libyices_curr_version) \
	-compatibility_version $(libyices_compat_version) \
	-Wl,-install_name,$(libyices_install_name) \
	-Wl,-headerpad_max_install_names \
	-Wl,-dead_strip \
	$(base_obj) $(version_obj) $(PIC_GMP)
	$(STRIP) -x $@

# All objects
obj: $(obj) $(bin_obj)

static-obj: $(static_obj) $(static_bin_obj)

# Binaries
bin: $(binaries)

static-bin: $(static_binaries)

# Libraries
lib: $(libyices) $(libyices_dynamic)

static-lib: $(static_libyices) $(static_libyices_dynamic)


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
# distdir. On cygwin/mingw, it makes sense to copy the dll
# into the bin directory.
#
dist: bin lib
	rm -r -f $(distdir)/*
	mkdir $(distdir)/include
	cp yices.h yices_types.h yices_limits.h yices_exit_codes.h $(distdir)/include
	mkdir $(distdir)/bin
	cp $(bindir)/yices_main$(EXEEXT) $(distdir)/bin/yices$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(distdir)/bin/yices$(EXEEXT)
	cp $(bindir)/yices_smtcomp$(EXEEXT) $(distdir)/bin/yices-smt$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(distdir)/bin/yices-smt$(EXEEXT)
	cp $(bindir)/yices_smt2$(EXEEXT) $(distdir)/bin/yices-smt2$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(distdir)/bin/yices-smt$(EXEEXT)
	cp $(bindir)/yices_sat$(EXEEXT) $(distdir)/bin/yices-sat$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(distdir)/bin/yices-sat$(EXEEXT)
	cp $(bindir)/*.dll $(distdir)/bin || true
	mkdir $(distdir)/lib
	cp $(libdir)/* $(distdir)/lib
	rm -f $(distdir)/lib/libyices.a

static-dist: static-bin static-lib
	rm -r -f $(static_distdir)/*
	mkdir $(static_distdir)/include
	cp yices.h yices_types.h yices_limits.h yices_exit_codes.h $(static_distdir)/include
	mkdir $(static_distdir)/bin
	cp $(static_bindir)/yices_main$(EXEEXT) $(static_distdir)/bin/yices$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(static_distdir)/bin/yices$(EXEEXT)
	cp $(static_bindir)/yices_smtcomp$(EXEEXT) $(static_distdir)/bin/yices-smt$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(static_distdir)/bin/yices-smt$(EXEEXT)
	cp $(static_bindir)/yices_smt2$(EXEEXT) $(static_distdir)/bin/yices-smt2$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(static_distdir)/bin/yices-smt2$(EXEEXT)
	cp $(static_bindir)/yices_sat$(EXEEXT) $(static_distdir)/bin/yices-sat$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(static_distdir)/bin/yices-sat$(EXEEXT)
	cp $(static_bindir)/*.dll $(static_distdir)/bin || true
	mkdir $(static_distdir)/lib
	cp $(static_libdir)/* $(static_distdir)/lib
	rm -f $(static_distdir)/lib/libyices.a


smt-dist: bin
	rm -r -f $(smt_distdir)/*
	mkdir $(smt_distdir)/bin
	cp $(bindir)/yices_smtcomp$(EXEEXT) $(smt_distdir)/bin/yices$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(smt_distdir)/bin/yices$(EXEEXT)

static-smt-dist: static-bin
	rm -r -f $(static_smt_distdir)/*
	mkdir $(static_smt_distdir)/bin
	cp $(bindir)/yices_smtcomp$(EXEEXT) $(static_smt_distdir)/bin/yices$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(static_smt_distdir)/bin/yices$(EXEEXT)


.PHONY: dist static-dist


############
#  OTHERS  #
############

#
# Clean: remove the generated source files
#
clean:
	rm -f yices_version.c yices_hash_keywords.h smt_hash_keywords.h smt2_hash_tokens.h \
	smt2_hash_keywords.h smt2_hash_symbols.h

.PHONY: clean


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
	@ echo "  NO_STACK_PROTECTOR = $(NO_STACK_PROTECTOR)"
	@ echo "  STATIC_GMP = $(STATIC_GMP)"
	@ echo "  STATIC_GMP_INCLUDE_DIR = $(STATIC_GMP_INCLUDE_DIR)"
	@ echo "  PIC_GMP = $(PIC_GMP)"
	@ echo "  PIC_GMP_INCLUDE_DIR = $(PIC_GMP_INCLUDE_DIR)"
	@ echo


