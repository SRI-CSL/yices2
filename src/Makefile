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
# For cygiwn and mingw: we use a third subdirectory to build objects for the
# dll that includes libgmp.a
# build/static_dll_obj
#
objdir := $(BUILD)/obj
libdir := $(BUILD)/lib
bindir := $(BUILD)/bin

static_objdir := $(BUILD)/static_obj
static_libdir := $(BUILD)/static_lib
static_bindir := $(BUILD)/static_bin

static_dll_objdir := $(BUILD)/static_dll_obj

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
core_src_c := \
	api/context_config.c \
	api/search_parameters.c \
	api/smt_logic_codes.c \
	api/yices_api.c \
	api/yices_error.c \
	api/yices_error_report.c \
	api/yval.c \
	context/assumption_stack.c \
	context/common_conjuncts.c \
	context/conditional_definitions.c \
	context/context.c \
	context/context_simplifier.c \
	context/context_solver.c \
	context/context_statistics.c \
	context/context_utils.c \
	context/divmod_table.c \
	context/eq_abstraction.c \
	context/eq_learner.c \
	context/internalization_table.c \
	context/ite_flattener.c \
	context/pseudo_subst.c \
	context/shared_terms.c \
	context/symmetry_breaking.c \
	context/quant_context_utils.c \
	context/quant_context.c \
	exists_forall/ef_client.c \
	exists_forall/ef_analyze.c \
	exists_forall/ef_values.c \
	exists_forall/ef_skolemize.c \
	exists_forall/efsolver.c \
	frontend/smt2/attribute_values.c \
	frontend/yices/yices_lexer.c \
	frontend/yices/yices_parser.c \
	io/concrete_value_printer.c \
	io/model_printer.c \
	io/pretty_printer.c \
	io/reader.c \
	io/simple_printf.c \
	io/term_printer.c \
	io/tracer.c \
	io/type_printer.c \
	io/yices_pp.c \
	io/writer.c \
	model/abstract_values.c \
	model/arith_projection.c \
	model/concrete_values.c \
	model/fresh_value_maker.c \
	model/fun_maps.c \
	model/fun_trees.c \
	model/generalization.c \
	model/literal_collector.c \
	model/map_to_model.c \
	model/model_eval.c \
	model/model_queries.c \
	model/model_support.c \
	model/models.c \
	model/presburger.c \
	model/projection.c \
	model/term_to_val.c \
	model/val_to_term.c \
	mt/yices_locks.c \
	parser_utils/lexer.c \
	parser_utils/parser.c \
	parser_utils/term_stack2.c \
	parser_utils/term_stack_error.c \
	solvers/bv/bit_blaster.c \
	solvers/bv/bv64_intervals.c \
	solvers/bv/bv_atomtable.c \
	solvers/bv/bvconst_hmap.c \
	solvers/bv/bvexp_table.c \
	solvers/bv/bv_intervals.c \
	solvers/bv/bvpoly_compiler.c \
	solvers/bv/bvpoly_dag.c \
	solvers/bv/bvsolver.c \
	solvers/bv/bv_vartable.c \
	solvers/bv/dimacs_printer.c \
	solvers/bv/merge_table.c \
	solvers/bv/remap_table.c \
	solvers/cdcl/delegate.c \
	solvers/cdcl/gates_hash_table.c \
	solvers/cdcl/gates_manager.c \
	solvers/cdcl/new_gates.c \
	solvers/cdcl/new_gate_hash_map.c \
	solvers/cdcl/new_gate_hash_map2.c \
	solvers/cdcl/new_sat_solver.c \
	solvers/cdcl/smt_core.c \
	solvers/cdcl/truth_tables.c \
	solvers/cdcl/wide_truth_tables.c \
	solvers/egraph/composites.c \
	solvers/egraph/diseq_stacks.c \
	solvers/egraph/egraph_assertion_queues.c \
	solvers/egraph/egraph.c \
	solvers/egraph/egraph_explanations.c \
	solvers/egraph/egraph_utils.c \
	solvers/egraph/theory_explanations.c \
	solvers/floyd_warshall/dl_vartable.c \
	solvers/floyd_warshall/idl_floyd_warshall.c \
	solvers/floyd_warshall/rdl_floyd_warshall.c \
	solvers/funs/fun_level.c \
	solvers/funs/fun_solver.c \
	solvers/funs/stratification.c \
	solvers/simplex/arith_atomtable.c \
	solvers/simplex/arith_vartable.c \
	solvers/simplex/diophantine_systems.c \
	solvers/simplex/gomory_cuts.c \
	solvers/simplex/integrality_constraints.c \
	solvers/simplex/matrices.c \
	solvers/simplex/offset_equalities.c \
	solvers/simplex/simplex.c \
	solvers/quant/quant_parameters.c \
	solvers/quant/ef_parameters.c \
	solvers/quant/ef_problem.c \
	solvers/quant/quant_pattern.c \
	solvers/quant/quant_cnstr.c \
	solvers/quant/cnstr_learner.c \
	solvers/quant/term_learner.c \
	solvers/quant/ematch_instr.c \
	solvers/quant/ematch_instr_stack.c \
	solvers/quant/ematch_instance.c \
	solvers/quant/ematch_compile.c \
	solvers/quant/ematch_execute.c \
	solvers/quant/quant_ematching.c \
	solvers/quant/quant_solver.c \
	terms/balanced_arith_buffers.c \
	terms/bit_expr.c \
	terms/bit_term_conversion.c \
	terms/bv64_interval_abstraction.c \
	terms/bv64_constants.c \
	terms/bv64_polynomials.c \
	terms/bvarith64_buffers.c \
	terms/bvarith64_buffer_terms.c \
	terms/bvarith_buffers.c \
	terms/bvarith_buffer_terms.c \
	terms/bv_constants.c \
	terms/bvfactor_buffers.c \
	terms/bvlogic_buffers.c \
	terms/bvpoly_buffers.c \
	terms/bv_polynomials.c \
	terms/bv_slices.c \
	terms/conditionals.c \
	terms/elim_subst.c \
	terms/extended_rationals.c \
	terms/free_var_collector.c \
	terms/full_subst.c \
	terms/int_rational_hash_maps.c \
	terms/ite_stack.c \
	terms/mpq_aux.c \
	terms/mpq_stores.c \
	terms/poly_buffer.c \
	terms/poly_buffer_terms.c \
	terms/polynomials.c \
	terms/power_products.c \
	terms/pprod_table.c \
	terms/rational_hash_maps.c \
	terms/rationals.c \
	terms/rba_buffer_terms.c \
	terms/renaming_context.c \
	terms/subst_cache.c \
	terms/subst_context.c \
	terms/term_explorer.c \
	terms/term_manager.c \
	terms/terms.c \
	terms/term_sets.c \
	terms/term_substitution.c \
	terms/term_utils.c \
	terms/types.c \
	terms/variable_renaming.c \
	utils/arena.c \
	utils/backtrack_arrays.c \
	utils/backtrack_int_hash_map.c \
	utils/cache.c \
	utils/csets.c \
	utils/cputime.c \
	utils/dep_tables.c \
	utils/error.c \
	utils/gcd.c \
	utils/generic_heap.c \
	utils/hash_functions.c \
	utils/index_vectors.c \
	utils/indexed_table.c \
	utils/int_array_hsets.c \
	utils/int_array_sort2.c \
	utils/int_array_sort.c \
	utils/int_bags.c \
	utils/int_bv_sets.c \
	utils/int_harray_store.c \
	utils/int_hash_classes.c \
	utils/int_hash_map2.c \
	utils/int_hash_map.c \
	utils/int_hash_sets.c \
	utils/int_hash_tables.c \
	utils/int_heap2.c \
	utils/int_heap.c \
	utils/int_partitions.c \
	utils/int_powers.c \
	utils/int_queues.c \
	utils/int_stack.c \
	utils/int_vectors.c \
	utils/mark_vectors.c \
	utils/memalloc.c \
	utils/object_stack.c \
	utils/object_stores.c \
	utils/pair_hash_map.c \
	utils/pair_hash_map2.c \
	utils/pointer_vectors.c \
	utils/ptr_array_sort2.c \
	utils/ptr_array_sort.c \
	utils/ptr_hash_classes.c \
	utils/ptr_hash_map.c \
	utils/ptr_heap.c \
	utils/ptr_partitions.c \
	utils/ptr_queues.c \
	utils/ptr_sets.c \
	utils/ptr_sets2.c \
	utils/ptr_stack.c \
	utils/ptr_vectors.c \
	utils/refcount_int_arrays.c \
	utils/refcount_strings.c \
	utils/resize_arrays.c \
	utils/simple_cache.c \
	utils/simple_int_stack.c \
	utils/sparse_arrays.c \
	utils/stable_sort.c \
	utils/string_buffers.c \
	utils/string_utils.c \
	utils/symbol_tables.c \
	utils/tag_map.c \
	utils/tuple_hash_map.c \
	utils/uint_array_sort.c \
	utils/uint_array_sort2.c \
	utils/uint_rbtrees.c \
	utils/use_vectors.c \
	utils/vector_hash_map.c \
	utils/uint_learner.c

#
# Optional: mcsat solver
#
mcsat_src_c := \
	mcsat/tracing.c \
	mcsat/solver.c \
	mcsat/variable_db.c \
	mcsat/variable_queue.c \
	mcsat/value.c \
	mcsat/model.c \
	mcsat/trail.c \
	mcsat/conflict.c \
	mcsat/unit_info.c \
	mcsat/gc.c \
	mcsat/eq/equality_graph.c \
	mcsat/eq/merge_queue.c \
	mcsat/weq/weak_eq_graph.c \
	mcsat/utils/int_mset.c \
	mcsat/utils/int_lset.c \
	mcsat/utils/lp_data.c \
	mcsat/utils/lp_utils.c \
	mcsat/utils/lp_constraint_db.c \
	mcsat/utils/value_hash_map.c \
	mcsat/utils/value_vector.c \
	mcsat/utils/scope_holder.c \
	mcsat/utils/statistics.c \
	mcsat/utils/substitution.c \
	mcsat/uf/uf_plugin.c \
	mcsat/bool/clause_db.c \
	mcsat/bool/cnf.c \
	mcsat/bool/bcp_watch_manager.c \
	mcsat/bool/bool_plugin.c \
	mcsat/nra/nra_plugin.c \
	mcsat/nra/nra_plugin_internal.c \
	mcsat/nra/nra_plugin_explain.c \
	mcsat/nra/nra_libpoly.c \
	mcsat/nra/feasible_set_db.c \
	mcsat/ff/ff_plugin.c \
	mcsat/ff/ff_plugin_internal.c \
	mcsat/ff/ff_plugin_explain.c \
	mcsat/ff/ff_libpoly.c \
	mcsat/ff/ff_feasible_set_db.c \
	mcsat/ite/ite_plugin.c \
	mcsat/bv/bv_plugin.c \
	mcsat/bv/bv_bdd_manager.c \
	mcsat/bv/bv_evaluator.c \
	mcsat/bv/bv_explainer.c \
	mcsat/bv/bv_feasible_set_db.c \
	mcsat/bv/bdd_computation.c \
	mcsat/bv/explain/arith_utils.c \
	mcsat/bv/explain/arith_norm.c \
	mcsat/bv/explain/arith_intervals.c \
	mcsat/bv/explain/arith.c \
	mcsat/bv/explain/eq_ext_con.c \
	mcsat/bv/explain/full_bv_sat.c \
	mcsat/bv/explain/full_bv_trivial.c \
	mcsat/watch_list_manager.c \
	mcsat/preprocessor.c \
	mcsat/options.c



#
# Fake mcsat module: do nothing. Used to make the compilation go through.
#
no_mcsat_src_c := \
	mcsat/no_mcsat.c \
	mcsat/options.c


#
# Other source files for libyices.a
# That's all the code needed by the main binaries
# + experimental/unfinished modules
# + functions for printing/debugging
# + old stuff not needed anymore (except for tests)
#
extra_src_c := \
	context/context_parameters.c \
	context/context_printer.c \
	context/dump_context.c \
	context/internalization_printer.c \
	frontend/common/assumptions_and_core.c \
	frontend/common/assumption_table.c \
	frontend/common/bug_report.c \
	frontend/common/named_term_stacks.c \
	frontend/common/parameters.c \
	frontend/common/tables.c \
	frontend/smt1/smt_lexer.c \
	frontend/smt1/smt_parser.c \
	frontend/smt1/smt_term_stack.c \
	frontend/smt2/parenthesized_expr.c \
	frontend/smt2/smt2_commands.c \
	frontend/smt2/smt2_expressions.c \
	frontend/smt2/smt2_lexer.c \
	frontend/smt2/smt2_model_printer.c \
	frontend/smt2/smt2_parser.c \
	frontend/smt2/smt2_printer.c \
	frontend/smt2/smt2_symbol_printer.c \
	frontend/smt2/smt2_term_stack.c \
	frontend/smt2/smt2_type_printer.c \
	frontend/yices/arith_solver_codes.c \
	frontend/yices/labeled_assertions.c \
	frontend/yices/yices_help.c \
	frontend/yices/yices_reval.c \
	model/large_bvsets.c \
	model/rb_bvsets.c \
	model/small_bvsets.c \
	solvers/bv/bvsolver_printer.c \
	solvers/cdcl/clause_pool.c \
	solvers/cdcl/gates_printer.c \
	solvers/cdcl/sat_solver.c \
	solvers/cdcl/smt_core_printer.c \
	solvers/egraph/egraph_printer.c \
	solvers/floyd_warshall/idl_fw_printer.c \
	solvers/floyd_warshall/rdl_fw_printer.c \
	solvers/funs/fun_solver_printer.c \
	solvers/simplex/dsolver_printer.c \
	solvers/simplex/int_constraint_printer.c \
	solvers/simplex/simplex_printer.c \
	solvers/simplex/simplex_prop_table.c \
	terms/arith_buffers.c \
	utils/command_line.c \
	utils/memsize.c \
	utils/pair_hash_sets.c \
	utils/string_hash_map.c \
	utils/timeout.c \
	utils/union_find.c


#
# Optional for libyices.a: support for launching threads
# and testing multi-threaded code
#
extra_thread_src_c := \
	mt/threads.c


#
# base: core + mcsat if MCSAT is enabled or core + fake mcsat
#
ifeq ($(ENABLE_MCSAT),yes)
base_src_c := $(core_src_c) $(mcsat_src_c)
else
base_src_c := $(core_src_c) $(no_mcsat_src_c)
endif

#
# all sources: base + extra
#
src_c := $(base_src_c) $(extra_src_c)
ifeq ($(THREAD_SAFE),1)
src_c := $(src_c) $(extra_thread_src_c)
endif

#
# additional source files for the binaries
#
bin_src_c := \
	frontend/yices.c \
	frontend/yices_sat.c \
	frontend/yices_sat_new.c \
	frontend/yices_smt.c \
	frontend/yices_smt2.c \
	frontend/yices_smtcomp.c \

#
# Auto-generated version file
#
version_c := api/yices_$(YICES_MODE)_version.c

#
# All auto-generated files
#
auto_generated := \
	$(version_c) \
	frontend/yices/yices_hash_keywords.h \
	frontend/smt1/smt_hash_keywords.h \
	frontend/smt2/smt2_hash_tokens.h \
	frontend/smt2/smt2_hash_keywords.h \
	frontend/smt2/smt2_hash_symbols.h

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

version_obj := $(objdir)/api/yices_version.o
version_dep := $(version_c:%.c=$(objdir)/%.d)
static_version_obj := $(static_objdir)/api/yices_version.o
static_version_dep := $(version_c:%.c=$(static_objdir)/%.d)

# extras for mingw and cygwin
static_dll_obj := $(src_c:%.c=$(static_dll_objdir)/%.o)
static_dll_dep := $(src_c:%.c=$(static_dll_objdir)/%.d)
static_dll_version_obj := $(static_dll_objdir)/api/yices_version.o
static_dll_version_dep := $(version_c:%.c=$(static_dll_objdir)/%.d)


#
# Static libraries
#
libyices := $(libdir)/libyices.a
static_libyices := $(static_libdir)/libyices.a


#
# Binaries
#
# binaries := $(bin_src_c:%.c=$(bindir)/%$(EXEEXT))
# static_binaries := $(bin_src_c:%.c=$(static_bindir)/%$(EXEEXT))
binaries := $(addprefix $(bindir)/,$(notdir $(bin_src_c:%.c=%$(EXEEXT))))
static_binaries := $(addprefix $(static_bindir)/,$(notdir $(bin_src_c:%.c=%$(EXEEXT))))


#
# DYNAMIC LIBRARIES
#

#
# Linux/Solaris/FreeBSD
# the library has full versioned name libyices.so.2.X.Y
# soname: libyices.so.2.X
#
# For Free BSD: the convention seems to be libyices.so.2.X
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
# 2014/10/22: changed install name to use the $(prefix)
# set by configure.
#
# TODO?: we should use $(libdir) instead of $(prefix)/lib but
# this clashes with the $(libdir) set at the beginning of this
# Makefile.
#
libyices_dylib := libyices.$(MAJOR).dylib
libyices_curr_version := $(MAJOR).$(MINOR).$(PATCH_LEVEL)
libyices_compat_version := $(MAJOR).$(MINOR).0
libyices_install_name := $(prefix)/lib/libyices.$(MAJOR).dylib

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
# Whether we are building for a big endian architecture
#
ifeq ($(WORDS_BIGENDIAN),yes)
  CPPFLAGS += -DWORDS_BIGENDIAN
endif

#
# Whether we have support for mcsat
#
ifeq ($(ENABLE_MCSAT),yes)
  CPPFLAGS += -DHAVE_MCSAT
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
  CPPFLAGS := $(CPPFLAGS) -DMINGW -D__USE_MINGW_ANSI_STDIO
  PIC=
  STATIC=-static -static-libgcc
  BIN_LDFLAGS= -Wl,--stack,8388608
  libyices_dynamic=$(bindir)/$(libyices_mingw_dll)
  static_libyices_dynamic=$(static_bindir)/$(libyices_mingw_dll)
else
ifeq ($(POSIXOS),darwin)
  CPPFLAGS := $(CPPFLAGS) -DMACOSX
  CFLAGS += -fvisibility=hidden $(PTHREAD)
  PIC=-fPIC
  STATIC=
  BIN_LDFLAGS=
  libyices_dynamic=$(libdir)/$(libyices_dylib)
  static_libyices_dynamic=$(static_libdir)/$(libyices_dylib)

  #
  # To stop a clang warning when we compile with -pthread,
  # we add option -Qunused-arguments
  #
  # Detect clang-disguised-as-gcc vs. GNU GCC
  #
  ifeq ($(THREAD_SAFE),1)
    ifeq ($(shell $(CC) -v 2>&1 | grep -c "clang version"), 1)
       CFLAGS += -Qunused-arguments
    endif
  endif
else
ifeq ($(POSIXOS),sunos)
  PIC=-fPIC
  STATIC=
  CPPFLAGS := $(CPPFLAGS) -DSOLARIS
  CFLAGS += -fvisibility=hidden $(PTHREAD)
  BIN_LDFLAGS=
  libyices_dynamic=$(libdir)/$(libyices_so)
  static_libyices_dynamic=$(static_libdir)/$(libyices_so)
else
ifeq ($(POSIXOS),linux)
  PIC=-fPIC
  STATIC=-static
  CPPFLAGS := $(CPPFLAGS) -DLINUX -U_FORTIFY_SOURCE
  CFLAGS += -fvisibility=hidden $(PTHREAD)
  BIN_LDFLAGS= $(PTHREAD)
  libyices_dynamic=$(libdir)/$(libyices_so)
  static_libyices_dynamic=$(static_libdir)/$(libyices_so)
else
ifeq ($(POSIXOS),freebsd)
  PIC=-fPIC
  STATIC=-static
  CPPFLAGS := $(CPPFLAGS) -DFREEBSD
  CFLAGS += -fvisibility=hidden $(PTHREAD)
  BIN_LDFLAGS=
  libyices_dynamic=$(libdir)/$(libyices_so)
  static_libyices_dynamic=$(static_libdir)/$(libyices_so)
else
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
# include dirs: we want -I. first
#
CPPFLAGS := -I. -Iinclude $(CPPFLAGS)

#
# Warning levels: dropped the flag -Winiline in all build modes.
# Can't keep up with gcc/clang.
#
CFLAGS += -Wall -Wredundant-decls

#
# Format string issues on Windows/mingw
#
ifeq ($(POSIXOS),mingw)
  CFLAGS += -Wno-format
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
# Related issue reported by Richard Corden (January 18, 2016)
# Ubuntu sets -D_FORTIFY_SOURCE=2 by default (to detect buffer overflows
# and other security issues). This causes link-time issues again:
#   undefined reference to __longjmp_chk.
# The fix is to add -U_FORTIFY_SOURCE when we compile on linux
#
# To link with google gperftools:
#  on Linux we add the flag -Wl,--no-as-needed otherwise the profiler
#  library may not be linked with the binaries. (Because some
#  Linux distributions set -Wl,--as-needed by default).
#
#
ifeq ($(YICES_MODE),release)
CFLAGS := $(CFLAGS) -O3 -fomit-frame-pointer $(NO_STACK_PROTECTOR)
CPPFLAGS := $(CPPFLAGS) -DNDEBUG
else
ifeq ($(YICES_MODE),devel)
CFLAGS := $(CFLAGS) -O3 -g -fomit-frame-pointer $(NO_STACK_PROTECTOR)
CPPFLAGS := $(CPPFLAGS)
else
ifeq ($(YICES_MODE),profile)
CFLAGS := $(CFLAGS) -O3 -pg
CPPFLAGS := $(CPPFLAGS) -DNDEBUG
else
ifeq ($(YICES_MODE),gcov)
CFLAGS := $(CFLAGS) -fprofile-arcs -ftest-coverage -g -O0
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
# Object files to include in the dynamic libraries
#
ifeq ($(YICES_MODE),release)
base_obj := $(base_src_c:%.c=$(objdir)/%.o)
static_base_obj := $(base_src_c:%.c=$(static_objdir)/%.o)
static_dll_base_obj := $(base_src_c:%.c=$(static_dll_objdir)/%.o)
else
base_obj := $(obj)
static_base_obj := $(static_obj)
static_dll_base_obj := $(static_dll_obj)
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
  STATIC_CPP_GMP := -I$(STATIC_GMP_INCLUDE_DIR)
endif

ifneq ($(STATIC_LIBPOLY_INCLUDE_DIR),)
  STATIC_CPP_LIBPOLY := -I$(STATIC_LIBPOLY_INCLUDE_DIR)
endif

STATIC_CPPFLAGS := $(STATIC_CPP_GMP) $(STATIC_CPP_LIBPOLY) $(CPPFLAGS)

#
# For building dll linked statically with libgmp.a
# we use the STATIC_CPPFLAGS (so that we use the right version of gmp.h)
# For building the binaries linked statically with libgmp.a,
# we also add the NOYICES_DLL flag.
#
ifeq ($(POSIXOS),cygwin)
  STATIC_DLL_CPPFLAGS := $(STATIC_CPP_GMP) $(STATIC_CPP_LIBPOLY) $(CPPFLAGS)
  STATIC_CPPFLAGS += -DNOYICES_DLL
else
ifeq ($(POSIXOS),mingw)
  STATIC_DLL_CPPFLAGS := $(STATIC_CPP_GMP) $(STATIC_CPP_LIBPOLY) $(CPPFLAGS)
  STATIC_CPPFLAGS += -DNOYICES_DLL
endif
endif


#
# LIBS for compiling in static mode
#
# We need to remove -lgmp and -lpoly from LIBS in static mode, otherwise adding
# $(STATIC_GMP) does not work on Darwin and cygwin
# We also use $(NOGMP_LIBS) to build yices_sat.
#
# Important: make sure the GMP library is last (if some
# archives/libraries in NOGMP_LIBS depend on GMP).
#
NOGMP_LIBS := $(subst -lpoly,,$(subst -lgmp,,$(LIBS)))
STATIC_LIBS := $(NOGMP_LIBS) $(STATIC_LIBPOLY) $(STATIC_GMP)
PIC_LIBS := $(NOGMP_LIBS) $(PIC_LIBPOLY) $(PIC_GMP)



#################
#  BUILD RULES  #
#################

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

$(static_dll_objdir)/%.d: %.c
	@set -e; echo Building dependency file $@ ; \
	$(CC) -MM -MG -MT $*.o $(CFLAGS) $(STATIC_DLL_CPPFLAGS) $< > $@.$$$$ ; \
	$(SED) 's,\($*\).o[ :]*,$(static_dll_objdir)/\1.o $@ : , g' < $@.$$$$ > $@ ; \
	rm -f $@.$$$$

ifneq ($(MAKECMDGOALS),clean)

static_goals := $(filter static-%,$(MAKECMDGOALS))
dyn_goals := $(filter-out static-%,$(MAKECMDGOALS))

ifneq ($(dyn_goals),)
 include $(dep)
 include $(bin_dep)
 include $(version_dep)
endif

ifneq ($(static_goals),)
 include $(static_dep)
 include $(static_bin_dep)
 include $(static_version_dep)
 ifeq ($(POSIXOS),mingw)
   include $(static_dll_dep)
   include $(static_dll_version_dep)
 else
 ifeq ($(POSIXOS),cygwin)
   include $(static_dll_dep)
   include $(static_dll_version_dep)
 endif
 endif
endif

endif

#
# Gperf generated tables
# - we need to give different names to the yices and smt lookup functions
#
frontend/yices/yices_hash_keywords.h: frontend/yices/yices_keywords.txt
	$(GPERF) -C -L ANSI-C -W yices_kw --output-file=frontend/yices/yices_hash_keywords.h \
	--lookup-function-name=in_yices_kw frontend/yices/yices_keywords.txt

frontend/smt1/smt_hash_keywords.h: frontend/smt1/smt_keywords.txt
	$(GPERF) -C -L ANSI-C -W smt_kw --output-file=frontend/smt1/smt_hash_keywords.h \
	--lookup-function-name=in_smt_kw frontend/smt1/smt_keywords.txt

#
# Tables for SMT2:
# - we want to include three hash functions in the same file (smt2_lexer.c)
# - for this to work,
#   we need to give different names to the hash function (option -H ...)
#   we can't use -G and we must give -E
#
frontend/smt2/smt2_hash_tokens.h: frontend/smt2/smt2_tokens.txt
	$(GPERF) -C -L ANSI-C -W smt2_tk -H hash_tk -E --output-file=frontend/smt2/smt2_hash_tokens.h \
	--lookup-function-name=in_smt2_tk frontend/smt2/smt2_tokens.txt

frontend/smt2/smt2_hash_keywords.h: frontend/smt2/smt2_keywords.txt
	$(GPERF) -C -L ANSI-C -W smt2_kw -H hash_kw -E --output-file=frontend/smt2/smt2_hash_keywords.h \
	--lookup-function-name=in_smt2_kw frontend/smt2/smt2_keywords.txt

frontend/smt2/smt2_hash_symbols.h: frontend/smt2/smt2_symbols.txt
	$(GPERF) -C -L ANSI-C -W smt2_sym -H hash_sym -E --output-file=frontend/smt2/smt2_hash_symbols.h \
	--lookup-function-name=in_smt2_sym frontend/smt2/smt2_symbols.txt

#
# Object files
#
$(version_obj): $(version_c)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(PIC) -c $(version_c) -o $(version_obj)

$(objdir)/%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) $(PIC) -c $< -o $@

$(static_version_obj): $(version_c)
	$(CC) -DYICES_STATIC $(STATIC_CPPFLAGS) $(CFLAGS) -c $(version_c) -o $(static_version_obj)

$(static_dll_version_obj): $(version_c)
	$(CC) -DYICES_STATIC $(STATIC_DLL_CPPFLAGS) $(CFLAGS) -c $(version_c) -o $(static_dll_version_obj)

$(static_objdir)/%.o: %.c
	$(CC) $(STATIC_CPPFLAGS) $(CFLAGS) -c $< -o $@

$(static_dll_objdir)/%.o: %.c
	$(CC) $(STATIC_DLL_CPPFLAGS) $(CFLAGS) -c $< -o $@

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
$(bindir)/yices_sat$(EXEEXT): $(objdir)/frontend/yices_sat.o $(libyices)
	$(LNK) $(CFLAGS) $(LDFLAGS) $(BIN_LDFLAGS) \
	   -o $@ $< $(libyices) $(NOGMP_LIBS)

$(static_bindir)/yices_sat$(EXEEXT): $(static_objdir)/frontend/yices_sat.o $(static_libyices)
	$(LNK) $(CFLAGS) $(LDFLAGS) $(BIN_LDFLAGS) $(STATIC) \
	   -o $@ $< $(static_libyices) $(NOGMP_LIBS)

$(bindir)/yices_sat_new$(EXEEXT): $(objdir)/frontend/yices_sat_new.o $(libyices)
	$(LNK) $(CFLAGS) $(LDFLAGS) $(BIN_LDFLAGS) \
	   -o $@ $< $(libyices) $(NOGMP_LIBS)

$(static_bindir)/yices_sat_new$(EXEEXT): $(static_objdir)/frontend/yices_sat_new.o $(static_libyices)
	$(LNK) $(CFLAGS) $(LDFLAGS) $(BIN_LDFLAGS) $(STATIC) \
	   -o $@ $< $(static_libyices) $(NOGMP_LIBS)


# for all other executables
$(bindir)/%$(EXEEXT): $(objdir)/frontend/%.o $(libyices)
	$(LNK) $(CFLAGS) $(LDFLAGS) $(BIN_LDFLAGS) \
	   -o $@ $< $(libyices) $(LIBS)

$(static_bindir)/%$(EXEEXT): $(static_objdir)/frontend/%.o $(static_libyices)
	$(LNK) $(CFLAGS) $(LDFLAGS) $(BIN_LDFLAGS) $(STATIC) \
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
ifeq ($(YICES_MODE),release)
	$(STRIP) -x $@
endif

$(static_libdir)/$(libyices_so): $(base_obj) $(version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -o $@ \
	-Wl,-soname,$(libyices_soname) -Wl,--no-undefined \
	$(base_obj) $(version_obj) $(PIC_LIBS) -lc
ifeq ($(YICES_MODE),release)
	$(STRIP) -x $@
endif

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
ifeq ($(YICES_MODE),release)
	$(STRIP) $@
endif

$(static_bindir)/$(libyices_dll): $(static_dll_base_obj) $(static_dll_version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -o $@ \
	-Wl,--out-implib=$(static_libdir)/$(libyices_implib) \
	-Wl,--no-undefined \
	$(static_dll_base_obj) $(static_dll_version_obj) $(PIC_LIBS)
ifeq ($(YICES_MODE),release)
	$(STRIP) -x $@
endif


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
ifeq ($(YICES_MODE),release)
	$(STRIP) $@
endif

$(static_bindir)/$(libyices_mingw_dll): $(static_dll_base_obj) $(static_dll_version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -shared -static-libgcc -o $@ \
	-Wl,--out-implib=$(static_libdir)/$(libyices_implib) \
	-Wl,--output-def,$(static_libdir)/$(libyices_def) \
	-Wl,--no-undefined \
	$(static_dll_base_obj) $(static_dll_version_obj) $(PIC_LIBS)
ifeq ($(YICES_MODE),release)
	$(STRIP) -x $@
endif


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
ifeq ($(YICES_MODE),release)
	$(STRIP) -x $@
endif

$(static_libdir)/$(libyices_dylib): $(static_base_obj) $(static_version_obj)
	$(CC) $(CFLAGS) $(LDFLAGS) -dynamiclib -o $@ \
	-current_version $(libyices_curr_version) \
	-compatibility_version $(libyices_compat_version) \
	-Wl,-install_name,$(libyices_install_name) \
	-Wl,-headerpad_max_install_names \
	-Wl,-dead_strip \
	$(static_base_obj) $(static_version_obj) $(PIC_LIBS)
ifeq ($(YICES_MODE),release)
	$(STRIP) -x $@
endif

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
	cp include/*.h $(distdir)/include
	mkdir $(distdir)/bin
	cp $(bindir)/yices$(EXEEXT) $(distdir)/bin/yices$(EXEEXT)
	cp $(bindir)/yices_smtcomp$(EXEEXT) $(distdir)/bin/yices-smt$(EXEEXT)
	cp $(bindir)/yices_smt2$(EXEEXT) $(distdir)/bin/yices-smt2$(EXEEXT)
	cp $(bindir)/yices_sat$(EXEEXT) $(distdir)/bin/yices-sat$(EXEEXT)
	cp $(bindir)/*.dll $(distdir)/bin || true
	mkdir $(distdir)/lib
	cp $(libdir)/* $(distdir)/lib
ifneq ($(YICES_MODE),debug)
	$(STRIP) $(STRIPFLAGS) $(distdir)/bin/yices$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(distdir)/bin/yices-smt$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(distdir)/bin/yices-smt2$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(distdir)/bin/yices-sat$(EXEEXT)
endif

static-dist: static-bin static-lib
	rm -r -f $(static_distdir)/*
	mkdir $(static_distdir)/include
	cp include/*.h $(static_distdir)/include
	mkdir $(static_distdir)/bin
	cp $(static_bindir)/yices$(EXEEXT) $(static_distdir)/bin/yices$(EXEEXT)
	cp $(static_bindir)/yices_smtcomp$(EXEEXT) $(static_distdir)/bin/yices-smt$(EXEEXT)
	cp $(static_bindir)/yices_smt2$(EXEEXT) $(static_distdir)/bin/yices-smt2$(EXEEXT)
	cp $(static_bindir)/yices_sat$(EXEEXT) $(static_distdir)/bin/yices-sat$(EXEEXT)
	cp $(static_bindir)/*.dll $(static_distdir)/bin || true
	mkdir $(static_distdir)/lib
	cp $(static_libdir)/* $(static_distdir)/lib
ifneq ($(YICES_MODE),debug)
	$(STRIP) $(STRIPFLAGS) $(static_distdir)/bin/yices$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(static_distdir)/bin/yices-smt$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(static_distdir)/bin/yices-smt2$(EXEEXT)
	$(STRIP) $(STRIPFLAGS) $(static_distdir)/bin/yices-sat$(EXEEXT)
endif


.PHONY: dist static-dist


############
#  OTHERS  #
############

#
# Clean: remove the generated source files
#
clean:
	rm -f $(auto_generated)

.PHONY: clean


ifeq ($(MAKE_RESTARTS),)
#
# Rules to keep going if .h or .c files have been deleted.  This
# allows Make to rebuild an out-of-date dependency file 'source.d'
# that refers to an 'oldstuff.h' that has been deleted.  We want to
# fail on the next restart if 'oldstuff.h' is still referenced in some
# existing 'source.c'.
#
%.h:
	@ echo "*** Warning: header file $@ is missing ***"

%.c:
	@ echo "*** Warning: source file $@ is missing ***"

endif


#
# For debugging of Makefile and configuration:
# print the options as set by this Makefile
#
show-details:
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
	@ echo "  ENABLE_MCSAT = $(ENABLE_MCSAT)"
	@ echo "  STATIC_LIBPOLY = $(STATIC_LIBPOLY)"
	@ echo "  STATIC_LIBPOLY_INCLUDE_DIR = $(STATIC_LIBPOLY_INCLUDE_DIR)"
	@ echo "  PIC_LIBPOLY = $(PIC_LIBPOLY)"
	@ echo "  PIC_LIBPOLY_INCLUDE_DIR = $(PIC_LIBPOLY_INCLUDE_DIR)"
