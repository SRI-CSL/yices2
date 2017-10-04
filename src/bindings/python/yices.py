"""
The Yices2 Python API.

Basically implements all the external symbols of Yices2 - see yices.h


iam: 9/26/2017   I decided that it was better to preserve the names
between the API and the python bindings, than any other consideration.

This will be annoying if one uses this idiom:

import yices

but not if one uses this idiom:

from yices import *

there is also the middle ground of

import yices as y

iam: What about constants like NULL_TERM?

iam: need to isolate and load the gmp stuff into a separate language binding.

bd: take care of pointer() vs. byref(). Be consistent about it.
    update the docstrings: some functions return bitvector values
    in an array of integers.

iam: we should beef up the Yices exception so that it contains a copy of the
error report.

iam: we should hide all ctype crap from the user. Any array passed in to a
python routine should be a python array. We can use the make_* routines
locally. we should also return values, not place them in "references" or "arrays"
since we do not have to return an error code like the C API.

"""
from __future__ import with_statement

import os
import sys

from functools import wraps

from ctypes import (
    Array,
    byref,
    CDLL,
    cast,
    c_char_p,
    c_double,
    c_int,
    c_uint,
    c_int32,
    c_uint32,
    c_int64,
    c_uint64,
    c_ulong,
    c_size_t,
    c_void_p,
    pointer,
    POINTER,
    Structure
    )

from ctypes.util import find_library


def yices_python_info_main():
    """The only console entry point; currently just used for information."""
    loadYices()
    sys.stdout.write('Python Yices Bindings. Version {0}\n'.format(yices_python_version));
    sys.stdout.write('Yices library loaded from {0}\n'.format(libyicespath))
    sys.stdout.write('Version: {0}\nArchitecture: {1}\nBuild mode: {2}\nBuild date: {3}\nMCSat support: {4}\n'.format(yices_version, yices_build_arch, yices_build_mode, yices_build_date, yices_has_mcsat()));





################################################################################################
# Feeping Creaturism:                                                                          #
#                                                                                              #
# this is the all important version number used by pip.                                        #
#                                                                                              #
#                                                                                              #
################################################################################################
#                                                                                              #
# Version History:                                                                             #
#                                                                                              #
# pip      -  lib      -  release date   -  notes                                              #
#                                                                                              #
# 1.0.0    -  2.5.3    -  9/11/2017      -  birth                                              #
# 1.0.1    -  2.5.3    -  9/27/2017      -  uniform API version                                #
# 1.0.2    -  2.5.3    -  9/27/2017      -  library version check                              #
# 1.0.3    -  2.5.3    -  9/28/2017      -  STATUS_SAT et al + Linux install fix.              #
# 1.0.4    -  2.5.3    -  9/28/2017      -  LD_LIBRARY_PATH hackery.                           #
# 1.0.5    -  2.5.3    -  9/28/2017      -  LD_LIBRARY_PATH hackery, II.                       #
# 1.0.6    -  2.5.3    -  9/28/2017      -  LD_LIBRARY_PATH hackery, III.                      #
# 1.0.7    -  2.5.4    -  9/29/2017      -  patch level version bump for PPA goodness          #
# 1.0.8    -  2.5.4    -  10/4/2017      -  improving the user experience  (less SIGSEGVs)     #
#                                                                                              #
################################################################################################

#
# when the dust settles we can synch this with the library, but
# while the bindings are moving so fast we should keep them separate.
#
#
yices_python_version = '1.0.8'

#
# 1.0.1 needs yices_has_mcsat
# 1.0.1-7 needs the _fd api additions that appear in 2.5.4
#
yices_recommended_version = '2.5.4'

#iam: 10/4/2017 try to make the user experience a little more pythony.
#BD suggests doing this in the loadYices routine; he might be right
#but this is more nannyish because the dolt could still call yices_exit
#then go on to try and do stuff.
__yices_library_inited__ = False

class YicesException(Exception):
    """Base class for exceptions from Yices."""
    pass

def catch_error(errval):
    """catches any error."""
    def decorator(yices_fun):
        """yices api function decorator."""
        @wraps(yices_fun)
        def wrapper(*args, **kwargs):
            """yices api function wrapper."""
            errstr = "You must initialize by calling yices_init()"
            result = yices_fun(*args, **kwargs) if __yices_library_inited__ else None
            if not  __yices_library_inited__ :
                raise YicesException(errstr)
            if result == errval and yices_error_code() != 0L:
                errstr = yices_error_string()
                yices_clear_error()
                raise YicesException(errstr)
            return result
        return wrapper
    return decorator

def catch_uninitialized():
    """catches a call to an uninitialized yices library (catch_error also does this)."""
    def decorator(yices_fun):
        """yices api function decorator."""
        @wraps(yices_fun)
        def wrapper(*args, **kwargs):
            """yices api function wrapper."""
            errstr = "You must initialize by calling yices_init()"
            result = yices_fun(*args, **kwargs) if __yices_library_inited__ else None
            if not  __yices_library_inited__ :
                raise YicesException(errstr)
            return result
        return wrapper
    return decorator


libyicespath = find_library("yices")
libyices = None



#########################################
#                                       #
#  Start of LOADING ZONE                #
#                                       #
#########################################

#
# Loading the library is complicated by misbehaviour on Linux
# So we manually have to go through the LD_LIBRARY_PATH, which may not
# really help anyway, since we would probably be getting the sudo
# version not the user's version. Probably the real issue is that
# on Linux yices installs in /usr/local/lib but the ctype loading probably
# expects it to be in some x86_64 archified directory. HOWEVER, if find_library
# can find the name correctly, you would expect that it could also load the
# puppy correctly.
#
def _loadYicesFromPath(path, library):
    global libyices
    try:
        if path is not None:
            libyices = CDLL(os.path.join(path, library))
        else:
            libyices = CDLL(library)
        return True
    except:
        return False

def loadYices():
    global libyicespath, libyices

    error_msg = "Yices dynamic library not found."

    if libyicespath is not None:
        #try first without hackery
        if _loadYicesFromPath(None, libyicespath):
            return
        #on linux we see if the LD_LIBRARY_PATH can help  (may not really help)
        ld_library_path = os.environ.get('LD_LIBRARY_PATH')
        if ld_library_path is not None:
            paths = ld_library_path.split(':')
            for path in paths:
                if _loadYicesFromPath(path, libyicespath):
                    return
        #try the default install location for yices on linux (this may be the real win)
        if _loadYicesFromPath('/usr/local/lib', libyicespath):
            return
        error_msg = "Yices dynamic library {0} not found. LD_LIBRARY_PATH was {1}".format(libyicespath, ld_library_path)
    # else we failed
    raise YicesException(error_msg)



loadYices()

###########################
#  VERSION AND RELATIVES  #
###########################

# const char *yices_version
yices_version = c_char_p.in_dll(libyices, "yices_version").value
"""libyices version as in '2.5.3'"""

# const char *yices_build_arch
yices_build_arch = c_char_p.in_dll(libyices, "yices_build_arch").value
"""libyices build architecture as in 'x86_64-pc-linux-gnu'"""

# const char *yices_build_mode
yices_build_mode = c_char_p.in_dll(libyices, "yices_build_mode").value
"""libyices build mode (typically either 'release' or 'debug'"""

# const char *yices_build_date
yices_build_date = c_char_p.in_dll(libyices, "yices_build_date").value
"""libyices build date as in '2017-09-08'"""

# int32_t yices_has_mcsat(void)
libyices.yices_has_mcsat.restype = c_int32
def yices_has_mcsat():
    """Returns 1 if the yices library has mcsat support, 0 otherwise."""
    return libyices.yices_has_mcsat()


def checkYices():
    """Checks that the library is not too stale to work with these bindings."""
    def _versionCheck():
        (lv_major, lv_minor, lv_revision) = [ int(x) for x in yices_version.split('.') ]
        (rv_major, rv_minor, rv_revision) = [ int(x) for x in yices_recommended_version.split('.') ]
        if lv_major < rv_major:
            return False
        if lv_major == rv_major and lv_minor < rv_minor:
            return False
        if lv_major == rv_major and lv_minor == rv_minor and lv_revision < rv_revision:
            return False
        return True
    complaint = """
    This Python package requires Yices C library version {0} or better.
    Your version is {1}.
    Please upgrade: http://yices.csl.sri.com/.
    """
    if not _versionCheck():
        raise YicesException(complaint.format(yices_recommended_version, yices_version))


checkYices()


#########################################
#                                       #
#  End of LOADING ZONE                  #
#                                       #
#########################################


#we are lazy about attempting to load gmp. The user must try
#to call a routine that needs gmp, otherwise we do not load it.
libgmppath = find_library("gmp")
libgmp = None
libgmpFailed = None


def hasGMP():
    """Returns True in the GMP library has been loaded and is ready to use, False otherwise."""
    global libgmpFailed, libgmp, libgmppath
    if libgmpFailed is True:
        return False
    if libgmp is not None:
        return True
    if libgmppath is None:
        libgmpFailed = True
        return False
    libgmp = CDLL(libgmppath)
    if libgmp is not None:
        sys.stderr.write('\nLoading gmp library from {0}.\n'.format(libgmppath))
        libgmpFailed = False
        return True
    else:
        libgmpFailed = True
        return False


# From yices_types.h

error_code_t = c_uint32 # an enum type, in yices_types.h
term_t = c_int32
type_t = c_int32
term_constructor_t = c_uint # an enum type, in yices_types.h
ctx_config_t = c_void_p # an opaque type, in yices_types.h
context_t = c_void_p # an opaque type, in yices_types.h
smt_status_t = c_uint # an enum type, in yices_types.h
param_t = c_void_p # an opaque type, in yices_types.h
model_t = c_void_p # an opaque type, in yices_types.h
#mpz_t = c_void_p
#mpq_t = c_void_p
#yval_t = c_void_p
yval_tag_t = c_uint
yices_gen_mode_t = c_void_p

class error_report_t(Structure):
    """The cause of an API error is stored in an error_report structure."""
    _fields_ = [("code", error_code_t),  # 8
                ("line", c_uint32),      # 4
                ("column", c_uint32),    # 4
                ("term1", term_t),       # 4
                ("type1", type_t),       # 4
                ("term2", term_t),       # 4
                ("type2", type_t),       # 4
                ("badval", c_int64)]     # 8

class yval_t(Structure):
    """The type of a node descriptor."""
    _fields_ = [("node_id", c_int32),
                ("node_tag", yval_tag_t)]

class term_vector_t(Structure):
    """A resizable array of terms."""
    _fields_ = [("capacity", c_uint32),
                ("size", c_uint32),
                ("data", POINTER(term_t))]

class type_vector_t(Structure):
    """A resizable array of types."""
    _fields_ = [("capacity", c_uint32),
                ("size", c_uint32),
                ("data", POINTER(type_t))]

class yval_vector_t(Structure):
    """A resizable array of node descriptors."""
    _fields_ = [("capacity", c_uint32),
                ("size", c_uint32),
                ("data", POINTER(yval_t))]

class yval_array(Array):
    """An array of node descriptors."""
    _type_ = yval_t
    _length_ = 2

# gmp types

class mpz_t(Structure):
    """Replica of the GMP mpz_t struct, it must be kept upto date with gmp.h."""
    _fields_ = [("_mp_alloc", c_int),
                ("_mp_size", c_int),
                ("_mp_d", POINTER(c_void_p))]

class mpq_t(Structure):
    """Replica of the GMP mpq_t struct, it must be kept upto date with gmp.h."""
    _fields_ = [("_mp_num", mpz_t),
                ("_mp_den", mpz_t)]

# From polylib poly.h
# class lp_upolynomial_t(Structure):
#     _fields_ = [("K", POINTER(lp_int_ring_t)),
#                 ("size", size_t),
#                 ("monomials", POINTER(ulp_monomial_t))]

lp_integer_t = mpz_t

class lp_dyadic_rational_t(Structure):
    """Replica of the Libpoly lp_dyadic_rational_t struct, it must be kept upto date with polynomial.h."""
    _fields_ = [("a", lp_integer_t),
                ("n", c_ulong)]

class lp_dyadic_interval_t(Structure):
    """Replica of the Libpoly lp_dyadic_interval_t struct, it must be kept upto date with polynomial.h."""
    _fields_ = [("a_open", c_size_t),
                ("b_open", c_size_t),
                ("is_point", c_size_t),
                ("a", lp_dyadic_rational_t),
                ("b", lp_dyadic_rational_t)]

class lp_algebraic_number_t(Structure):
    """Replica of the Libpoly lp_algebraic_number_t struct, it must be kept upto date with polynomial.h."""
    _fields_ = [("f", c_void_p), #("f", POINTER(lp_upolynomial_t)),
                ("I", lp_dyadic_interval_t),
                ("sgn_at_a", c_int),
                ("sgn_at_b", c_int)]



#from yices_types.h:

#yval_tag_t:  yval node_tag values
YVAL_UNKNOWN = 0
YVAL_BOOL = 1
YVAL_RATIONAL = 2
YVAL_ALGEBRAIC = 3
YVAL_BV = 4
YVAL_SCALAR = 5
YVAL_TUPLE = 6
YVAL_FUNCTION = 7
YVAL_MAPPING = 8


#smt_status_t
STATUS_IDLE = 0
STATUS_SEARCHING = 1
STATUS_UNKNOWN = 2
STATUS_SAT = 3
STATUS_UNSAT = 4
STATUS_INTERRUPTED = 5
STATUS_ERROR = 6

#term_constructor_t
YICES_CONSTRUCTOR_ERROR = -1
YICES_BOOL_CONSTANT = 0
YICES_ARITH_CONSTANT = 1
YICES_BV_CONSTANT = 2
YICES_SCALAR_CONSTANT = 3
YICES_VARIABLE = 4
YICES_UNINTERPRETED_TERM = 5
YICES_ITE_TERM = 6
YICES_APP_TERM = 7
YICES_UPDATE_TERM = 8
YICES_TUPLE_TERM = 9
YICES_EQ_TERM = 10
YICES_DISTINCT_TERM = 11
YICES_FORALL_TERM = 12
YICES_LAMBDA_TERM = 13
YICES_NOT_TERM = 14
YICES_OR_TERM = 15
YICES_XOR_TERM = 16
YICES_BV_ARRAY = 17
YICES_BV_DIV = 18
YICES_BV_REM = 19
YICES_BV_SDIV = 20
YICES_BV_SREM = 21
YICES_BV_SMOD = 22
YICES_BV_SHL = 23
YICES_BV_LSHR = 24
YICES_BV_ASHR = 25
YICES_BV_GE_ATOM = 26
YICES_BV_SGE_ATOM = 27
YICES_ARITH_GE_ATOM = 28
YICES_ARITH_ROOT_ATOM = 29
YICES_ABS = 30
YICES_CEIL = 31
YICES_FLOOR = 32
YICES_RDIV = 33
YICES_IDIV = 34
YICES_IMOD = 35
YICES_IS_INT_ATOM = 36
YICES_DIVIDES_ATOM = 37
YICES_SELECT_TERM = 38
YICES_BIT_TERM = 39
YICES_BV_SUM = 40
YICES_ARITH_SUM = 41
YICES_POWER_PRODUCT = 42

#yices_gen_mode_t
YICES_GEN_DEFAULT = 0
YICES_GEN_BY_SUBST = 1
YICES_GEN_BY_PROJ = 2

# From yices.h


########################################
#  GLOBAL INITIALIZATION AND CLEANUP   #
########################################


# void yices_init(void)
libyices.yices_init.restype = None
def yices_init():
    """This function must be called before anything else to initialize internal data structures."""
    global __yices_library_inited__
    __yices_library_inited__ = True
    libyices.yices_init()

# void yices_exit(void)
libyices.yices_exit.restype = None
@catch_uninitialized()
def yices_exit():
    """Delete all internal data structures and objects - this must be called to avoid memory leaks."""
    libyices.yices_exit()
    __yices_library_inited__ = False

# void yices_reset(void)
libyices.yices_reset.restype = None
@catch_uninitialized()
def yices_reset():
    """A full reset of all internal data structures (terms, types, symbol tables, contexts, models, ...)."""
    libyices.yices_reset()


# void yices_free_string(char*)
# No API for this - the functions which return a C string (e.g., yices_error_string)
# all call yices_free_string as soon as they cast it to a Python string

# void yices_set_out_of_mem_callback(void (*callback)(void))
# libyices.yices_set_out_of_mem_callback.restype = None
# CBFUNC = CFUNCTYPE(None)
# libyices.yices_set_out_of_mem_callback.argtypes = [c_void_p]


#######################
#  ERROR REPORTING    #
#######################


# error_code_t yices_error_code(void)
libyices.yices_error_code.restype = error_code_t
@catch_uninitialized()
def yices_error_code():
    """Get the last error code."""
    return libyices.yices_error_code()

# error_report_t *yices_error_report(void)
libyices.yices_error_report.restype = POINTER(error_report_t)
@catch_uninitialized()
def yices_error_report():
    """Get the last error report."""
    return libyices.yices_error_report().contents

# void yices_clear_error(void)
libyices.yices_clear_error.restype = None
@catch_uninitialized()
def yices_clear_error():
    """Clear the error report."""
    libyices.yices_clear_error()

# int32_t yices_print_error_fd(int fd)
libyices.yices_print_error_fd.restype = c_int32
libyices.yices_print_error_fd.argtypes = [c_int]
@catch_uninitialized()
def yices_print_error_fd(fd):
    """Print an error message on file descriptor fd."""
    return libyices.yices_print_error_fd(fd)

# char *yices_error_string(void)
# NOTE: restype is c_void_p in order not to trigger the automatic cast, which loses the pointer
libyices.yices_error_string.restype = c_void_p
libyices.yices_free_string.argtypes = [c_void_p]
@catch_uninitialized()
def yices_error_string():
    """Build a string from the current error code + error report structure."""
    cstrptr = libyices.yices_error_string()
    errstr = cast(cstrptr, c_char_p).value
    libyices.yices_free_string(cstrptr)
    return errstr


#################################
#   PYTHON <-> C UTILITIES      #
#################################


# Utilities for constructing:
#
# - C arrays of a certain type from python arrays
# - C arrays that are empty (i.e. zeroed) of a certain type and given length
#
#  types include: term_t type_t yval_t c_int32 c_int64.
#
# The idea being to hide as much of ctype weirdness as possible. This was a demand driven list.
# feel free to add more, or request that I (iam) add more.
#

def make_term_array(pyarray):
    """Makes a C term array object from a python array object"""
    retval = None
    if pyarray is not None:
        #weird python and ctype magic
        retval = (term_t * len(pyarray))(*pyarray)
    return retval

def make_empty_term_array(n):
    """Makes an empty C term array object of length n"""
    retval = (term_t * n)()
    return retval

def make_type_array(pyarray):
    """Makes a C term array object from a python array object"""
    retval = None
    if pyarray is not None:
        #weird python and ctype magic
        retval = (type_t * len(pyarray))(*pyarray)
    return retval


def make_empty_type_array(n):
    """Makes an empty C type array object of length n"""
    retval = (type_t * n)()
    return retval


def make_int32_array(pyarray):
    """Makes a C int32 array object from a python array object"""
    retval = None
    if pyarray is not None:
        #weird python and ctype magic
        retval = (c_int32 * len(pyarray))(*pyarray)
    return retval


def make_empty_int32_array(n):
    """Makes an empty C int32 array object of length n"""
    retval = (c_int32 * n)()
    return retval


def make_int64_array(pyarray):
    """Makes a C int64 array object from a python array object"""
    retval = None
    if pyarray is not None:
        #weird python and ctype magic
        retval = (c_int64 * len(pyarray))(*pyarray)
    return retval


def make_empty_int64_array(n):
    """Makes an empty C int64 array object of length n"""
    retval = (c_int64 * n)()
    return retval


def make_empty_yval_array(n):
    """Makes an empty C yval array object of length n"""
    retval = (yval_t * n)()
    return retval




#################################
#   VECTORS OF TERMS AND TYPES  #
#################################


# void yices_init_term_vector(term_vector_t *v)
libyices.yices_init_term_vector.restype = None
libyices.yices_init_term_vector.argtypes = [POINTER(term_vector_t)]
@catch_uninitialized()
def yices_init_term_vector(v):
    """Before calling any function that fills in a term_vector the vector object must be initialized via init_term_vector."""
    libyices.yices_init_term_vector(pointer(v))

# void yices_init_type_vector(type_vector_t *v)
libyices.yices_init_type_vector.restype = None
libyices.yices_init_type_vector.argtypes = [POINTER(type_vector_t)]
@catch_uninitialized()
def yices_init_type_vector(v):
    """Before calling any function that fills in a type_vector the vector object must be initialized via init_type_vector."""
    libyices.yices_init_type_vector(pointer(v))

# void yices_delete_term_vector(term_vector_t *v)
libyices.yices_delete_term_vector.restype = None
libyices.yices_delete_term_vector.argtypes = [POINTER(term_vector_t)]
@catch_uninitialized()
def yices_delete_term_vector(v):
    """To prevent memory leaks, a term_vector must be deleted when no longer needed."""
    libyices.yices_delete_term_vector(pointer(v))

# void yices_delete_type_vector(type_vector_t *v)
libyices.yices_delete_type_vector.restype = None
libyices.yices_delete_type_vector.argtypes = [POINTER(type_vector_t)]
@catch_uninitialized()
def yices_delete_type_vector(v):
    """To prevent memory leaks, a type_vector must be deleted when no longer needed."""
    libyices.yices_delete_type_vector(pointer(v))

# void yices_reset_term_vector(term_vector_t *v)
libyices.yices_reset_term_vector.restype = None
libyices.yices_reset_term_vector.argtypes = [POINTER(term_vector_t)]
@catch_uninitialized()
def yices_reset_term_vector(v):
    """Reset: empty the vector (reset size to 0)."""
    libyices.yices_reset_term_vector(pointer(v))

# void yices_reset_type_vector(type_vector_t *v)
libyices.yices_reset_type_vector.restype = None
libyices.yices_reset_type_vector.argtypes = [POINTER(type_vector_t)]
@catch_uninitialized()
def yices_reset_type_vector(v):
    """Reset: empty the vector (reset size to 0)."""
    libyices.yices_reset_type_vector(pointer(v))

#######################
#  TYPE CONSTRUCTORS  #
#######################

# type_t yices_bool_type(void)
libyices.yices_bool_type.restype = type_t
@catch_uninitialized()
def yices_bool_type():
    """Returns the built-in bool type."""
    return libyices.yices_bool_type()

# type_t yices_int_type(void)
libyices.yices_int_type.restype = type_t
@catch_uninitialized()
def yices_int_type():
    """Returns the built-in int type."""
    return libyices.yices_int_type()

# type_t yices_real_type(void)
libyices.yices_real_type.restype = type_t
@catch_uninitialized()
def yices_real_type():
    """Returns the built-in real type."""
    return libyices.yices_real_type()

# type_t yices_bv_type(uint32_t size)
libyices.yices_bv_type.restype = type_t
libyices.yices_bv_type.argtypes = [c_uint32]
@catch_error(-1)
def yices_bv_type(size):
    """Returns the type of bitvectors of given size (number of bits), size > 0."""
    return libyices.yices_bv_type(size)

# type_t yices_new_scalar_type(uint32_t card)
libyices.yices_new_scalar_type.restype = type_t
libyices.yices_new_scalar_type.argtypes = [c_uint32]
@catch_error(-1)
def yices_new_scalar_type(card):
    """New scalar type of given cardinality, card > 0."""
    return libyices.yices_new_scalar_type(card)

# type_t yices_new_uninterpreted_type(void)
libyices.yices_new_uninterpreted_type.restype = type_t
@catch_uninitialized()
def yices_new_uninterpreted_type():
    """New uninterpreted type, no error report."""
    return libyices.yices_new_uninterpreted_type()

# type_t yices_tuple_type(uint32_t n, const type_t tau[])
libyices.yices_tuple_type.restype = type_t
libyices.yices_tuple_type.argtypes = [c_uint32, POINTER(type_t)]
@catch_error(-1)
def yices_tuple_type(n, tau):
    """Tuple type tau[0] x ... x tau[n-1], requires n> 0 and tau[0] ... tau[n-1] to be well defined types."""
    return libyices.yices_tuple_type(n, tau)

# type_t yices_tuple_type1(type_t tau1)
libyices.yices_tuple_type1.restype = type_t
libyices.yices_tuple_type1.argtypes = [type_t]
@catch_error(-1)
def yices_tuple_type1(tau):
    """For convenience: returns a unary tuple type, tau must be a valid type."""
    return libyices.yices_tuple_type1(tau)

# type_t yices_tuple_type2(type_t tau1, type_t tau2)
libyices.yices_tuple_type2.restype = type_t
libyices.yices_tuple_type2.argtypes = [type_t, type_t]
@catch_error(-1)
def yices_tuple_type2(tau1, tau2):
    """For convenience: returns a binary tuple type, tau1, tau2 must be a valid types."""
    return libyices.yices_tuple_type2(tau1, tau2)

# type_t yices_tuple_type3(type_t tau1, type_t tau2, type_t tau3)
libyices.yices_tuple_type3.restype = type_t
libyices.yices_tuple_type3.argtypes = [type_t, type_t, type_t]
@catch_error(-1)
def yices_tuple_type3(tau1, tau2, tau3):
    """For convenience: returns a ternary tuple type, tau1, tau2, tau3 must be a valid types."""
    return libyices.yices_tuple_type3(tau1, tau2, tau3)

# type_t yices_function_type(uint32_t n, const type_t dom[], type_t range)
libyices.yices_function_type.restype = type_t
libyices.yices_function_type.argtypes = [c_uint32, POINTER(type_t), type_t]
@catch_error(-1)
def yices_function_type(n, dom, ran):
    """Function type: dom[0] ... dom[n-1] -> ran, requires n>0, and dom[0] ... dom[n-1] and ran to be well defined."""
    return libyices.yices_function_type(n, dom, ran)

# type_t yices_function_type1(type_t tau1, type_t range)
libyices.yices_function_type1.restype = type_t
libyices.yices_function_type1.argtypes = [type_t, type_t]
@catch_error(-1)
def yices_function_type1(tau1, ran):
    """For convenience: returns the function type tau1 -> ran, tau1, ran must be a valid types."""
    return libyices.yices_function_type1(tau1, ran)

# type_t yices_function_type2(type_t tau1, type_t tau2, type_t range)
libyices.yices_function_type2.restype = type_t
libyices.yices_function_type2.argtypes = [type_t, type_t, type_t]
@catch_error(-1)
def yices_function_type2(tau1, tau2, ran):
    """For convenience: returns the function type tau1, tau2 -> ran, tau1, tau2, ran must be a valid types."""
    return libyices.yices_function_type2(tau1, tau2, ran)

# type_t yices_function_type3(type_t tau1, type_t tau2, type_t tau3, type_t range)
libyices.yices_function_type3.restype = type_t
libyices.yices_function_type3.argtypes = [type_t, type_t, type_t, type_t]
@catch_error(-1)
def yices_function_type3(tau1, tau2, tau3, ran):
    """For convenience: returns the function type tau1, tau2, tau3 -> ran, tau1, tau2, tau3, ran must be a valid types."""
    return libyices.yices_function_type3(tau1, tau2, tau3, ran)

#########################
#   TYPE EXPLORATION    #
#########################

# int32_t yices_type_is_bool(type_t tau)
libyices.yices_type_is_bool.restype = c_int32
libyices.yices_type_is_bool.argtypes = [type_t]
@catch_error(0)
def yices_type_is_bool(tau):
    """Returns 1 if tau is the built-in bool type, 0 otherwise."""
    return libyices.yices_type_is_bool(tau)

# int32_t yices_type_is_int(type_t tau)
libyices.yices_type_is_int.restype = c_int32
libyices.yices_type_is_int.argtypes = [type_t]
@catch_error(0)
def yices_type_is_int(tau):
    """Returns 1 if tau is the built-in int type, 0 otherwise."""
    return libyices.yices_type_is_int(tau)

# int32_t yices_type_is_real(type_t tau)
libyices.yices_type_is_real.restype = c_int32
libyices.yices_type_is_real.argtypes = [type_t]
@catch_error(0)
def yices_type_is_real(tau):
    """Returns 1 if tau is the built-in real type, 0 otherwise."""
    return libyices.yices_type_is_real(tau)

# int32_t yices_type_is_arithmetic(type_t tau)
libyices.yices_type_is_arithmetic.restype = c_int32
libyices.yices_type_is_arithmetic.argtypes = [type_t]
@catch_error(0)
def yices_type_is_arithmetic(tau):
    """Returns 1 if tau is either the int or real type, 0 otherwise."""
    return libyices.yices_type_is_arithmetic(tau)

# int32_t yices_type_is_bitvector(type_t tau)
libyices.yices_type_is_bitvector.restype = c_int32
libyices.yices_type_is_bitvector.argtypes = [type_t]
@catch_error(0)
def yices_type_is_bitvector(tau):
    """Returns 1 if tau is a bitvector type, 0 otherwise."""
    return libyices.yices_type_is_bitvector(tau)

# int32_t yices_type_is_tuple(type_t tau)
libyices.yices_type_is_tuple.restype = c_int32
libyices.yices_type_is_tuple.argtypes = [type_t]
@catch_error(0)
def yices_type_is_tuple(tau):
    """Returns 1 if tau is a tuple type, 0 otherwise."""
    return libyices.yices_type_is_tuple(tau)

# int32_t yices_type_is_function(type_t tau)
libyices.yices_type_is_function.restype = c_int32
libyices.yices_type_is_function.argtypes = [type_t]
@catch_error(0)
def yices_type_is_function(tau):
    """Returns 1 if tau is a function type, 0 otherwise."""
    return libyices.yices_type_is_function(tau)

# int32_t yices_type_is_scalar(type_t tau)
libyices.yices_type_is_scalar.restype = c_int32
libyices.yices_type_is_scalar.argtypes = [type_t]
@catch_error(0)
def yices_type_is_scalar(tau):
    """Returns 1 if tau is a scalar type, 0 otherwise."""
    return libyices.yices_type_is_scalar(tau)

# int32_t yices_type_is_uninterpreted(type_t tau)
libyices.yices_type_is_uninterpreted.restype = c_int32
libyices.yices_type_is_uninterpreted.argtypes = [type_t]
@catch_error(0)
def yices_type_is_uninterpreted(tau):
    """Returns 1 if tau is a uninterpreted type, 0 otherwise."""
    return libyices.yices_type_is_uninterpreted(tau)

# int32_t yices_test_subtype(type_t tau, type_t sigma)
libyices.yices_test_subtype.restype = c_int32
libyices.yices_test_subtype.argtypes = [type_t, type_t]
@catch_error(0)
def yices_test_subtype(tau, sigma):
    """Returns 1 if tau is a subtype of sigma, 0 otherwise."""
    return libyices.yices_test_subtype(tau, sigma)

# uint32_t yices_bvtype_size(type_t tau)
libyices.yices_bvtype_size.restype = c_uint32
libyices.yices_bvtype_size.argtypes = [type_t]
@catch_error(0)
def yices_bvtype_size(tau):
    """Returns the number of bits for type tau, or 0 if there's and error."""
    return libyices.yices_bvtype_size(tau)

# uint32_t yices_scalar_type_card(type_t tau)
libyices.yices_scalar_type_card.restype = c_uint32
libyices.yices_scalar_type_card.argtypes = [type_t]
@catch_error(0)
def yices_scalar_type_card(tau):
    """Returns the cardinality of teh scalar tau, or 0 if there's and error."""
    return libyices.yices_scalar_type_card(tau)

# int32_t yices_type_num_children(type_t tau)
libyices.yices_type_num_children.restype = c_int32
libyices.yices_type_num_children.argtypes = [type_t]
@catch_error(-1)
def yices_type_num_children(tau):
    """Returns the number of children of type tau.

     - if tau is a tuple type (tuple tau_1 ... tau_n), returns n
     - if tau is a function type (-> tau_1 ... tau_n sigma), returns n+1
     - if tau is any other type, returns 0
    """
    return libyices.yices_type_num_children(tau)

# type_t yices_type_child(type_t tau, int32_t i)
libyices.yices_type_child.restype = type_t
libyices.yices_type_child.argtypes = [type_t, c_int32]
@catch_error(-1)
def yices_type_child(tau, i):
    """Returns the i-th child of type tau."""
    return libyices.yices_type_child(tau, i)

# int32_t yices_type_children(type_t tau, type_vector_t *v)
libyices.yices_type_children.restype = c_int32
libyices.yices_type_children.argtypes = [type_t, POINTER(type_vector_t)]
@catch_error(-1)
def yices_type_children(tau, v):
    """Collect all the children of type tau in vector v."""
    return libyices.yices_type_children(tau, v)


########################
#  TERM CONSTRUCTORS   #
########################

# term_t yices_true(void)
libyices.yices_true.restype = term_t
@catch_uninitialized()
def yices_true():
    """Returns the true term."""
    return libyices.yices_true()

# term_t yices_false(void)
libyices.yices_false.restype = term_t
@catch_uninitialized()
def yices_false():
    """Returns the false term."""
    return libyices.yices_false()

# term_t yices_constant(type_t tau, int32_t index)
libyices.yices_constant.restype = term_t
libyices.yices_constant.argtypes = [type_t, c_int32]
@catch_error(-1)
def yices_constant(tau, index):
    """Returns the constant of type tau and id = index."""
    return libyices.yices_constant(tau, index)

# term_t yices_new_uninterpreted_term(type_t tau)
libyices.yices_new_uninterpreted_term.restype = term_t
libyices.yices_new_uninterpreted_term.argtypes = [type_t]
@catch_error(-1)
def yices_new_uninterpreted_term(tau):
    """Returns an uninterpreted term of type tau."""
    return libyices.yices_new_uninterpreted_term(tau)

# term_t yices_new_variable(type_t tau)
libyices.yices_new_variable.restype = term_t
libyices.yices_new_variable.argtypes = [type_t]
@catch_error(-1)
def yices_new_variable(tau):
    """Returns a newly created  variable of type tau."""
    return libyices.yices_new_variable(tau)

# term_t yices_application(term_t fun, uint32_t n, const term_t arg[])
libyices.yices_application.restype = term_t
libyices.yices_application.argtypes = [term_t, c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_application(fun, n, arg):
    """Returns the application of an uninterpreted function to n arguments."""
    return libyices.yices_application(fun, n, arg)

# term_t yices_application1(term_t fun, term_t arg1)
libyices.yices_application1.restype = term_t
libyices.yices_application1.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_application1(fun, arg1):
    """Returns the application of unary fun to arg1."""
    return libyices.yices_application1(fun, arg1)

# term_t yices_application2(term_t fun, term_t arg1, term_t arg2)
libyices.yices_application2.restype = term_t
libyices.yices_application2.argtypes = [term_t, term_t, term_t]
@catch_error(-1)
def yices_application2(fun, arg1, arg2):
    """Returns the application of binary fun to arg1 and arg2."""
    return libyices.yices_application2(fun, arg1, arg2)

# term_t yices_application3(term_t fun, term_t arg1, term_t arg2, term_t arg3)
libyices.yices_application3.restype = term_t
libyices.yices_application3.argtypes = [term_t, term_t, term_t, term_t]
@catch_error(-1)
def yices_application3(fun, arg1, arg2, arg3):
    """Returns the application of ternary fun to arg1, arg2 and arg3."""
    return libyices.yices_application3(fun, arg1, arg2, arg3)

# term_t yices_ite(term_t cond, term_t then_term, term_t else_term)
libyices.yices_ite.restype = term_t
libyices.yices_ite.argtypes = [term_t, term_t, term_t]
@catch_error(-1)
def yices_ite(cond, then_term, else_term):
    """Returns the if-then-else of the given cond and terms."""
    return libyices.yices_ite(cond, then_term, else_term)

# term_t yices_eq(term_t left, term_t right)
libyices.yices_eq.restype = term_t
libyices.yices_eq.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_eq(left, right):
    """Returns the equality term of left and right."""
    return libyices.yices_eq(left, right)

# term_t yices_neq(term_t left, term_t right)
libyices.yices_neq.restype = term_t
libyices.yices_neq.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_neq(left, right):
    """Returns the inequality term of left and right."""
    return libyices.yices_neq(left, right)

# term_t yices_not(term_t arg)
libyices.yices_not.restype = term_t
libyices.yices_not.argtypes = [term_t]
@catch_error(-1)
def yices_not(arg):
    """Returns the negation term of arg."""
    return libyices.yices_not(arg)

# term_t yices_or(uint32_t n, term_t arg[])
libyices.yices_or.restype = term_t
libyices.yices_or.argtypes = [c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_or(n, arg):
    """Returns (or  arg[0] ... arg[n-1])."""
    return libyices.yices_or(n, arg)

# term_t yices_and(uint32_t n, term_t arg[])
libyices.yices_and.restype = term_t
libyices.yices_and.argtypes = [c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_and(n, arg):
    """Returns (and  arg[0] ... arg[n-1])."""
    return libyices.yices_and(n, arg)

# term_t yices_xor(uint32_t n, term_t arg[])
libyices.yices_xor.restype = term_t
libyices.yices_xor.argtypes = [c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_xor(n, arg):
    """Returns (and  arg[0] ... arg[n-1])."""
    return libyices.yices_xor(n, arg)

# term_t yices_or2(term_t t1, term_t t2)
libyices.yices_or2.restype = term_t
libyices.yices_or2.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_or2(t1, t2):
    """Returns (or t1 t2)."""
    return libyices.yices_or2(t1, t2)

# term_t yices_and2(term_t t1, term_t t2)
libyices.yices_and2.restype = term_t
libyices.yices_and2.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_and2(t1, t2):
    """Returns (and t1 t2)."""
    return libyices.yices_and2(t1, t2)

# term_t yices_xor2(term_t t1, term_t t2)
libyices.yices_xor2.restype = term_t
libyices.yices_xor2.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_xor2(t1, t2):
    """Returns (xor t1 t2)."""
    return libyices.yices_xor2(t1, t2)

# term_t yices_or3(term_t t1, term_t t2, term_t t3)
libyices.yices_or3.restype = term_t
libyices.yices_or3.argtypes = [term_t, term_t, term_t]
@catch_error(-1)
def yices_or3(t1, t2, t3):
    """Returns (or t1 t2 t3)."""
    return libyices.yices_or3(t1, t2, t3)

# term_t yices_and3(term_t t1, term_t t2, term_t t3)
libyices.yices_and3.restype = term_t
libyices.yices_and3.argtypes = [term_t, term_t, term_t]
@catch_error(-1)
def yices_and3(t1, t2, t3):
    """Returns (and t1 t2 t3)."""
    return libyices.yices_and3(t1, t2, t3)

# term_t yices_xor3(term_t t1, term_t t2, term_t t3)
libyices.yices_xor3.restype = term_t
libyices.yices_xor3.argtypes = [term_t, term_t, term_t]
@catch_error(-1)
def yices_xor3(t1, t2, t3):
    """Returns (xor t1 t2 t3)."""
    return libyices.yices_xor3(t1, t2, t3)

# term_t yices_iff(term_t left, term_t right)
libyices.yices_iff.restype = term_t
libyices.yices_iff.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_iff(left, right):
    """Returns (iff left right)."""
    return libyices.yices_iff(left, right)

# term_t yices_implies(term_t left, term_t right)
libyices.yices_implies.restype = term_t
libyices.yices_implies.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_implies(left, right):
    """Returns (implies left right)."""
    return libyices.yices_implies(left, right)

# term_t yices_tuple(uint32_t n, const term_t arg[])
libyices.yices_tuple.restype = term_t
libyices.yices_tuple.argtypes = [c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_tuple(n, arg):
    """Returns (tuple  arg[0] ... arg[n-1])."""
    return libyices.yices_tuple(n, arg)

# term_t yices_pair(term_t arg1, term_t arg2)
libyices.yices_pair.restype = term_t
libyices.yices_pair.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_pair(arg1, arg2):
    """Returns (tuple arg1 arg2)."""
    return libyices.yices_pair(arg1, arg2)

# term_t yices_triple(term_t arg1, term_t arg2, term_t arg3)
libyices.yices_triple.restype = term_t
libyices.yices_triple.argtypes = [term_t, term_t, term_t]
@catch_error(-1)
def yices_triple(arg1, arg2, arg3):
    """Returns (tuple arg1 arg2 arg3)."""
    return libyices.yices_triple(arg1, arg2, arg3)

# term_t yices_select(uint32_t index, term_t tuple)
libyices.yices_select.restype = term_t
libyices.yices_select.argtypes = [c_uint32, term_t]
@catch_error(-1)
def yices_select(index, tup):
    """Tuple projection, returns the index-th component of the tuple."""
    return libyices.yices_select(index, tup)

# term_t yices_tuple_update(term_t tuple, uint32_t index, term_t new_v)
libyices.yices_tuple_update.restype = term_t
libyices.yices_tuple_update.argtypes = [term_t, c_uint32, term_t]
@catch_error(-1)
def yices_tuple_update(tup, index, new_v):
    """Tuple update, replaces the index-th component of tuple by new_v."""
    return libyices.yices_tuple_update(tup, index, new_v)

# term_t yices_update(term_t fun, uint32_t n, const term_t arg[], term_t new_v)
libyices.yices_update.restype = term_t
libyices.yices_update.argtypes = [term_t, c_uint32, POINTER(term_t), term_t]
@catch_error(-1)
def yices_update(fun, n, arg, new_v):
    """Function update."""
    return libyices.yices_update(fun, n, arg, new_v)

# term_t yices_update1(term_t fun, term_t arg1, term_t new_v)
libyices.yices_update1.restype = term_t
libyices.yices_update1.argtypes = [term_t, term_t, term_t]
@catch_error(-1)
def yices_update1(fun, arg1, new_v):
    """Variant of update for n = 1."""
    return libyices.yices_update1(fun, arg1, new_v)

# term_t yices_update2(term_t fun, term_t arg1, term_t arg2, term_t new_v)
libyices.yices_update2.restype = term_t
libyices.yices_update2.argtypes = [term_t, term_t, term_t, term_t]
@catch_error(-1)
def yices_update2(fun, arg1, arg2, new_v):
    """Variant of update for n = 2."""
    return libyices.yices_update2(fun, arg1, arg2, new_v)

# term_t yices_update3(term_t fun, term_t arg1, term_t arg2, term_t arg3, term_t new_v)
libyices.yices_update3.restype = term_t
libyices.yices_update3.argtypes = [term_t, term_t, term_t, term_t, term_t]
@catch_error(-1)
def yices_update3(fun, arg1, arg2, arg3, new_v):
    """Variant of update for n = 3."""
    return libyices.yices_update3(fun, arg1, arg2, arg3, new_v)

# term_t yices_distinct(uint32_t n, term_t arg[])
libyices.yices_distinct.restype = term_t
libyices.yices_distinct.argtypes = [c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_distinct(n, arg):
    """Returns (distinct arg[0] ... arg[n-1])."""
    return libyices.yices_distinct(n, arg)

# term_t yices_forall(uint32_t n, term_t var[], term_t body)
libyices.yices_forall.restype = term_t
libyices.yices_forall.argtypes = [c_uint32, POINTER(term_t), term_t]
@catch_error(-1)
def yices_forall(n, var, body):
    """Returns  (forall (var[0] ... var[n-1]) body)."""
    return libyices.yices_forall(n, var, body)

# term_t yices_exists(uint32_t n, term_t var[], term_t body)
libyices.yices_exists.restype = term_t
libyices.yices_exists.argtypes = [c_uint32, POINTER(term_t), term_t]
@catch_error(-1)
def yices_exists(n, var, body):
    """Returns  (exists (var[0] ... var[n-1]) body)."""
    return libyices.yices_exists(n, var, body)

# term_t yices_lambda(uint32_t n, const term_t var[], term_t body)
libyices.yices_lambda.restype = term_t
libyices.yices_lambda.argtypes = [c_uint32, POINTER(term_t), term_t]
@catch_error(-1)
def yices_lambda(n, var, body):
    """Returns  (lambda (var[0] ... var[n-1]) body)."""
    return libyices.yices_lambda(n, var, body)


###################################
#  ARITHMETIC TERM CONSTRUCTORS   #
###################################

# term_t yices_zero(void)
libyices.yices_zero.restype = term_t
@catch_uninitialized()
def yices_zero():
    """Returns the yices term for zero."""
    return libyices.yices_zero()

# term_t yices_int32(int32_t val)
libyices.yices_int32.restype = term_t
libyices.yices_int32.argtypes = [c_int32]
@catch_uninitialized()
def yices_int32(val):
    """Returns a constant term for the given 32 bit int."""
    return libyices.yices_int32(val)

# term_t yices_int64(int64_t val)
libyices.yices_int64.restype = term_t
libyices.yices_int64.argtypes = [c_int64]
@catch_uninitialized()
def yices_int64(val):
    """Returns a constant term for the given 64 bit int."""
    return libyices.yices_int64(val)

# term_t yices_rational32(int32_t num, uint32_t den)
libyices.yices_rational32.restype = term_t
libyices.yices_rational32.argtypes = [c_int32, c_int32]
@catch_error(-1)
def yices_rational32(num, den):
    """Returns a constant rational term from the given 32 bit numerator and denominator.

    rational32(num, den):
    - den must be non-zero
    - common factors are removed

    Error report:
    if den is zero
    code = DIVISION_BY_ZERO
    """
    return libyices.yices_rational32(num, den)

# term_t yices_rational64(int64_t num, uint64_t den)
libyices.yices_rational64.restype = term_t
libyices.yices_rational64.argtypes = [c_int64, c_int64]
@catch_error(-1)
def yices_rational64(num, den):
    """Returns a constant rational term from the given 64 bit numerator and denominator.

    rational32(num, den):
    - den must be non-zero
    - common factors are removed

    Error report:
    if den is zero
    code = DIVISION_BY_ZERO
    """
    return libyices.yices_rational64(num, den)

# term_t yices_mpz(const mpz_t z)
libyices.yices_mpz.restype = term_t
libyices.yices_mpz.argtypes = [POINTER(mpz_t)]
@catch_uninitialized()
def yices_mpz(z):
    """Returns the constant term from the given GMP integer."""
    return libyices.yices_mpz(z)

# term_t yices_mpq(const mpq_t q)
libyices.yices_mpq.restype = term_t
libyices.yices_mpq.argtypes = [POINTER(mpq_t)]
@catch_uninitialized()
def yices_mpq(q):
    """Returns the constant term from the given GMP rational, which must be canonicalized."""
    return libyices.yices_mpq(q)


# term_t yices_parse_rational(const char *s)
libyices.yices_parse_rational.restype = term_t
libyices.yices_parse_rational.argtypes = [c_char_p]
@catch_error(-1)
def yices_parse_rational(s):
    """Converts a string to a rational or integer term.

    The string format is
        <optional_sign> <numerator>/<denominator>
     or <optional_sign> <numerator>

    where <optional_sign> is + or - or nothing
    <numerator> and <denominator> are sequences of
    decimal digits.

    Error report:
      code = INVALID_RATIONAL_FORMAT if s is not in this format
      code = DIVISION_BY_ZERO if the denominator is zero

    """
    return libyices.yices_parse_rational(s)

# term_t yices_parse_float(const char *s)
libyices.yices_parse_float.restype = term_t
libyices.yices_parse_float.argtypes = [c_char_p]
@catch_error(-1)
def yices_parse_float(s):
    """Converts a string in  floating point format to a rational constant term.

    The string must be in one of the following formats:
      <optional sign> <integer part> . <fractional part>
      <optional sign> <integer part> <exp> <optional sign> <integer>
      <optional sign> <integer part> . <fractional part> <exp> <optional sign> <integer>

    where <optional sign> is + or - or nothing
          <exp> is either 'e' or 'E'

    Error report:
    code = INVALID_FLOAT_FORMAT
    """
    return libyices.yices_parse_float(s)

#
# ARITHMETIC OPERATIONS
#

# term_t yices_add(term_t t1, term_t t2)     // t1 + t2
libyices.yices_add.restype = term_t
libyices.yices_add.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_add(t1, t2):
    """Returns the term (t1 + t2) from the given terms, or NULL_TERM if there's an error."""
    return libyices.yices_add(t1, t2)

# term_t yices_sub(term_t t1, term_t t2)     // t1 - t2
libyices.yices_sub.restype = term_t
libyices.yices_sub.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_sub(t1, t2):
    """Returns the term (t1 - t2) from the given terms, or NULL_TERM if there's an error."""
    return libyices.yices_sub(t1, t2)

# term_t yices_neg(term_t t1)                // -t1
libyices.yices_neg.restype = term_t
libyices.yices_neg.argtypes = [term_t]
@catch_error(-1)
def yices_neg(t1):
    """Returns the term (- t1) from the given term t1, or NULL_TERM if there's an error."""
    return libyices.yices_neg(t1)

# term_t yices_mul(term_t t1, term_t t2)     // t1 * t2
libyices.yices_mul.restype = term_t
libyices.yices_mul.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_mul(t1, t2):
    """Returns the term (t1 * t2) from the given terms, or NULL_TERM if there's an error."""
    return libyices.yices_mul(t1, t2)

# term_t yices_square(term_t t1)             // t1 * t1
libyices.yices_square.restype = term_t
libyices.yices_square.argtypes = [term_t]
@catch_error(-1)
def yices_square(t1):
    """Returns the term (t1 * t1) from the given term t1, or NULL_TERM if there's an error."""
    return libyices.yices_square(t1)

# term_t yices_power(term_t t1, uint32_t d)  // t1 ^ d
libyices.yices_power.restype = term_t
libyices.yices_power.argtypes = [term_t, c_uint32]
@catch_error(-1)
def yices_power(t1, d):
    """Returns the term (t1 ^ d) from the given terms, or NULL_TERM if there's an error."""
    return libyices.yices_power(t1, d)

# term_t yices_sum(uint32_t n, const term_t t[])
libyices.yices_sum.restype = term_t
libyices.yices_sum.argtypes = [c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_sum(n, t):
    """Returns the term (t[0] + ... + t[n-1]) from the given term array t of length n, or NULL_TERM if there's an error."""
    return libyices.yices_sum(n, t)

# term_t yices_product(uint32_t n, const term_t t[])
libyices.yices_product.restype = term_t
libyices.yices_product.argtypes = [c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_product(n, t):
    """Returns the term (t[0] * ... * t[n-1]) from the given arithmetic term array t of length n, or NULL_TERM if there's an error."""
    return libyices.yices_product(n, t)

# term_t yices_division(term_t t1, term_t t2)
libyices.yices_division.restype = term_t
libyices.yices_division.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_division(t1, t2):
    """Returns the term (t1 / t2) from the given terms, or NULL_TERM if there's an error.

    division(t1, t2):
    t1 and t2 must be arithmetic terms

    NOTE: Until Yices 2.5.0, t2 was required to be a non-zero constant.
    This is no longer the case: t2 can be any arithmetic term.

    Return NULL_TERM if there's an error

    Error report:
    if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
    if t1 or t2 is not an arithmetic term
       code = ARITHTERM_REQUIRED
       term1 = t1 or t2
    """
    return libyices.yices_division(t1, t2)

# term_t yices_idiv(term_t t1, term_t t2)
libyices.yices_idiv.restype = term_t
libyices.yices_idiv.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_idiv(t1, t2):
    """Returns the interger division of t1 by t1.

    idiv(t1, t2):
    t1 and t2 must arithmetic terms

    The semantics is as defined in SMT-LIB 2.0 (theory Ints),
    except that t1 and t2 are not required to be integer.

    NOTE: Until Yices 2.5.0, t2 was required to be a non-zero constant.
    This is no longer the case: t2 can be any arithmetic term.

    The functions (div t1 t2) and (mod t1 t2) satisfy the following
    constraints:
       t1 = (div t1 t2) t2 + (mod t1 t2)
       0 <= (mod t1 t2) < (abs t2)
       (div t1 t2) is an integer

    The functions return NULL_TERM if there's an error.

    Error report:
    if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
    if t1 or t2 is not an arithmetic term
       code = ARITHTERM_REQUIRED
       term1 = t1 or t2
    """
    return libyices.yices_idiv(t1, t2)

# term_t yices_imod(term_t t1, term_t t2)
libyices.yices_imod.restype = term_t
libyices.yices_imod.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_imod(t1, t2):
    """Returns the interger modulus of t1 by t1.

    imod(t1, t2):
    t1 and t2 must arithmetic terms

    The semantics is as defined in SMT-LIB 2.0 (theory Ints),
    except that t1 and t2 are not required to be integer.

    NOTE: Until Yices 2.5.0, t2 was required to be a non-zero constant.
    This is no longer the case: t2 can be any arithmetic term.

    The functions (div t1 t2) and (mod t1 t2) satisfy the following
    constraints:
       t1 = (div t1 t2) t2 + (mod t1 t2)
       0 <= (mod t1 t2) < (abs t2)
       (div t1 t2) is an integer

    The functions return NULL_TERM if there's an error.

    Error report:
    if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
    if t1 or t2 is not an arithmetic term
       code = ARITHTERM_REQUIRED
       term1 = t1 or t2
    """
    return libyices.yices_imod(t1, t2)

# term_t yices_divides_atom(term_t t1, term_t t2)
libyices.yices_divides_atom.restype = term_t
libyices.yices_divides_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_divides_atom(t1, t2):
    """Contructs a divisibility test term.

    divides_atom(t1, t2):
    t1 must be an arihtmetic constant.
    t2 must be an arithmetic term.

    This function constructs the atom (divides t1 t2).
    The semantics is
      (divides t1 t2) IFF (there is an integer k such that t2 = k t1)

    The functions return NULL_TERM if there's an error.

    Error report:
    if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
    if t1 is not an arithmetic term
       code = ARITHTERM_REQUIRED
       term1 = t1
    if t2 is not an arithmetic constant
       code = ARITHCONSTANT_REQUIRED
       term1 = t2
    """
    return libyices.yices_divides_atom(t1, t2)

# term_t yices_is_int_atom(term_t t)
libyices.yices_is_int_atom.restype = term_t
libyices.yices_is_int_atom.argtypes = [term_t]
@catch_error(-1)
def yices_is_int_atom(t):
    """Constructs an integral test term.

    is_int_atom(t):
     - t must be an arithmetic term.

     This function constructs the atom (is-int t) as defined in
     SMT-LIB 2: (is-int t) is true iff t is an integer. Also, we have
     (is-int t) iff (divides 1 t).

     The function returns NULL_TERM if there's an error.

     Error report:
     if t is not valid
        code = INVALID_TERM
        term1 = t
     if t is not an arithmetic term
        code = ARITHTERM_REQUIRED
        term1 = t
    """
    return libyices.yices_is_int_atom(t)

# term_t yices_abs(term_t t)
libyices.yices_abs.restype = term_t
libyices.yices_abs.argtypes = [term_t]
@catch_error(-1)
def yices_abs(t):
    """Constructs the absolute value of the arithmetic term.

     Error report:
     if t is not valid
        code = INVALID_TERM
        term1 = t
     if t is not an arithmetic term
        code = ARITHTERM_REQUIRED
        term1 = t
    """
    return libyices.yices_abs(t)

# term_t yices_floor(term_t t)
libyices.yices_floor.restype = term_t
libyices.yices_floor.argtypes = [term_t]
@catch_error(-1)
def yices_floor(t):
    """
    Constructs the floor of the arithmetic term.

    floor(t) is the largest integer that's less than or equal to t
    ceiling t is the smallest integer that's greater than or equal to t
    The function return NULL_TERM if there's an error.

     Error report:
     if t is not valid
        code = INVALID_TERM
        term1 = t
     if t is not an arithmetic term
        code = ARITHTERM_REQUIRED
        term1 = t
    """
    return libyices.yices_floor(t)

# term_t yices_ceil(term_t t)
libyices.yices_ceil.restype = term_t
libyices.yices_ceil.argtypes = [term_t]
@catch_error(-1)
def yices_ceil(t):
    """
    Constructs the ceiling  of the arithmetic term.

    The function return NULL_TERM if there's an error.

     Error report:
     if t is not valid
        code = INVALID_TERM
        term1 = t
     if t is not an arithmetic term
        code = ARITHTERM_REQUIRED
        term1 = t
    """
    return libyices.yices_ceil(t)

#
# POLYNOMIALS
#

# term_t yices_poly_int32(uint32_t n, const int32_t a[], const term_t t[])
libyices.yices_poly_int32.restype = term_t
libyices.yices_poly_int32.argtypes = [c_uint32, POINTER(c_int32), POINTER(term_t)]
@catch_error(-1)
def yices_poly_int32(n, a, t):
    """Constructs a polynomial with 32 bit integer coefficients.

    poly_int32(n, a, t):
    - a and t must both be arrays of size n

    constructs the term a_0 t_0 + ... + a_{n-1} t_{n-1}
    given n constant coefficients a_0, ..., a_{n-1} and
          n arithmetic terms t_0, ..., t_{n-1}.

    If there's an error, the functions return NULL_TERM (-1).

    Error reports:
    if t[i] is not valid
      code = INVALID_TERM
      term1 = t[i]
    if t[i] is not an arithmetic term
      code = ARITHTERM_REQUIRED
      term1 = t[i]
    """
    return libyices.yices_poly_int32(n, a, t)

# term_t yices_poly_int64(uint32_t n, const int64_t a[], const term_t t[])
libyices.yices_poly_int64.restype = term_t
libyices.yices_poly_int64.argtypes = [c_uint32, POINTER(c_int64), POINTER(term_t)]
@catch_error(-1)
def yices_poly_int64(n, a, t):
    """Constructs a polynomial with 64 bit integer coefficients.

    poly_int64(n, a, t):
    - a and t must both be arrays of size n
    construct the term a_0 t_0 + ... + a_{n-1} t_{n-1}
    given n constant coefficients a_0, ..., a_{n-1} and
          n arithmetic terms t_0, ..., t_{n-1}.

    If there's an error, the functions return NULL_TERM (-1).

    Error reports:
    if t[i] is not valid
      code = INVALID_TERM
      term1 = t[i]
    if t[i] is not an arithmetic term
      code = ARITHTERM_REQUIRED
      term1 = t[i]
    """
    return libyices.yices_poly_int64(n, a, t)

# term_t yices_poly_rational32(uint32_t n, const int32_t num[], const uint32_t den[], const term_t t[])
libyices.yices_poly_rational32.restype = term_t
libyices.yices_poly_rational32.argtypes = [c_uint32, POINTER(c_int32), POINTER(c_int32), POINTER(term_t)]
@catch_error(-1)
def yices_poly_rational32(n, num, den, t):
    """Constructs a polynomial with rational 32 bit coefficients

    poly_rational32(n, num, den, t):
     - den, num, and t must be arrays of size n
     - the coefficient a_i is num[i]/den[i]

     Error report:
     if den[i] is 0
       code = DIVISION_BY_ZERO
    """
    return libyices.yices_poly_rational32(n, num, den, t)

# term_t yices_poly_rational64(uint32_t n, const int64_t num[], const uint64_t den[], const term_t t[])
libyices.yices_poly_rational64.restype = term_t
libyices.yices_poly_rational64.argtypes = [c_uint32, POINTER(c_int64), POINTER(c_int64), POINTER(term_t)]
@catch_error(-1)
def yices_poly_rational64(n, num, den, t):
    """Constructs a polynomial with rational 64 bit coefficients

    poly_rational64(n, num, den, t):
     - den, num, and t must be arrays of size n
     - the coefficient a_i is num[i]/den[i]

     Error report:
     if den[i] is 0
       code = DIVISION_BY_ZERO
    """
    return libyices.yices_poly_rational64(n, num, den, t)

# term_t yices_poly_mpz(uint32_t n, const mpz_t z[], const term_t t[])
libyices.yices_poly_mpz.restype = term_t
libyices.yices_poly_mpz.argtypes = [c_uint32, POINTER(mpz_t), POINTER(term_t)]
@catch_error(-1)
def yices_poly_mpz(n, z, t):
    """Constructs a polynomial with GMP integer coefficients.
    """
    return libyices.yices_poly_mpz(n, z, t)

# term_t yices_poly_mpq(uint32_t n, const mpq_t q[], const term_t t[])
libyices.yices_poly_mpq.restype = term_t
libyices.yices_poly_mpq.argtypes = [c_uint32, POINTER(mpq_t), POINTER(term_t)]
@catch_error(-1)
def yices_poly_mpq(n, q, t):
    """Constructs a polynomial with GMP rational coefficients.

    poly_mpq(n, q, t):
    the rationals q[0 ... n-1] must all be canonicalized.
    """
    return libyices.yices_poly_mpq(n, q, t)

#
# ARITHMETIC ATOMS
#

# term_t yices_arith_eq_atom(term_t t1, term_t t2)   // t1 == t2
libyices.yices_arith_eq_atom.restype = term_t
libyices.yices_arith_eq_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_arith_eq_atom(t1, t2):
    """Creates the term (t1 == t2), or NULL_TERM if there's an error (NULL_TERM = -1).

    Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not an arithmetic term
       code = ARITHTERM_REQUIRED
       term1 = t1 or t2.
    """
    return libyices.yices_arith_eq_atom(t1, t2)

# term_t yices_arith_neq_atom(term_t t1, term_t t2)  // t1 != t2
libyices.yices_arith_neq_atom.restype = term_t
libyices.yices_arith_neq_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_arith_neq_atom(t1, t2):
    """Creates the term (t1 != t2), or NULL_TERM if there's an error (NULL_TERM = -1).

    Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not an arithmetic term
       code = ARITHTERM_REQUIRED
       term1 = t1 or t2.
    """
    return libyices.yices_arith_neq_atom(t1, t2)

# term_t yices_arith_geq_atom(term_t t1, term_t t2)  // t1 >= t2
libyices.yices_arith_geq_atom.restype = term_t
libyices.yices_arith_geq_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_arith_geq_atom(t1, t2):
    """Creates the term (t1 >= t2), or NULL_TERM if there's an error (NULL_TERM = -1).

    Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not an arithmetic term
       code = ARITHTERM_REQUIRED
       term1 = t1 or t2.
    """
    return libyices.yices_arith_geq_atom(t1, t2)

# term_t yices_arith_leq_atom(term_t t1, term_t t2)  // t1 <= t2
libyices.yices_arith_leq_atom.restype = term_t
libyices.yices_arith_leq_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_arith_leq_atom(t1, t2):
    """Creates the term (t1 <= t2), or NULL_TERM if there's an error (NULL_TERM = -1).

    Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not an arithmetic term
       code = ARITHTERM_REQUIRED
       term1 = t1 or t2.
    """
    return libyices.yices_arith_leq_atom(t1, t2)

# term_t yices_arith_gt_atom(term_t t1, term_t t2)   // t1 > t2
libyices.yices_arith_gt_atom.restype = term_t
libyices.yices_arith_gt_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_arith_gt_atom(t1, t2):
    """Creates the term (t1 > t2), or NULL_TERM if there's an error (NULL_TERM = -1).

    Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not an arithmetic term
       code = ARITHTERM_REQUIRED
       term1 = t1 or t2.
    """
    return libyices.yices_arith_gt_atom(t1, t2)

# term_t yices_arith_lt_atom(term_t t1, term_t t2)   // t1 < t2
libyices.yices_arith_lt_atom.restype = term_t
libyices.yices_arith_lt_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_arith_lt_atom(t1, t2):
    """Creates the term (t1 < t2), or NULL_TERM if there's an error (NULL_TERM = -1).

    Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not an arithmetic term
       code = ARITHTERM_REQUIRED
       term1 = t1 or t2.
    """
    return libyices.yices_arith_lt_atom(t1, t2)

# term_t yices_arith_eq0_atom(term_t t)   // t == 0
libyices.yices_arith_eq0_atom.restype = term_t
libyices.yices_arith_eq0_atom.argtypes = [term_t]
@catch_error(-1)
def yices_arith_eq0_atom(t):
    """Creates the term (t == 0), or NULL_TERM if there's an error (NULL_TERM = -1).

     Error report:
     if t is not valid:
       code = INVALID_TERM
       term1 = t
     if t is not an arithmetic term
       code = ARITH_TERM_REQUIRED
       term1 = t
    """
    return libyices.yices_arith_eq0_atom(t)

# term_t yices_arith_neq0_atom(term_t t)  // t != 0
libyices.yices_arith_neq0_atom.restype = term_t
libyices.yices_arith_neq0_atom.argtypes = [term_t]
@catch_error(-1)
def yices_arith_neq0_atom(t):
    """Creates the term (t != 0), or NULL_TERM if there's an error (NULL_TERM = -1).

     Error report:
     if t is not valid:
       code = INVALID_TERM
       term1 = t
     if t is not an arithmetic term
       code = ARITH_TERM_REQUIRED
       term1 = t
    """
    return libyices.yices_arith_neq0_atom(t)

# term_t yices_arith_geq0_atom(term_t t)  // t >= 0
libyices.yices_arith_geq0_atom.restype = term_t
libyices.yices_arith_geq0_atom.argtypes = [term_t]
@catch_error(-1)
def yices_arith_geq0_atom(t):
    """Creates the term (t >= 0), or NULL_TERM if there's an error (NULL_TERM = -1).

     Error report:
     if t is not valid:
       code = INVALID_TERM
       term1 = t
     if t is not an arithmetic term
       code = ARITH_TERM_REQUIRED
       term1 = t
    """
    return libyices.yices_arith_geq0_atom(t)

# term_t yices_arith_leq0_atom(term_t t)  // t <= 0
libyices.yices_arith_leq0_atom.restype = term_t
libyices.yices_arith_leq0_atom.argtypes = [term_t]
@catch_error(-1)
def yices_arith_leq0_atom(t):
    """Creates the term (t <= 0), or NULL_TERM if there's an error (NULL_TERM = -1).

     Error report:
     if t is not valid:
       code = INVALID_TERM
       term1 = t
     if t is not an arithmetic term
       code = ARITH_TERM_REQUIRED
       term1 = t
    """
    return libyices.yices_arith_leq0_atom(t)

# term_t yices_arith_gt0_atom(term_t t)   // t > 0
libyices.yices_arith_gt0_atom.restype = term_t
libyices.yices_arith_gt0_atom.argtypes = [term_t]
@catch_error(-1)
def yices_arith_gt0_atom(t):
    """Creates the term (t > 0), or NULL_TERM if there's an error (NULL_TERM = -1).

     Error report:
     if t is not valid:
       code = INVALID_TERM
       term1 = t
     if t is not an arithmetic term
       code = ARITH_TERM_REQUIRED
       term1 = t
    """
    return libyices.yices_arith_gt0_atom(t)

# term_t yices_arith_lt0_atom(term_t t)   // t < 0
libyices.yices_arith_lt0_atom.restype = term_t
libyices.yices_arith_lt0_atom.argtypes = [term_t]
@catch_error(-1)
def yices_arith_lt0_atom(t):
    """Creates the term (t < 0), or NULL_TERM if there's an error (NULL_TERM = -1).

     Error report:
     if t is not valid:
       code = INVALID_TERM
       term1 = t
     if t is not an arithmetic term
       code = ARITH_TERM_REQUIRED
       term1 = t
    """
    return libyices.yices_arith_lt0_atom(t)


###################################
#   BITVECTOR TERM CONSTRUCTORS   #
###################################



# term_t yices_bvconst_uint32(uint32_t n, uint32_t x)
libyices.yices_bvconst_uint32.restype = term_t
libyices.yices_bvconst_uint32.argtypes = [c_uint32, c_uint32]
@catch_error(-1)
def yices_bvconst_uint32(n, x):
    """Conversion of an integer to a bitvector constant, returns NULL_TERM (-1) if there's an error.

    bvconst_uint32(n, x):
     - n = number of bits
     - x = value
     The low-order bit of x is bit 0 of the constant.

     - if n is less than 32, then the value of x is truncated to
       n bits (i.e., only the n least significant bits of x are considered)
     - if n is more than 32, then the value of x is zero-extended to
       n bits.

     Error report:
     if n = 0
        code = POS_INT_REQUIRED
        badval = n
     if n > YICES_MAX_BVSIZE
        code = MAX_BVSIZE_EXCEEDED
        badval = n.
    """
    return libyices.yices_bvconst_uint32(n, x)

# term_t yices_bvconst_uint64(uint32_t n, uint64_t x)
libyices.yices_bvconst_uint64.restype = term_t
libyices.yices_bvconst_uint64.argtypes = [c_uint32, c_uint64]
@catch_error(-1)
def yices_bvconst_uint64(n, x):
    """Conversion of an integer to a bitvector constant, returns NULL_TERM (-1) if there's an error.

    bvconst_uint64(n, x):
     - n = number of bits
     - x = value
     The low-order bit of x is bit 0 of the constant.
     - if n is less than 64, then the value of x is truncated to
       n bits (i.e., only the n least significant bits of x are considered)
     - if n is more than 64, then the value of x is zero-extended to
       n bits.

     Error report:
     if n = 0
        code = POS_INT_REQUIRED
        badval = n
     if n > YICES_MAX_BVSIZE
        code = MAX_BVSIZE_EXCEEDED
        badval = n.
    """
    return libyices.yices_bvconst_uint64(n, x)

# term_t yices_bvconst_int32(uint32_t n, int32_t x)
libyices.yices_bvconst_int32.restype = term_t
libyices.yices_bvconst_int32.argtypes = [c_uint32, c_int32]
@catch_error(-1)
def yices_bvconst_int32(n, x):
    """Conversion of an integer to a bitvector constant, returns NULL_TERM (-1) if there's an error.

    bvconst_int32(n, x):
     - n = number of bits
     - x = value
     The low-order bit of x is bit 0 of the constant.
     - if n is less than 32, then the value of x is truncated to
       n bits (i.e., only the n least significant bits of x are considered)
     - if n is more than 32, then the value of x is sign-extended to
       n bits.

     Error report:
     if n = 0
        code = POS_INT_REQUIRED
        badval = n
     if n > YICES_MAX_BVSIZE
        code = MAX_BVSIZE_EXCEEDED
        badval = n.
    """
    return libyices.yices_bvconst_int32(n, x)

# term_t yices_bvconst_int64(uint32_t n, int64_t x)
libyices.yices_bvconst_int64.restype = term_t
libyices.yices_bvconst_int64.argtypes = [c_uint32, c_int64]
@catch_error(-1)
def yices_bvconst_int64(n, x):
    """Conversion of an integer to a bitvector constant, returns NULL_TERM (-1) if there's an error.

    bvconst_int64(n, x):
     - n = number of bits
     - x = value
     The low-order bit of x is bit 0 of the constant.
     - if n is less than 64, then the value of x is truncated to
       n bits (i.e., only the n least significant bits of x are considered)
     - if n is more than 64, then the value of x is sign-extended to
       n bits.

     Error report:
     if n = 0
        code = POS_INT_REQUIRED
        badval = n
     if n > YICES_MAX_BVSIZE
        code = MAX_BVSIZE_EXCEEDED
        badval = n.
    """
    return libyices.yices_bvconst_int64(n, x)

# term_t yices_bvconst_mpz(uint32_t n, const mpz_t x)
libyices.yices_bvconst_mpz.restype = term_t
libyices.yices_bvconst_mpz.argtypes = [c_uint32, mpz_t]
@catch_error(-1)
def yices_bvconst_mpz(n, x):
    """Conversion of an integer to a bitvector constant, returns NULL_TERM (-1) if there's an error.

    bvconst_mpz(n, x):
     - n = number of bits
     - x = value
     The low-order bit of x is bit 0 of the constant.
     - x is interpreted as a signed number in 2-s complement
     - if x has fewer than n bits (in 2's complement), then the value is sign-extended
     - if x has more than n bits (in 2's complement) then the value is truncated
       (to n least significant bits).

     Error report:
     if n = 0
        code = POS_INT_REQUIRED
        badval = n
     if n > YICES_MAX_BVSIZE
        code = MAX_BVSIZE_EXCEEDED
        badval = n.
    """
    return libyices.yices_bvconst_mpz(n, x)


# term_t yices_bvconst_zero(uint32_t n)
libyices.yices_bvconst_zero.restype = term_t
libyices.yices_bvconst_zero.argtypes = [c_uint32]
@catch_error(-1)
def yices_bvconst_zero(n):
    """Set all bits to 0.

     Error report:
     if n = 0
        code = POS_INT_REQUIRED
        badval = n
     if n > YICES_MAX_BVSIZE
        code = MAX_BVSIZE_EXCEEDED
        badval = n.
    """
    return libyices.yices_bvconst_zero(n)

# term_t yices_bvconst_one(uint32_t n)
libyices.yices_bvconst_one.restype = term_t
libyices.yices_bvconst_one.argtypes = [c_uint32]
@catch_error(-1)
def yices_bvconst_one(n):
    """Set low-order bit to 1, all the other bits to 0.

     Error report:
     if n = 0
        code = POS_INT_REQUIRED
        badval = n
     if n > YICES_MAX_BVSIZE
        code = MAX_BVSIZE_EXCEEDED
        badval = n.
    """
    return libyices.yices_bvconst_one(n)

# term_t yices_bvconst_minus_one(uint32_t n)
libyices.yices_bvconst_minus_one.restype = term_t
libyices.yices_bvconst_minus_one.argtypes = [c_uint32]
@catch_error(-1)
def yices_bvconst_minus_one(n):
    """Set all bits to 1.

     Error report:
     if n = 0
        code = POS_INT_REQUIRED
        badval = n
     if n > YICES_MAX_BVSIZE
        code = MAX_BVSIZE_EXCEEDED
        badval = n.
    """
    return libyices.yices_bvconst_minus_one(n)

# term_t yices_bvconst_from_array(uint32_t n, const int32_t a[])
libyices.yices_bvconst_from_array.restype = term_t
libyices.yices_bvconst_from_array.argtypes = [c_uint32, POINTER(c_int32)]
@catch_error(-1)
def yices_bvconst_from_array(n, a):
    """Construction from an integer array.

    bvconst_from_array(n, a):
     bit i of the constant is 0 if a[i] == 0
     bit i of the constant is 1 if a[i] != 0

     Error report:
     if n = 0
        code = POS_INT_REQUIRED
        badval = n
     if n > YICES_MAX_BVSIZE
        code = MAX_BVSIZE_EXCEEDED
        badval = n.
    """
    return libyices.yices_bvconst_from_array(n, a)

# term_t yices_parse_bvbin(const char *s)
libyices.yices_parse_bvbin.restype = term_t
libyices.yices_parse_bvbin.argtypes = [c_char_p]
@catch_error(-1)
def yices_parse_bvbin(s):
    """Constructs a bitvector by parsing from a string of characters '0' and '1'.

    parse_bvbin(s):
     First character = high-order bit
     Last character = low-order bit
     The constant has n bits if the strings has n characters.

     Error report:
     if the format is incorrect:
       code = INVALID_BVBIN_FORMAT
     if the string has more than YICES_MAX_BVSIZE digits
       code = MAX_BVSIZE_EXCEEDED
       badval = n.
    """
    return libyices.yices_parse_bvbin(s)

# term_t yices_parse_bvhex(const char *s)
libyices.yices_parse_bvhex.restype = term_t
libyices.yices_parse_bvhex.argtypes = [c_char_p]
@catch_error(-1)
def yices_parse_bvhex(s):
    """Constructs a bitvector by parsing from a hexadecimal string.

    parse_bvhex(s):
     All characters must be '0' to '9' or 'a' to 'f' or 'A' to 'F'
     - First character = 4 high-order bits
     - Last character = 4 low-order bits
     The constant has 4n bits if s has n characters.

     Error report:
     if the format is incorrect:
       code = INVALID_BVHEX_FORMAT
     if the result would have more than YICES_MAX_BVSIZE digits
       code = MAX_BVSIZE_EXCEEDED
       badval = 4n.
    """
    return libyices.yices_parse_bvhex(s)

#
# BIT-VECTOR ARITHMETIC
#


# term_t yices_bvadd(term_t t1, term_t t2)     // addition (t1 + t2)
libyices.yices_bvadd.restype = term_t
libyices.yices_bvadd.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvadd(t1, t2):
    """Constructs the bitvector term (t1 + t2), returning return NULL_TERM (-1) if there's an error.

    bvadd(t1, t2):
    Both arguments must be bitvector terms of the same size.

     Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1 or t2
     if t1 and t2 do not have the same bitvector type
       code = INCOMPATIBLE_TYPES
       term1 = t1
       type1 = type of t1
       term2 = t2
       type2 = type of t2.
    """
    return libyices.yices_bvadd(t1, t2)

# term_t yices_bvsub(term_t t1, term_t t2)     // subtraction (t1 - t2)
libyices.yices_bvsub.restype = term_t
libyices.yices_bvsub.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvsub(t1, t2):
    """Constructs the bitvector term (t1 - t2), returning return NULL_TERM (-1) if there's an error.

    bvsub(t1, t2):
    Both arguments must be bitvector terms of the same size.

     Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1 or t2
     if t1 and t2 do not have the same bitvector type
       code = INCOMPATIBLE_TYPES
       term1 = t1
       type1 = type of t1
       term2 = t2
       type2 = type of t2.
    """
    return libyices.yices_bvsub(t1, t2)

# term_t yices_bvneg(term_t t1)                // negation (- t1)
libyices.yices_bvneg.restype = term_t
libyices.yices_bvneg.argtypes = [term_t]
@catch_error(-1)
def yices_bvneg(t1):
    """Constructs the bitvector term (- t1), returning return NULL_TERM (-1) if there's an error.

    bvneg(t1):
     Error reports
     if t1 is not valid
       code = INVALID_TERM
       term1 = t1
     if t1 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1.
    """
    return libyices.yices_bvneg(t1)

# term_t yices_bvmul(term_t t1, term_t t2)     // multiplication (t1 * t2)
libyices.yices_bvmul.restype = term_t
libyices.yices_bvmul.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvmul(t1, t2):
    """Constructs the bitvector term (t1 * t2), returning return NULL_TERM (-1) if there's an error.

    bvmul(t1, t2):
    Both arguments must be bitvector terms of the same size.

     Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1 or t2
     if t1 and t2 do not have the same bitvector type
       code = INCOMPATIBLE_TYPES
       term1 = t1
       type1 = type of t1
       term2 = t2
       type2 = type of t2.

     If the degree is too large
       code = DEGREE_OVERFLOW.
    """
    return libyices.yices_bvmul(t1, t2)

# term_t yices_bvsquare(term_t t1)             // square (t1 * t1)
libyices.yices_bvsquare.restype = term_t
libyices.yices_bvsquare.argtypes = [term_t]
@catch_error(-1)
def yices_bvsquare(t1):
    """Constructs the bitvector term (t1 * t1), returning return NULL_TERM (-1) if there's an error.

    bvsquare(t1):
    The argument must be a bitvector term.

     Error reports
     Error reports
     if t1 is not valid
       code = INVALID_TERM
       term1 = t1
     if t1 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1.

     if the degree is too large
       code = DEGREE_OVERFLOW.
    """
    return libyices.yices_bvsquare(t1)

# term_t yices_bvpower(term_t t1, uint32_t d)  // exponentiation (t1 ^ d)
libyices.yices_bvpower.restype = term_t
libyices.yices_bvpower.argtypes = [term_t, c_uint32]
@catch_error(-1)
def yices_bvpower(t1, d):
    """Constructs the bitvector term (t1 ^ d), returning return NULL_TERM (-1) if there's an error.

    bvpower(t1, d):
    t1 must be a bitvector term.

    Error reports
    if t1 is not valid
      code = INVALID_TERM
      term1 = t1 or t2
    if t1 is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t1
    if the degree is too large
       code = DEGREE_OVERFLOW.
    """
    return libyices.yices_bvpower(t1, d)

# term_t yices_bvdiv(term_t t1, term_t t2)   // unsigned div
libyices.yices_bvdiv.restype = term_t
libyices.yices_bvdiv.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvdiv(t1, t2):
    """Constructs the unsigned division bitvector term, returning return NULL_TERM (-1) if there's an error.

    bvdiv(t1, t2):
    Both arguments must be bitvector terms of the same size.

     Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1 or t2
     if t1 and t2 do not have the same bitvector type
       code = INCOMPATIBLE_TYPES
       term1 = t1
       type1 = type of t1
       term2 = t2
       type2 = type of t2

     In case of division by 0, Yices uses the following conventions:

       (bvdiv  x 0b00...0) is the  largest unsigned integer that can be represented using n bits
                           (i.e., 0b111....1)

       (bvrem  x 0b00...0) is x

       (bvsdiv x 0b00...0) is   0b00..01 (i.e., +1) if x's sign bit is 1
                           and  0b111111 (i.e., -1) if x's sign bit is 0

       (bvsrem x 0b00...0) is x

       (bvsmod x 0b00...0) is x.
    """
    return libyices.yices_bvdiv(t1, t2)

# term_t yices_bvrem(term_t t1, term_t t2)   // unsigned rem
libyices.yices_bvrem.restype = term_t
libyices.yices_bvrem.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvrem(t1, t2):
    """Constructs the unsigned remainder bitvector term, returning return NULL_TERM (-1) if there's an error.

    bvrem(t1, t2:
    Both arguments must be bitvector terms of the same size.

     Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1 or t2
     if t1 and t2 do not have the same bitvector type
       code = INCOMPATIBLE_TYPES
       term1 = t1
       type1 = type of t1
       term2 = t2
       type2 = type of t2

     In case of division by 0, Yices uses the following conventions:

       (bvdiv  x 0b00...0) is the  largest unsigned integer that can be represented using n bits
                           (i.e., 0b111....1)

       (bvrem  x 0b00...0) is x

       (bvsdiv x 0b00...0) is   0b00..01 (i.e., +1) if x's sign bit is 1
                           and  0b111111 (i.e., -1) if x's sign bit is 0

       (bvsrem x 0b00...0) is x

       (bvsmod x 0b00...0) is x.
    """
    return libyices.yices_bvrem(t1, t2)

# term_t yices_bvsdiv(term_t t1, term_t t2)  // signed div
libyices.yices_bvsdiv.restype = term_t
libyices.yices_bvsdiv.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvsdiv(t1, t2):
    """Constructs the signed division bitvector term (), returning return NULL_TERM (-1) if there's an error.

    bvsdiv(t1, t2):
    Both arguments must be bitvector terms of the same size.

     Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1 or t2
     if t1 and t2 do not have the same bitvector type
       code = INCOMPATIBLE_TYPES
       term1 = t1
       type1 = type of t1
       term2 = t2
       type2 = type of t2

     In case of division by 0, Yices uses the following conventions:

       (bvdiv  x 0b00...0) is the  largest unsigned integer that can be represented using n bits
                           (i.e., 0b111....1)

       (bvrem  x 0b00...0) is x

       (bvsdiv x 0b00...0) is   0b00..01 (i.e., +1) if x's sign bit is 1
                           and  0b111111 (i.e., -1) if x's sign bit is 0

       (bvsrem x 0b00...0) is x

       (bvsmod x 0b00...0) is x.
    """
    return libyices.yices_bvsdiv(t1, t2)

# term_t yices_bvsrem(term_t t1, term_t t2)  // signed rem
libyices.yices_bvsrem.restype = term_t
libyices.yices_bvsrem.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvsrem(t1, t2):
    """Constructs the signed remainder bitvector term, returning return NULL_TERM (-1) if there's an error.

    bvsrem(t1, t2):
    Both arguments must be bitvector terms of the same size.

     Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1 or t2
     if t1 and t2 do not have the same bitvector type
       code = INCOMPATIBLE_TYPES
       term1 = t1
       type1 = type of t1
       term2 = t2
       type2 = type of t2

     In case of division by 0, Yices uses the following conventions:

       (bvdiv  x 0b00...0) is the  largest unsigned integer that can be represented using n bits
                           (i.e., 0b111....1)

       (bvrem  x 0b00...0) is x

       (bvsdiv x 0b00...0) is   0b00..01 (i.e., +1) if x's sign bit is 1
                           and  0b111111 (i.e., -1) if x's sign bit is 0

       (bvsrem x 0b00...0) is x

       (bvsmod x 0b00...0) is x.
    """
    return libyices.yices_bvsrem(t1, t2)

# term_t yices_bvsmod(term_t t1, term_t t2)  // signed mod
libyices.yices_bvsmod.restype = term_t
libyices.yices_bvsmod.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvsmod(t1, t2):
    """Constructs the signed modulus bitvector term (), returning return NULL_TERM (-1) if there's an error.

    bvsmod(t1, t2):
    Both arguments must be bitvector terms of the same size.

     Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1 or t2
     if t1 and t2 do not have the same bitvector type
       code = INCOMPATIBLE_TYPES
       term1 = t1
       type1 = type of t1
       term2 = t2
       type2 = type of t2

     In case of division by 0, Yices uses the following conventions:

       (bvdiv  x 0b00...0) is the  largest unsigned integer that can be represented using n bits
                           (i.e., 0b111....1)

       (bvrem  x 0b00...0) is x

       (bvsdiv x 0b00...0) is   0b00..01 (i.e., +1) if x's sign bit is 1
                           and  0b111111 (i.e., -1) if x's sign bit is 0

       (bvsrem x 0b00...0) is x

       (bvsmod x 0b00...0) is x.
    """
    return libyices.yices_bvsmod(t1, t2)

# term_t yices_bvnot(term_t t1)              // bitwise not
libyices.yices_bvnot.restype = term_t
libyices.yices_bvnot.argtypes = [term_t]
@catch_error(-1)
def yices_bvnot(t1):
    """Constructs the bitwise not bitvector term, returning return NULL_TERM (-1) if there's an error.

    bvnot(t1):
    The argument must be a bitvector term.

     Error reports
     Error reports
     if t1 is not valid
       code = INVALID_TERM
       term1 = t1
     if t1 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1.
    """
    return libyices.yices_bvnot(t1)

# term_t yices_bvnand(term_t t1, term_t t2)  // bitwise not and
libyices.yices_bvnand.restype = term_t
libyices.yices_bvnand.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvnand(t1, t2):
    """Constructs the bitwise not and bitvector term, returning return NULL_TERM (-1) if there's an error.

    bvnand(t1, t2):
    Both arguments must be bitvector terms of the same size.

     Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1 or t2
     if t1 and t2 do not have the same bitvector type
       code = INCOMPATIBLE_TYPES
       term1 = t1
       type1 = type of t1
       term2 = t2
       type2 = type of t2.
    """
    return libyices.yices_bvnand(t1, t2)

# term_t yices_bvnor(term_t t1, term_t t2)   // bitwise not or
libyices.yices_bvnor.restype = term_t
libyices.yices_bvnor.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvnor(t1, t2):
    """Constructs the  bitwise not or bitvector term, returning return NULL_TERM (-1) if there's an error.

    bvnor(t1, t2):
    Both arguments must be bitvector terms of the same size.

     Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1 or t2
     if t1 and t2 do not have the same bitvector type
       code = INCOMPATIBLE_TYPES
       term1 = t1
       type1 = type of t1
       term2 = t2
       type2 = type of t2.
    """
    return libyices.yices_bvnor(t1, t2)

# term_t yices_bvxnor(term_t t1, term_t t2)  // bitwise not xor
libyices.yices_bvxnor.restype = term_t
libyices.yices_bvxnor.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvxnor(t1, t2):
    """Constructs the bitwise not xor bitvector term, returning return NULL_TERM (-1) if there's an error.

    bvxnor(t1, t2):
    Both arguments must be bitvector terms of the same size.

     Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1 or t2
     if t1 and t2 do not have the same bitvector type
       code = INCOMPATIBLE_TYPES
       term1 = t1
       type1 = type of t1
       term2 = t2
       type2 = type of t2.
    """
    return libyices.yices_bvxnor(t1, t2)

# term_t yices_bvshl(term_t t1, term_t t2)   // shift t1 left by k bits where k = value of t2
libyices.yices_bvshl.restype = term_t
libyices.yices_bvshl.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvshl(t1, t2):
    """Constructs the shift t1 left by k bits where k = value of t2, returning return NULL_TERM (-1) if there's an error.

    bvshl(t1, t2):
    Both arguments must be bitvector terms of the same size.

     Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1 or t2
     if t1 and t2 do not have the same bitvector type
       code = INCOMPATIBLE_TYPES
       term1 = t1
       type1 = type of t1
       term2 = t2
       type2 = type of t2.
    """
    return libyices.yices_bvshl(t1, t2)

# term_t yices_bvlshr(term_t t1, term_t t2)  // logical shift t1 right by k bits, where k = value of t2
libyices.yices_bvlshr.restype = term_t
libyices.yices_bvlshr.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvlshr(t1, t2):
    """Constructs the logical shift t1 right by k bits, where k = value of t2, returning return NULL_TERM (-1) if there's an error.

    bvlshr(t1, t2):
    Both arguments must be bitvector terms of the same size.

     Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1 or t2
     if t1 and t2 do not have the same bitvector type
       code = INCOMPATIBLE_TYPES
       term1 = t1
       type1 = type of t1
       term2 = t2
       type2 = type of t2.
    """
    return libyices.yices_bvlshr(t1, t2)

# term_t yices_bvashr(term_t t1, term_t t2)  // arithmetic shift t1 right by k bits, k = value of t2
libyices.yices_bvashr.restype = term_t
libyices.yices_bvashr.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvashr(t1, t2):
    """Constructs the arithmetic shift t1 right by k bits, k = value of t2, returning return NULL_TERM (-1) if there's an error.

    bvashr(t1, t2):
    Both arguments must be bitvector terms of the same size.

     Error reports
     if t1 or t2 is not valid
       code = INVALID_TERM
       term1 = t1 or t2
     if t1 or t2 is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t1 or t2
     if t1 and t2 do not have the same bitvector type
       code = INCOMPATIBLE_TYPES
       term1 = t1
       type1 = type of t1
       term2 = t2
       type2 = type of t2.
    """
    return libyices.yices_bvashr(t1, t2)


# term_t yices_bvand(uint32_t n, const term_t t[])
libyices.yices_bvand.restype = term_t
libyices.yices_bvand.argtypes = [c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_bvand(n, t):
    """Constructs the bitwise and bitvector and/or/xor, returning the  NULL_TERM if there's an error.

     The general form takes an array t[0 ...n-1] as argument (n must be positive).
     - all t[i]s must be bitvector term of the same type (i.e., the same number of bits).
     - special forms are provided for convenience for n=2 and 3.

     Error reports:
     if n == 0
        code = POS_INT_REQUIRED
        badval = n
     if t[i] is not valid
        code = INVALID_TERM
        term1 = t[i]
     if t[i] is not a bitvector term
        code = BITVECTOR_REQUIRED
        badval = n
     if t[0] and t[i] don't have the same bitvector type
        code = INCOMPATIBLE_TYPES
        term1 = t[0]
        type1 = type of t[0]
        term2 = t[i]
        type2 = type of t[i].
    """
    return libyices.yices_bvand(n, t)

# term_t yices_bvor(uint32_t n, const term_t t[])
libyices.yices_bvor.restype = term_t
libyices.yices_bvor.argtypes = [c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_bvor(n, t):
    """Constructs the bitvector or, returning the  NULL_TERM if there's an error.

     The general form takes an array t[0 ...n-1] as argument (n must be positive).
     - all t[i]s must be bitvector term of the same type (i.e., the same number of bits).
     - special forms are provided for convenience for n=2 and 3.

     Error reports:
     if n == 0
        code = POS_INT_REQUIRED
        badval = n
     if t[i] is not valid
        code = INVALID_TERM
        term1 = t[i]
     if t[i] is not a bitvector term
        code = BITVECTOR_REQUIRED
        badval = n
     if t[0] and t[i] don't have the same bitvector type
        code = INCOMPATIBLE_TYPES
        term1 = t[0]
        type1 = type of t[0]
        term2 = t[i]
        type2 = type of t[i].
    """
    return libyices.yices_bvor(n, t)

# term_t yices_bvxor(uint32_t n, const term_t t[])
libyices.yices_bvxor.restype = term_t
libyices.yices_bvxor.argtypes = [c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_bvxor(n, t):
    """Constructs the bitvector xor, returning the  NULL_TERM if there's an error.

     The general form takes an array t[0 ...n-1] as argument (n must be positive).
     - all t[i]s must be bitvector term of the same type (i.e., the same number of bits).
     - special forms are provided for convenience for n=2 and 3.

     Error reports:
     if n == 0
        code = POS_INT_REQUIRED
        badval = n
     if t[i] is not valid
        code = INVALID_TERM
        term1 = t[i]
     if t[i] is not a bitvector term
        code = BITVECTOR_REQUIRED
        badval = n
     if t[0] and t[i] don't have the same bitvector type
        code = INCOMPATIBLE_TYPES
        term1 = t[0]
        type1 = type of t[0]
        term2 = t[i]
        type2 = type of t[i].
    """
    return libyices.yices_bvxor(n, t)

# term_t yices_bvand2(term_t t1, term_t t2)
libyices.yices_bvand2.restype = term_t
libyices.yices_bvand2.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvand2(t1, t2):
    """Constructs the bitvector and, returning the  NULL_TERM if there's an error.

    bvand2(t1, t2):
     - t1 and t2 must be bitvector terms of the same type (i.e., the same number of bits).

     Error reports:
     if n == 0
        code = POS_INT_REQUIRED
        badval = n
     if t[i] is not valid
        code = INVALID_TERM
        term1 = t[i]
     if t[i] is not a bitvector term
        code = BITVECTOR_REQUIRED
        badval = n
     if t[0] and t[i] don't have the same bitvector type
        code = INCOMPATIBLE_TYPES
        term1 = t[0]
        type1 = type of t[0]
        term2 = t[i]
        type2 = type of t[i].
    """
    return libyices.yices_bvand2(t1, t2)

# term_t yices_bvor2(term_t t1, term_t t2)
libyices.yices_bvor2.restype = term_t
libyices.yices_bvor2.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvor2(t1, t2):
    """Constructs the bitvector or, returning the  NULL_TERM if there's an error.

    bvor2(t1, t2):
     - t1 and t2 must be bitvector terms of the same type (i.e., the same number of bits).

     Error reports:
     if n == 0
        code = POS_INT_REQUIRED
        badval = n
     if t[i] is not valid
        code = INVALID_TERM
        term1 = t[i]
     if t[i] is not a bitvector term
        code = BITVECTOR_REQUIRED
        badval = n
     if t[0] and t[i] don't have the same bitvector type
        code = INCOMPATIBLE_TYPES
        term1 = t[0]
        type1 = type of t[0]
        term2 = t[i]
        type2 = type of t[i].
    """
    return libyices.yices_bvor2(t1, t2)

# term_t yices_bvxor2(term_t t1, term_t t2)
libyices.yices_bvxor2.restype = term_t
libyices.yices_bvxor2.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvxor2(t1, t2):
    """Constructs the bitvector and/or/xor, returning the  NULL_TERM if there's an error.

     bvxor2(t1, t2):
     - t1 and t2 must be bitvector terms of the same type (i.e., the same number of bits).

     Error reports:
     if n == 0
        code = POS_INT_REQUIRED
        badval = n
     if t[i] is not valid
        code = INVALID_TERM
        term1 = t[i]
     if t[i] is not a bitvector term
        code = BITVECTOR_REQUIRED
        badval = n
     if t[0] and t[i] don't have the same bitvector type
        code = INCOMPATIBLE_TYPES
        term1 = t[0]
        type1 = type of t[0]
        term2 = t[i]
        type2 = type of t[i].
    """
    return libyices.yices_bvxor2(t1, t2)

# term_t yices_bvand3(term_t t1, term_t t2, term_t t3)
libyices.yices_bvand3.restype = term_t
libyices.yices_bvand3.argtypes = [term_t, term_t, term_t]
@catch_error(-1)
def yices_bvand3(t1, t2, t3):
    """Constructs the bitvector and, returning the  NULL_TERM if there's an error.

     bvand3(t1, t2, t3):
     - t1, t2, t3 must be bitvector terms of the same type (i.e., the same number of bits).

     Error reports:
     if n == 0
        code = POS_INT_REQUIRED
        badval = n
     if t[i] is not valid
        code = INVALID_TERM
        term1 = t[i]
     if t[i] is not a bitvector term
        code = BITVECTOR_REQUIRED
        badval = n
     if t[0] and t[i] don't have the same bitvector type
        code = INCOMPATIBLE_TYPES
        term1 = t[0]
        type1 = type of t[0]
        term2 = t[i]
        type2 = type of t[i].
    """
    return libyices.yices_bvand3(t1, t2, t3)

# term_t yices_bvor3(term_t t1, term_t t2, term_t t3)
libyices.yices_bvor3.restype = term_t
libyices.yices_bvor3.argtypes = [term_t, term_t, term_t]
@catch_error(-1)
def yices_bvor3(t1, t2, t3):
    """Constructs the bitvector or, returning the  NULL_TERM if there's an error.

     bvor3(t1, t2, t3):
     - t1, t2, t3 must be bitvector terms of the same type (i.e., the same number of bits).

     Error reports:
     if n == 0
        code = POS_INT_REQUIRED
        badval = n
     if t[i] is not valid
        code = INVALID_TERM
        term1 = t[i]
     if t[i] is not a bitvector term
        code = BITVECTOR_REQUIRED
        badval = n
     if t[0] and t[i] don't have the same bitvector type
        code = INCOMPATIBLE_TYPES
        term1 = t[0]
        type1 = type of t[0]
        term2 = t[i]
        type2 = type of t[i].
    """
    return libyices.yices_bvor3(t1, t2, t3)

# term_t yices_bvxor3(term_t t1, term_t t2, term_t t3)
libyices.yices_bvxor3.restype = term_t
libyices.yices_bvxor3.argtypes = [term_t, term_t, term_t]
@catch_error(-1)
def yices_bvxor3(t1, t2, t3):
    """Constructs the bitvector xor, returning the  NULL_TERM if there's an error.

     bvxor3(t1, t2, t3):
     - t1, t2, t3 must be bitvector terms of the same type (i.e., the same number of bits).

     Error reports:
     if n == 0
        code = POS_INT_REQUIRED
        badval = n
     if t[i] is not valid
        code = INVALID_TERM
        term1 = t[i]
     if t[i] is not a bitvector term
        code = BITVECTOR_REQUIRED
        badval = n
     if t[0] and t[i] don't have the same bitvector type
        code = INCOMPATIBLE_TYPES
        term1 = t[0]
        type1 = type of t[0]
        term2 = t[i]
        type2 = type of t[i].
    """
    return libyices.yices_bvxor3(t1, t2, t3)

# term_t yices_bvsum(uint32_t n, const term_t t[])
libyices.yices_bvsum.restype = term_t
libyices.yices_bvsum.argtypes = [c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_bvsum(n, t):
    """Returns the sum of an array on bitvectors, or the NULL_TERM if there's an error.

    bvsum(n, t):
    Sum of n bitvector terms t[0] ... t[n-1]
    - n must be positive
    - all t[i]s must be bitvector terms of the same type (same number of bits)

    Error reports:
    if n == 0
       code = POS_INT_REQUIRED
       badval = n
    if t[i] is not valid
       code = INVALID_TERM
       term1 = t[i]
    if t[i] is not a bitvector term
       code = BITVECTOR_REQUIRED
       badval = n
    if t[0] and t[i] don't have the same bitvector type
       code = INCOMPATIBLE_TYPES
       term1 = t[0]
       type1 = type of t[0]
       term2 = t[i]
       type2 = type of t[i]
    """
    return libyices.yices_bvsum(n, t)

# term_t yices_bvproduct(uint32_t n, const term_t t[])
libyices.yices_bvproduct.restype = term_t
libyices.yices_bvproduct.argtypes = [c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_bvproduct(n, t):
    """Returns the product of an array on bitvectors, or the NULL_TERM if there's an error.

    bvproduct(n, t):
    Product of n bitvector terms t[0] ... t[n-1]
    - n must be positive
    - all t[i]s must be bitvector terms of the same type (same number of bits)

    Error reports:
    if n == 0
       code = POS_INT_REQUIRED
       badval = n
    if t[i] is not valid
       code = INVALID_TERM
       term1 = t[i]
    if t[i] is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t[i]
    if t[0] and t[i] don't have the same bitvector type
       code = INCOMPATIBLE_TYPES
       term1 = t[0]
       type1 = type of t[0]
       term2 = t[i]
       type2 = type of t[i]
    if the result has degree > YICES_MAX_DEGREE
       code = DEGREE_OVERFLOW
       badval = degree
    """
    return libyices.yices_bvproduct(n, t)

# term_t yices_shift_left0(term_t t, uint32_t n)
libyices.yices_shift_left0.restype = term_t
libyices.yices_shift_left0.argtypes = [term_t, c_uint32]
@catch_error(-1)
def yices_shift_left0(t, n):
    """Shift left by an integer constant n, return NULL_TERM (-1) if there's an error.

    shift_left0(t, n):
    - shift_left0 sets the low-order bits to zero

    If t is a vector of m bits, then n must satisfy 0 <= n <= m.

    Error reports:
    if t is not valid
      code = INVALID_TERM
      term1 = t
    if t is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t
    if n > size of t
      code = INVALID_BITSHIFT
      badval = n
    """
    return libyices.yices_shift_left0(t, n)

# term_t yices_shift_left1(term_t t, uint32_t n)
libyices.yices_shift_left1.restype = term_t
libyices.yices_shift_left1.argtypes = [term_t, c_uint32]
@catch_error(-1)
def yices_shift_left1(t, n):
    """Shift left by an integer constant n, return NULL_TERM (-1) if there's an error.

    shift_left1(t, n):
    - shift_left1 sets the low-order bits to one

    If t is a vector of m bits, then n must satisfy 0 <= n <= m.

    Error reports:
    if t is not valid
      code = INVALID_TERM
      term1 = t
    if t is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t
    if n > size of t
      code = INVALID_BITSHIFT
      badval = n
    """
    return libyices.yices_shift_left1(t, n)

# term_t yices_shift_right0(term_t t, uint32_t n)
libyices.yices_shift_right0.restype = term_t
libyices.yices_shift_right0.argtypes = [term_t, c_uint32]
@catch_error(-1)
def yices_shift_right0(t, n):
    """Shift right by an integer constant n, return NULL_TERM (-1) if there's an error.

    shift_right0(t, n):
    - shift_right0 sets the high-order bits to zero

    If t is a vector of m bits, then n must satisfy 0 <= n <= m.

    Error reports:
    if t is not valid
      code = INVALID_TERM
      term1 = t
    if t is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t
    if n > size of t
      code = INVALID_BITSHIFT
      badval = n
    """
    return libyices.yices_shift_right0(t, n)

# term_t yices_shift_right1(term_t t, uint32_t n)
libyices.yices_shift_right1.restype = term_t
libyices.yices_shift_right1.argtypes = [term_t, c_uint32]
@catch_error(-1)
def yices_shift_right1(t, n):
    """Shift right an integer constant n, return NULL_TERM (-1) if there's an error.

    shift_right1(t, n):
    - shift_right1 sets the high-order bits to one

    If t is a vector of m bits, then n must satisfy 0 <= n <= m.

    Error reports:
    if t is not valid
      code = INVALID_TERM
      term1 = t
    if t is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t
    if n > size of t
      code = INVALID_BITSHIFT
      badval = n
    """
    return libyices.yices_shift_right1(t, n)

# term_t yices_ashift_right(term_t t, uint32_t n)
libyices.yices_ashift_right.restype = term_t
libyices.yices_ashift_right.argtypes = [term_t, c_uint32]
@catch_error(-1)
def yices_ashift_right(t, n):
    """Shift right by an integer constant n, return NULL_TERM (-1) if there's an error.

    ashift_right(t, n):
    - ashift_right is arithmetic shift, it copies the sign bit

    If t is a vector of m bits, then n must satisfy 0 <= n <= m.

    Error reports:
    if t is not valid
      code = INVALID_TERM
      term1 = t
    if t is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t
    if n > size of t
      code = INVALID_BITSHIFT
      badval = n
    """
    return libyices.yices_ashift_right(t, n)

# term_t yices_rotate_left(term_t t, uint32_t n)
libyices.yices_rotate_left.restype = term_t
libyices.yices_rotate_left.argtypes = [term_t, c_uint32]
@catch_error(-1)
def yices_rotate_left(t, n):
    """Rotation by an integer constant n, return NULL_TERM (-1) if there's an error.

    rotate_left(t, n):
    - rotate_left: circular rotation

    If t is a vector of m bits, then n must satisfy 0 <= n <= m.

    Error reports:
    if t is not valid
      code = INVALID_TERM
      term1 = t
    if t is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t
    if n > size of t
      code = INVALID_BITSHIFT
      badval = n
    """
    return libyices.yices_rotate_left(t, n)

# term_t yices_rotate_right(term_t t, uint32_t n)
libyices.yices_rotate_right.restype = term_t
libyices.yices_rotate_right.argtypes = [term_t, c_uint32]
@catch_error(-1)
def yices_rotate_right(t, n):
    """Rotation by an integer constant n, return NULL_TERM (-1) if there's an error.

    rotate_right(t, n):
    - rotate_right: circular rotation

    If t is a vector of m bits, then n must satisfy 0 <= n <= m.

    Error reports:
    if t is not valid
      code = INVALID_TERM
      term1 = t
    if t is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t
    if n > size of t
      code = INVALID_BITSHIFT
      badval = n
    """
    return libyices.yices_rotate_right(t, n)

# term_t yices_bvextract(term_t t, uint32_t i, uint32_t j)
libyices.yices_bvextract.restype = term_t
libyices.yices_bvextract.argtypes = [term_t, c_uint32, c_uint32]
@catch_error(-1)
def yices_bvextract(t, i, j):
    """Extract a subvector of t, return NULL_TERM (-1) if there's an error.

    bvextract(t, i, j):
    - t must be a bitvector term of size m
    - i and j must satisfy i <= j <= m-1
    The result is the bits i to j of t.

    Error reports:
    if t is not valid
      code = INVALID_TERM
      term1 = t
    if t is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t
    if i <= j <= m-1 does not hold.
    """
    return libyices.yices_bvextract(t, i, j)

# term_t yices_bvconcat2(term_t t1, term_t t2)
libyices.yices_bvconcat2.restype = term_t
libyices.yices_bvconcat2.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvconcat2(t1, t2):
    """Concatenation of two bitvector terms, returns NULL_TERM (-1) if there's an error.

    bvconcat2(t1, t2):
    - t1 and t2 must be bitvector terms

    NOTE: t1 is the high-order part of the result, t2 is the low-order part.
    For example, if t1 is 0b0000 and t2 is 0b11111, then the function will
    construct 0b000011111.

    Error reports
    if t1 or t2 is not a valid term
      code = INVALID_TERM
      term1 = t1 or t2
    if t1 or t2 is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t1 or t2
    if the size of the result would be larger than MAX_BVSIZE
      code = MAX_BVSIZE_EXCEEDED
      badval = n1 + n2 (n1 = size of t1, n2 = size of t2).
    """
    return libyices.yices_bvconcat2(t1, t2)

# term_t yices_bvconcat(uint32_t n, const term_t t[])
libyices.yices_bvconcat.restype = term_t
libyices.yices_bvconcat.argtypes = [c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_bvconcat(n, t):
    """General form of concatenation: the input is an array of n bitvector terms.

    bvconcat(n, t):
    - n must be positive.

    NOTE: t[0] is the high-order part of the result, and t[n-1] is the low-order
    part. For example, if n=3, t[0] is 0b000, t[1] is 0b111, and t[2] is 0b01, then
    the function constructs 0b00011101.

    Error reports:
    if n == 0
       code = POS_INT_REQUIRED
       badval = n
    if t[i] is not valid
       code = INVALID_TERM
       term1 = t[i]
    if t[i] is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t[i]
    if the size of the result would be more than YICES_MAX_BVSIZE
       code = MAX_BVSIZE_EXCEEDED
       badval = sum of the size of t[i]s.
    """
    return libyices.yices_bvconcat(n, t)

# term_t yices_bvrepeat(term_t t, uint32_t n)
libyices.yices_bvrepeat.restype = term_t
libyices.yices_bvrepeat.argtypes = [term_t, c_uint32]
@catch_error(-1)
def yices_bvrepeat(t, n):
    """Repeated concatenation.

    bvrepeat(t, n):
    - make n copies of t and concatenate them
    - n must be positive

    Return NULL_TERM (-1) if there's an error

    Error report:
    if t is not valid
      code = INVALID_TERM
      term1 = t
    if t is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t
    if n == 0
      code = POS_INT_REQUIRED
      badval = n
    if n * size of t > MAX_BVSIZE
       code = MAX_BVSIZE_EXCEEDED
       badval = n * size of t.
    """
    return libyices.yices_bvrepeat(t, n)

# term_t yices_sign_extend(term_t t, uint32_t n)
libyices.yices_sign_extend.restype = term_t
libyices.yices_sign_extend.argtypes = [term_t, c_uint32]
@catch_error(-1)
def yices_sign_extend(t, n):
    """Sign extension, return NULL_TERM if there's an error.

    sign_extend(t, n):
    - add n copies of t's sign bit

    Error reports:
    if t is invalid
      code = INVALID_TERM
      term1 = t
    if t is not a bitvector
      code = BITVECTOR_REQUIRED
      term1 = t
    if n + size of t > MAX_BVSIZE
      code = MAX_BVSIZE_EXCEEDED
      badval = n * size of t.
    """
    return libyices.yices_sign_extend(t, n)

# term_t yices_zero_extend(term_t t, uint32_t n)
libyices.yices_zero_extend.restype = term_t
libyices.yices_zero_extend.argtypes = [term_t, c_uint32]
@catch_error(-1)
def yices_zero_extend(t, n):
    """Zero extension, return NULL_TERM if there's an error.

    zero_extend(t, n):
     - add n zeros to t

    Error reports:
    if t is invalid
      code = INVALID_TERM
      term1 = t
    if t is not a bitvector
      code = BITVECTOR_REQUIRED
      term1 = t
    if n + size of t > MAX_BVSIZE
      code = MAX_BVSIZE_EXCEEDED
      badval = n * size of t.
    """
    return libyices.yices_zero_extend(t, n)

# term_t yices_redand(term_t t)
libyices.yices_redand.restype = term_t
libyices.yices_redand.argtypes = [term_t]
@catch_error(-1)
def yices_redand(t):
    """AND-reduction, return NULL_TERM if there's an error.

    redand(t):
    if t is b[m-1] ... b[0], then the result is a bit-vector of 1 bit
    equal to the conjunction of all bits of t (i.e., (and b[0] ... b[m-1])

    Error reports:
    if t is invalid
      code = INVALID_TERM
      term1 = t
    if t is not a bitvector
      code = BITVECTOR_REQUIRED
      term1 = t.
   """
    return libyices.yices_redand(t)

# term_t yices_redor(term_t t)
libyices.yices_redor.restype = term_t
libyices.yices_redor.argtypes = [term_t]
@catch_error(-1)
def yices_redor(t):
    """OR-reduction, return NULL_TERM if there's an error.

    redor(t):
    if t is b[m-1] ... b[0], then the result is a bit-vector of 1 bit
    equal to the disjunction of all bits of t (i.e., (or b[0] ... b[m-1])

    Error reports:
    if t is invalid
      code = INVALID_TERM
      term1 = t
    if t is not a bitvector
      code = BITVECTOR_REQUIRED
      term1 = t.
    """
    return libyices.yices_redor(t)

# term_t yices_redcomp(term_t t1, term_t t2)
libyices.yices_redcomp.restype = term_t
libyices.yices_redcomp.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_redcomp(t1, t2):
    """Bitwise equality comparison: if t1 and t2 are bitvectors of size n, return NULL_TERM if there's an error.

    redcomp(t1, t2):
     construct (bvredand (bvxnor t1 t2))

    Error reports:
    if t1 or t2 is not valid
      code = INVALID_TERM
      term1 = t1 or t2
    if t1 or t2 is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t1 or t2
    if t1 and t2 do not have the same bitvector type
      code = INCOMPATIBLE_TYPES
      term1 = t1
      type1 = type of t1
      term2 = t2
      type2 = type of t2.
    """
    return libyices.yices_redcomp(t1, t2)

# term_t yices_bvarray(uint32_t n, const term_t arg[])
libyices.yices_bvarray.restype = term_t
libyices.yices_bvarray.argtypes = [c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_bvarray(n, arg):
    """Convert an array of boolean terms arg[0 ... n-1] into a bitvector term of n bits.

    bvarray(n, arg):
    - arg[0] = low-order bit of the result
    - arg[n-1] = high-order bit

    Error report:
    if n == 0
       code = POS_INT_REQUIRED
       badval = n
    if n > YICES_MAX_BVSIZE
       code = MAX_BVSIZE_EXCEEDED
       badval = size
    if arg[i] is invalid
       code = INVALID_TERM
       term1 = arg[i]
    if arg[i] is not a boolean
       code = TYPE_MISMATCH
       term1 = arg[i]
       type1 = bool.
    """
    return libyices.yices_bvarray(n, arg)

# term_t yices_bitextract(term_t t, uint32_t i)
libyices.yices_bitextract.restype = term_t
libyices.yices_bitextract.argtypes = [term_t, c_uint32]
@catch_error(-1)
def yices_bitextract(t, i):
    """Extract bit i of vector t (as a boolean).

    bitextract(t, i):
    - if t is a bitvector of n bits, then i must be between 0 and n-1
    - the low-order bit of t has index 0
    - the high-order bit of t has index (n-1)

    Error report:
    if t is invalid
       code = INVALID_TERM
       term1 = t
    if t is not a bitvector term
       code = BITVECTOR_REQUIRED
       term1 = t
    if i >= t's bitsize
       code = INVALID_BITEXTRACT.
    """
    return libyices.yices_bitextract(t, i)


#
# BITVECTOR ATOMS
#

# term_t yices_bveq_atom(term_t t1, term_t t2)   // t1 == t2
libyices.yices_bveq_atom.restype = term_t
libyices.yices_bveq_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bveq_atom(t1, t2):
    """Creates the term asserting (t1 == t2), or returns the NULL_TERM (i.e., a negative index) on error.

    Error reports
    if t1 or t2 is not valid
      code = INVALID_TERM
      term1 = t1 or t2
    if t1 or t2 is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t1 or t2
    if t1 and t2 do not have the same bitvector type
      code = INCOMPATIBLE_TYPES
      term1 = t1
      type1 = type of t1
      term2 = t2
      type2 = type of t2.
    """
    return libyices.yices_bveq_atom(t1, t2)

# term_t yices_bvneq_atom(term_t t1, term_t t2)  // t1 != t2
libyices.yices_bvneq_atom.restype = term_t
libyices.yices_bvneq_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvneq_atom(t1, t2):
    """Creates the term asserting (t1 != t2), or returns the NULL_TERM (i.e., a negative index) on error.

    Error reports
    if t1 or t2 is not valid
      code = INVALID_TERM
      term1 = t1 or t2
    if t1 or t2 is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t1 or t2
    if t1 and t2 do not have the same bitvector type
      code = INCOMPATIBLE_TYPES
      term1 = t1
      type1 = type of t1
      term2 = t2
      type2 = type of t2.
    """
    return libyices.yices_bvneq_atom(t1, t2)

# term_t yices_bvge_atom(term_t t1, term_t t2)  // t1 >= t2
libyices.yices_bvge_atom.restype = term_t
libyices.yices_bvge_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvge_atom(t1, t2):
    """Creates the term asserting (t1 >= t2), or returns the NULL_TERM (i.e., a negative index) on error.

    Error reports
    if t1 or t2 is not valid
      code = INVALID_TERM
      term1 = t1 or t2
    if t1 or t2 is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t1 or t2
    if t1 and t2 do not have the same bitvector type
      code = INCOMPATIBLE_TYPES
      term1 = t1
      type1 = type of t1
      term2 = t2
      type2 = type of t2.
    """
    return libyices.yices_bvge_atom(t1, t2)

# term_t yices_bvgt_atom(term_t t1, term_t t2)  // t1 > t2
libyices.yices_bvgt_atom.restype = term_t
libyices.yices_bvgt_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvgt_atom(t1, t2):
    """Creates the term asserting (t1 > t2), or returns the NULL_TERM (i.e., a negative index) on error.

    Error reports
    if t1 or t2 is not valid
      code = INVALID_TERM
      term1 = t1 or t2
    if t1 or t2 is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t1 or t2
    if t1 and t2 do not have the same bitvector type
      code = INCOMPATIBLE_TYPES
      term1 = t1
      type1 = type of t1
      term2 = t2
      type2 = type of t2.
    """
    return libyices.yices_bvgt_atom(t1, t2)

# term_t yices_bvle_atom(term_t t1, term_t t2)  // t1 <= t2
libyices.yices_bvle_atom.restype = term_t
libyices.yices_bvle_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvle_atom(t1, t2):
    """Creates the term asserting (t1 <= t2), or returns the NULL_TERM (i.e., a negative index) on error.

    Error reports
    if t1 or t2 is not valid
      code = INVALID_TERM
      term1 = t1 or t2
    if t1 or t2 is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t1 or t2
    if t1 and t2 do not have the same bitvector type
      code = INCOMPATIBLE_TYPES
      term1 = t1
      type1 = type of t1
      term2 = t2
      type2 = type of t2.
    """
    return libyices.yices_bvle_atom(t1, t2)

# term_t yices_bvlt_atom(term_t t1, term_t t2)  // t1 < t2
libyices.yices_bvlt_atom.restype = term_t
libyices.yices_bvlt_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvlt_atom(t1, t2):
    """Creates the term asserting (t1 < t2), or returns the NULL_TERM (i.e., a negative index) on error.

    Error reports
    if t1 or t2 is not valid
      code = INVALID_TERM
      term1 = t1 or t2
    if t1 or t2 is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t1 or t2
    if t1 and t2 do not have the same bitvector type
      code = INCOMPATIBLE_TYPES
      term1 = t1
      type1 = type of t1
      term2 = t2
      type2 = type of t2.
    """
    return libyices.yices_bvlt_atom(t1, t2)

# term_t yices_bvsge_atom(term_t t1, term_t t2)  // t1 >= t2
libyices.yices_bvsge_atom.restype = term_t
libyices.yices_bvsge_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvsge_atom(t1, t2):
    """Creates the term asserting (t1 >= t2), or returns the NULL_TERM (i.e., a negative index) on error.

    Error reports
    if t1 or t2 is not valid
      code = INVALID_TERM
      term1 = t1 or t2
    if t1 or t2 is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t1 or t2
    if t1 and t2 do not have the same bitvector type
      code = INCOMPATIBLE_TYPES
      term1 = t1
      type1 = type of t1
      term2 = t2
      type2 = type of t2.
    """
    return libyices.yices_bvsge_atom(t1, t2)

# term_t yices_bvsgt_atom(term_t t1, term_t t2)  // t1 > t2
libyices.yices_bvsgt_atom.restype = term_t
libyices.yices_bvsgt_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvsgt_atom(t1, t2):
    """Creates the term asserting (t1 > t2), or returns the NULL_TERM (i.e., a negative index) on error.

    Error reports
    if t1 or t2 is not valid
      code = INVALID_TERM
      term1 = t1 or t2
    if t1 or t2 is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t1 or t2
    if t1 and t2 do not have the same bitvector type
      code = INCOMPATIBLE_TYPES
      term1 = t1
      type1 = type of t1
      term2 = t2
      type2 = type of t2.
    """
    return libyices.yices_bvsgt_atom(t1, t2)

# term_t yices_bvsle_atom(term_t t1, term_t t2)  // t1 <= t2
libyices.yices_bvsle_atom.restype = term_t
libyices.yices_bvsle_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvsle_atom(t1, t2):
    """Creates the term asserting (t1 <= t2), or returns the NULL_TERM (i.e., a negative index) on error.

    Error reports
    if t1 or t2 is not valid
      code = INVALID_TERM
      term1 = t1 or t2
    if t1 or t2 is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t1 or t2
    if t1 and t2 do not have the same bitvector type
      code = INCOMPATIBLE_TYPES
      term1 = t1
      type1 = type of t1
      term2 = t2
      type2 = type of t2.
    """
    return libyices.yices_bvsle_atom(t1, t2)

# term_t yices_bvslt_atom(term_t t1, term_t t2)  // t1 < t2
libyices.yices_bvslt_atom.restype = term_t
libyices.yices_bvslt_atom.argtypes = [term_t, term_t]
@catch_error(-1)
def yices_bvslt_atom(t1, t2):
    """Creates the term asserting (t1 < t2), or returns the NULL_TERM (i.e., a negative index) on error.

    Error reports
    if t1 or t2 is not valid
      code = INVALID_TERM
      term1 = t1 or t2
    if t1 or t2 is not a bitvector term
      code = BITVECTOR_REQUIRED
      term1 = t1 or t2
    if t1 and t2 do not have the same bitvector type
      code = INCOMPATIBLE_TYPES
      term1 = t1
      type1 = type of t1
      term2 = t2
      type2 = type of t2.
    """
    return libyices.yices_bvslt_atom(t1, t2)


################
#  PARSING     #
################

# type_t yices_parse_type(const char *s)
libyices.yices_parse_type.restype = type_t
libyices.yices_parse_type.argtypes = [c_char_p]
@catch_error(-1)
def yices_parse_type(s):
    """Returns the result of parsing s as a Yices type."""
    return libyices.yices_parse_type(s)

# term_t yices_parse_term(const char *s)
libyices.yices_parse_term.restype = term_t
libyices.yices_parse_term.argtypes = [c_char_p]
@catch_error(-1)
def yices_parse_term(s):
    """Returns the result of parsing s as a Yices term."""
    return libyices.yices_parse_term(s)


#####################
#  SUBSTITUTIONS    #
#####################

# term_t yices_subst_term(uint32_t n, const term_t var[], const term_t map[], term_t t)
libyices.yices_subst_term.restype = term_t
libyices.yices_subst_term.argtypes = [c_uint32, POINTER(term_t), POINTER(term_t), term_t]
@catch_error(-1)
def yices_subst_term(n, var, smap, t):
    """Returns the result of applying the substitution defined by arrays var and smap to a term t."""
    return libyices.yices_subst_term(n, var, smap, t)

# int32_t yices_subst_term_array(uint32_t n, const term_t var[], const term_t map[], uint32_t m, term_t t[])
libyices.yices_subst_term_array.restype = c_int32
libyices.yices_subst_term_array.argtypes = [c_uint32, POINTER(term_t), POINTER(term_t), c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_subst_term_array(n, var, smap, m, t):
    """Returns the result of applying the substitution to m terms in parallel."""
    return libyices.yices_subst_term_array(n, var, smap, m, t)

##############
#  NAMES     #
##############

 # int32_t yices_set_type_name(type_t tau, const char *name)
libyices.yices_set_type_name.restype = c_int32
libyices.yices_set_type_name.argtypes = [type_t, c_char_p]
@catch_error(-1)
def yices_set_type_name(tau, name):
    """Attaches the name to the type tau, for subsequent retrieval."""
    return libyices.yices_set_type_name(tau, name)

# int32_t yices_set_term_name(term_t t, const char *name)
libyices.yices_set_term_name.restype = c_int32
libyices.yices_set_term_name.argtypes = [type_t, c_char_p]
@catch_error(-1)
def yices_set_term_name(t, name):
    """Attaches the name to the term t, for subsequent retrieval."""
    return libyices.yices_set_term_name(t, name)

# void yices_remove_type_name(const char *name)
libyices.yices_remove_type_name.argtypes = [c_char_p]
@catch_error(-1)
def yices_remove_type_name(name):
    """Removes the name from its attachment to the type."""
    libyices.yices_remove_type_name(name)

# void yices_remove_term_name(const char *name)
libyices.yices_remove_term_name.argtypes = [c_char_p]
@catch_error(-1)
def yices_remove_term_name(name):
    """Removes the name from its attachment to the term."""
    libyices.yices_remove_term_name(name)

# type_t yices_get_type_by_name(const char *name)
libyices.yices_get_type_by_name.restype = type_t
libyices.yices_get_type_by_name.argtypes = [c_char_p]
@catch_error(-1)
def yices_get_type_by_name(name):
    """Retrieves the type named by name."""
    return libyices.yices_get_type_by_name(name)

# term_t yices_get_term_by_name(const char *name)
libyices.yices_get_term_by_name.restype = term_t
libyices.yices_get_term_by_name.argtypes = [c_char_p]
@catch_error(-1)
def yices_get_term_by_name(name):
    """Retrieves the term named by name."""
    return libyices.yices_get_term_by_name(name)

# int32_t yices_clear_type_name(type_t tau)
libyices.yices_clear_type_name.restype = c_int32
libyices.yices_clear_type_name.argtypes = [type_t]
@catch_error(-1)
def yices_clear_type_name(tau):
    """Removes any name attached to the type tau."""
    return libyices.yices_clear_type_name(tau)

# int32_t yices_clear_term_name(term_t t)
libyices.yices_clear_term_name.restype = c_int32
libyices.yices_clear_term_name.argtypes = [term_t]
@catch_error(-1)
def yices_clear_term_name(t):
    """Removes any name attached to the term tau."""
    return libyices.yices_clear_term_name(t)

# const char *yices_get_type_name(type_t tau)
libyices.yices_get_type_name.restype = c_char_p
libyices.yices_get_type_name.argtypes = [type_t]
@catch_error(-1)
def yices_get_type_name(tau):
    """Retrieves the name attached to the type tau."""
    return libyices.yices_get_type_name(tau)

# const char *yices_get_term_name(term_t t)
libyices.yices_get_term_name.restype = c_char_p
libyices.yices_get_term_name.argtypes = [term_t]
@catch_error(-1)
def yices_get_term_name(t):
    """Retrieves the name attached to the term t."""
    return libyices.yices_get_term_name(t)


########################
#   TERM EXPLORATION   #
########################

# type_t yices_type_of_term(term_t t)
libyices.yices_type_of_term.restype = type_t
libyices.yices_type_of_term.argtypes = [term_t]
@catch_error(-1)
def yices_type_of_term(t):
    """Returns the type of the term t, or NULL_TYPE if t is not a valid term."""
    return libyices.yices_type_of_term(t)

# int32_t yices_term_is_bool(term_t t)
libyices.yices_term_is_bool.restype = c_int32
libyices.yices_term_is_bool.argtypes = [term_t]
@catch_error(0)
def yices_term_is_bool(t):
    """Returns 1 if t has type bool, 0 otherwise."""
    return libyices.yices_term_is_bool(t)

# int32_t yices_term_is_int(term_t t)
libyices.yices_term_is_int.restype = c_int32
libyices.yices_term_is_int.argtypes = [term_t]
@catch_error(0)
def yices_term_is_int(t):
    """Returns 1 if t has type int, 0 otherwise."""
    return libyices.yices_term_is_int(t)

# int32_t yices_term_is_real(term_t t)
libyices.yices_term_is_real.restype = c_int32
libyices.yices_term_is_real.argtypes = [term_t]
@catch_error(0)
def yices_term_is_real(t):
    """Returns 1 if t has type real, 0 otherwise."""
    return libyices.yices_term_is_real(t)

# int32_t yices_term_is_arithmetic(term_t t)
libyices.yices_term_is_arithmetic.restype = c_int32
libyices.yices_term_is_arithmetic.argtypes = [term_t]
@catch_error(0)
def yices_term_is_arithmetic(t):
    """Returns 1 if t has type real or int, 0 otherwise."""
    return libyices.yices_term_is_arithmetic(t)

# int32_t yices_term_is_bitvector(term_t t)
libyices.yices_term_is_bitvector.restype = c_int32
libyices.yices_term_is_bitvector.argtypes = [term_t]
@catch_error(0)
def yices_term_is_bitvector(t):
    """Returns 1 if t is a bitvector, 0 otherwise."""
    return libyices.yices_term_is_bitvector(t)

# int32_t yices_term_is_tuple(term_t t)
libyices.yices_term_is_tuple.restype = c_int32
libyices.yices_term_is_tuple.argtypes = [term_t]
@catch_error(0)
def yices_term_is_tuple(t):
    """Returns 1 if t is a tuple, 0 otherwise."""
    return libyices.yices_term_is_tuple(t)

# int32_t yices_term_is_function(term_t t)
libyices.yices_term_is_function.restype = c_int32
libyices.yices_term_is_function.argtypes = [term_t]
@catch_error(0)
def yices_term_is_function(t):
    """Returns 1 if t is a function, 0 otherwise."""
    return libyices.yices_term_is_function(t)

# int32_t yices_term_is_scalar(term_t t)
libyices.yices_term_is_scalar.restype = c_int32
libyices.yices_term_is_scalar.argtypes = [term_t]
@catch_error(0)
def yices_term_is_scalar(t):
    """Returns 1 if t is a scalar, 0 otherwise."""
    return libyices.yices_term_is_scalar(t)

# uint32_t yices_term_bitsize(term_t t)
libyices.yices_term_bitsize.restype = c_uint32
libyices.yices_term_bitsize.argtypes = [term_t]
@catch_error(0)
def yices_term_bitsize(t):
    """Returns the bitsize of the bitvector t, 0 if tehre is an error."""
    return libyices.yices_term_bitsize(t)

# int32_t yices_term_is_ground(term_t t)
libyices.yices_term_is_ground.restype = c_int32
libyices.yices_term_is_ground.argtypes = [term_t]
@catch_error(0)
def yices_term_is_ground(t):
    """Returns 1 if t is ground (i.e. has no free variables), 0 otherwise."""
    return libyices.yices_term_is_ground(t)

# int32_t yices_term_is_atomic(term_t t)
libyices.yices_term_is_atomic.restype = c_int32
libyices.yices_term_is_atomic.argtypes = [term_t]
@catch_error(0)
def yices_term_is_atomic(t):
    """Returns 1 if t is atomic (i.e. has no subterms), 0 otherwise."""
    return libyices.yices_term_is_atomic(t)

# int32_t yices_term_is_composite(term_t t)
libyices.yices_term_is_composite.restype = c_int32
libyices.yices_term_is_composite.argtypes = [term_t]
@catch_error(0)
def yices_term_is_composite(t):
    """Returns 1 if the term is a composite, 0 otherwise.

    Composite terms are of the form
     (constructor, number-of-children, list-of-children)
    """
    return libyices.yices_term_is_composite(t)

# int32_t yices_term_is_projection(term_t t)
libyices.yices_term_is_projection.restype = c_int32
libyices.yices_term_is_projection.argtypes = [term_t]
@catch_error(0)
def yices_term_is_projection(t):
    """Returns 1 if t is a projection (i.e. is of the form (select i t) or (bit i t)), 0 otherwise."""
    return libyices.yices_term_is_projection(t)

# int32_t yices_term_is_sum(term_t t)
libyices.yices_term_is_sum.restype = c_int32
libyices.yices_term_is_sum.argtypes = [term_t]
@catch_error(0)
def yices_term_is_sum(t):
    """Returns 1 if t is a sum (i.e. is of the form (a_0 t_0 + ... + a_n t_n) where the a_i are rational, and t_i are arithmetic), 0 otherwise."""
    return libyices.yices_term_is_sum(t)

# int32_t yices_term_is_bvsum(term_t t)
libyices.yices_term_is_bvsum.restype = c_int32
libyices.yices_term_is_bvsum.argtypes = [term_t]
@catch_error(-1)
def yices_term_is_bvsum(t):
    """Returns 1 if t is a bvsum (i.e. is of the form (a_0 t_0 + ... + a_n t_n) where the a_i are bitvector constants, and t_i are bitvectors), 0 otherwise."""
    return libyices.yices_term_is_bvsum(t)

# int32_t yices_term_is_product(term_t t)
libyices.yices_term_is_product.restype = c_int32
libyices.yices_term_is_product.argtypes = [term_t]
@catch_error(-1)
def yices_term_is_product(t):
    """Returns 1 if t is a product (i.e. is of the form (t_0^d_0 x ... x t_n ^d_n) where the p_i are positive exponents, and t_i are ALL arithmetic or ALL bitvector), 0 otherwise."""
    return libyices.yices_term_is_product(t)

# term_constructor_t yices_term_constructor(term_t t)
libyices.yices_term_constructor.restype = term_constructor_t
libyices.yices_term_constructor.argtypes = [term_t]
@catch_error(-1)
def yices_term_constructor(t):
    """Returns the constructor of the composite term t, or a negative number otherwise."""
    return libyices.yices_term_constructor(t)

# int32_t yices_term_num_children(term_t t)
libyices.yices_term_num_children.restype = c_int32
libyices.yices_term_num_children.argtypes = [term_t]
@catch_error(-1)
def yices_term_num_children(t):
    """Returns the number of children of the composite term t, or a -1 if there is an error.

       - for atomic terms, returns 0
       - for composite terms, returns the number of children
       - for projections, returns 1
       - for sums, returns the number of summands
       - for products, returns the number of factors
    """
    return libyices.yices_term_num_children(t)

# term_t yices_term_child(term_t t, int32_t i)
libyices.yices_term_child.restype = term_t
libyices.yices_term_child.argtypes = [term_t, c_int32]
@catch_error(-1)
def yices_term_child(t, i):
    """Returns the i-th child of the composite term t, or a NULL_TERM if there is an error."""
    return libyices.yices_term_child(t, i)

# int32_t yices_proj_index(term_t t)
libyices.yices_proj_index.restype = c_int32
libyices.yices_proj_index.argtypes = [term_t]
@catch_error(-1)
def yices_proj_index(t):
    """Returns the index of the projection t."""
    return libyices.yices_proj_index(t)

# term_t yices_proj_arg(term_t t)
libyices.yices_proj_arg.restype = term_t
libyices.yices_proj_arg.argtypes = [term_t]
@catch_error(-1)
def yices_proj_arg(t):
    """Returns the argument of the projection t."""
    return libyices.yices_proj_arg(t)

# int32_t yices_bool_const_value(term_t t, int32_t *val)
libyices.yices_bool_const_value.restype = c_int32
libyices.yices_bool_const_value.argtypes = [term_t, POINTER(c_int32)]
@catch_error(-1)
def yices_bool_const_value(t, val):
    """Stores the value of the constant bool term t in val, returning 0 if successful, -1 otherwise."""
    return libyices.yices_bool_const_value(t, val)

# int32_t yices_bv_const_value(term_t t, int32_t val[])
libyices.yices_bv_const_value.restype = c_int32
libyices.yices_bv_const_value.argtypes = [term_t, POINTER(c_int32)]
@catch_error(-1)
def yices_bv_const_value(t, val):
    """Stores the value of the constant bitvector term t in val, returning 0 if successful, -1 otherwise."""
    return libyices.yices_bv_const_value(t, val)

# int32_t yices_scalar_const_value(term_t t, int32_t *val)
libyices.yices_scalar_const_value.restype = c_int32
libyices.yices_scalar_const_value.argtypes = [term_t, POINTER(c_int32)]
@catch_error(-1)
def yices_scalar_const_value(t, val):
    """Stores the value of the constant scalar term t in val, returning 0 if successful, -1 otherwise."""
    return libyices.yices_scalar_const_value(t, val)

# int32_t yices_rational_const_value(term_t t, mpq_t q)
libyices.yices_rational_const_value.restype = c_int32
libyices.yices_rational_const_value.argtypes = [term_t, POINTER(mpq_t)]
@catch_error(-1)
def yices_rational_const_value(t, q):
    """Stores the value of the constant rational term t in val, returning 0 if successful, -1 otherwise."""
    return libyices.yices_rational_const_value(t, q)

# int32_t yices_sum_component(term_t t, int32_t i, mpq_t coeff, term_t *term)
libyices.yices_sum_component.restype = c_int32
libyices.yices_sum_component.argtypes = [term_t, c_int32, POINTER(mpq_t), POINTER(term_t)]
@catch_error(-1)
def yices_sum_component(t, i, coeff, term):
    """Stores the coefficient and the term t in the passed in arguments, returning 0 if successful, -1 otherwise."""
    #  return libyices.yices_sum_component(t, i, byref(coeff), byref(term))
    return libyices.yices_sum_component(t, i, pointer(coeff), pointer(term))

# int32_t yices_bvsum_component(term_t t, int32_t i, int32_t val[], term_t *term)
libyices.yices_bvsum_component.restype = c_int32
libyices.yices_bvsum_component.argtypes = [term_t, c_int32, POINTER(c_int32), POINTER(term_t)]
@catch_error(-1)
def yices_bvsum_component(t, i, val, term):
    """Stores the coefficient and the term t in the passed in arguments, returning 0 if successful, -1 otherwise."""
    return libyices.yices_bvsum_component(t, i, val, pointer(term))

# int32_t yices_product_component(term_t t, int32_t i, term_t *term, uint32_t *exp)
libyices.yices_product_component.restype = c_int32
libyices.yices_product_component.argtypes = [term_t, c_int32, POINTER(term_t), POINTER(c_int32)]
@catch_error(-1)
def yices_product_component(t, i, term, exp):
    """Stores the exponent and the term t in the passed in arguments, returning 0 if successful, -1 otherwise."""
    return libyices.yices_product_component(t, i, pointer(term), pointer(exp))

##########################
#  GARBAGE COLLECTION    #
##########################


# uint32_t yices_num_terms(void)
libyices.yices_num_terms.restype = c_uint32
@catch_error(-1)
def yices_num_terms():
    """Returns the number of terms currently in the internal data structures."""
    return libyices.yices_num_terms()

# uint32_t yices_num_types(void)
libyices.yices_num_types.restype = c_uint32
@catch_error(-1)
def yices_num_types():
    """Returns the number of types currently in the internal data structures."""
    return libyices.yices_num_types()

# int32_t yices_incref_term(term_t t)
libyices.yices_incref_term.restype = c_int32
libyices.yices_incref_term.argtypes = [term_t]
@catch_error(-1)
def yices_incref_term(t):
    """Increments the reference count of the term, return 0 on success, -1 on failure."""
    return libyices.yices_incref_term(t)

# int32_t yices_decref_term(term_t t)
libyices.yices_decref_term.restype = c_int32
libyices.yices_decref_term.argtypes = [term_t]
@catch_error(-1)
def yices_decref_term(t):
    """Decrements the reference count of the term, return 0 on success, -1 on failure."""
    return libyices.yices_decref_term(t)

# int32_t yices_incref_type(type_t tau)
libyices.yices_incref_type.restype = c_int32
libyices.yices_incref_type.argtypes = [term_t]
@catch_error(-1)
def yices_incref_type(tau):
    """Increments the reference count of the type, return 0 on success, -1 on failure."""
    return libyices.yices_incref_type(tau)

# int32_t yices_decref_type(type_t tau)
libyices.yices_decref_type.restype = c_int32
libyices.yices_decref_type.argtypes = [term_t]
@catch_error(-1)
def yices_decref_type(tau):
    """Decrements the reference count of the type, return 0 on success, -1 on failure."""
    return libyices.yices_decref_type(tau)

# uint32_t yices_num_posref_terms(void)
libyices.yices_num_posref_terms.restype = c_uint32
@catch_error(-1)
def yices_num_posref_terms():
    """Returns the number of terms that have positive reference count."""
    return libyices.yices_num_posref_terms()

# uint32_t yices_num_posref_types(void)
libyices.yices_num_posref_types.restype = c_uint32
@catch_error(-1)
def yices_num_posref_types():
    """Returns the number of types that have positive reference count."""
    return libyices.yices_num_posref_types()

# void yices_garbage_collect(const term_t t[], uint32_t nt, const type_t tau[], uint32_t ntau, int32_t keep_named)
libyices.yices_garbage_collect.argtypes = [POINTER(term_t), c_uint32, POINTER(type_t), c_uint32, c_int32]
@catch_error(-1)
def yices_garbage_collect(t, nt, tau, ntau, keep_named):
    """Explicitly calls the garbage collector.

    - t = optional array of terms
    - nt = size of t
    - tau = optional array of types
    - ntau = size of tau
    - keep_named specifies whether the named terms and types should
    all be preserved.
    """
    return libyices.yices_garbage_collect(t, nt, tau, ntau, keep_named)


#############################
#  CONTEXT CONFIGURATION    #
#############################

# ctx_config_t *yices_new_config(void)
libyices.yices_new_config.restype = ctx_config_t
@catch_error(-1)
def yices_new_config():
    """Returns a newly allocated context configuration descriptor, set to the default configuration."""
    return libyices.yices_new_config()

# void yices_free_config(ctx_config_t *config)
libyices.yices_free_config.argtypes = [ctx_config_t]
@catch_error(-1)
def yices_free_config(config):
    """Frees the context descriptor."""
    libyices.yices_free_config(config)

# int32_t yices_set_config(ctx_config_t *config, const char *name, const char *value)
libyices.yices_set_config.restype = c_int32
libyices.yices_set_config.argtypes = [ctx_config_t, c_char_p, c_char_p]
@catch_error(-1)
def yices_set_config(config, name, value):
    """Sets the value of name in the context configuration, returns 0 on success, -1 on failure."""
    return libyices.yices_set_config(config, name, value)

# int32_t yices_default_config_for_logic(ctx_config_t *config, const char *logic)
libyices.yices_default_config_for_logic.restype = c_int32
libyices.yices_default_config_for_logic.argtypes = [ctx_config_t, c_char_p]
@catch_error(-1)
def yices_default_config_for_logic(config, logic):
    """Sets the logic of the context configuration, returns 0 on success, -1 on failure."""
    return libyices.yices_default_config_for_logic(config, logic)

#################
#   CONTEXTS    #
#################

# context_t *yices_new_context(const ctx_config_t *config)
libyices.yices_new_context.restype = context_t
libyices.yices_new_context.argtypes = [ctx_config_t]
@catch_error(-1)
def yices_new_context(config):
    """Returns a newly allocated context; a context is a stack of assertions."""
    return libyices.yices_new_context(config)

# void yices_free_context(context_t *ctx)
libyices.yices_free_context.argtypes = [context_t]
@catch_error(-1)
def yices_free_context(ctx):
    """Frees a context."""
    libyices.yices_free_context(ctx)

# smt_status_t yices_context_status(context_t *ctx)
libyices.yices_context_status.restype = smt_status_t
libyices.yices_context_status.argtypes = [context_t]
@catch_error(-1)
def yices_context_status(ctx):
    """The context status: a number (starting with 0L) representing one of
    STATUS_IDLE, STATUS_SEARCHING, STATUS_UNKNOWN,
    STATUS_SAT, STATUS_UNSAT, STATUS_INTERRUPTED, STATUS_ERROR
    """
    return libyices.yices_context_status(ctx)

# void yices_reset_context(context_t *ctx)
libyices.yices_reset_context.argtypes = [context_t]
@catch_error(-1)
def yices_reset_context(ctx):
    """Removes all assertions from the context."""
    libyices.yices_reset_context(ctx)

# int32_t yices_push(context_t *ctx)
libyices.yices_push.restype = c_int32
libyices.yices_push.argtypes = [context_t]
@catch_error(-1)
def yices_push(ctx):
    """Marks a backtrack point in the context, returns 0 on success, -1 otherwise."""
    return libyices.yices_push(ctx)

# int32_t yices_pop(context_t *ctx)
libyices.yices_pop.restype = c_int32
libyices.yices_pop.argtypes = [context_t]
@catch_error(-1)
def yices_pop(ctx):
    """Backtracks to the previous backtrack point, returns 0 on success, -1 otherwise."""
    return libyices.yices_pop(ctx)

# int32_t yices_context_enable_option(context_t *ctx, const char *option)
libyices.yices_context_enable_option.restype = c_int32
libyices.yices_context_enable_option.argtypes = [context_t, c_char_p]
@catch_error(-1)
def yices_context_enable_option(ctx, option):
    """Used to tune the amount of simplification used when evaluating assertions."""
    return libyices.yices_context_enable_option(ctx, option)

# int32_t yices_context_disable_option(context_t *ctx, const char *option)
libyices.yices_context_disable_option.restype = c_int32
libyices.yices_context_disable_option.argtypes = [context_t, c_char_p]
@catch_error(-1)
def yices_context_disable_option(ctx, option):
    """Used to tune the amount of simplification used when evaluating assertions."""
    return libyices.yices_context_disable_option(ctx, option)

# int32_t yices_assert_formula(context_t *ctx, term_t t)
libyices.yices_assert_formula.restype = c_int32
libyices.yices_assert_formula.argtypes = [context_t, term_t]
@catch_error(-1)
def yices_assert_formula(ctx, t):
    """Assert the formula t in the context ctx.

    - ctx status must be STATUS_IDLE or STATUS_UNSAT or STATUS_SAT or STATUS_UNKNOWN
    - t must be a boolean term

    If ctx's status is STATUS_UNSAT, nothing is done.

    If ctx's status is STATUS_IDLE, STATUS_SAT, or STATUS_UNKNOWN, then
    the formula is simplified and  asserted in the context. The context
    status is changed  to STATUS_UNSAT if the formula  is simplified to
    'false' or to STATUS_IDLE otherwise.

    This returns 0 if there's no error or -1 if there's an error.
    """
    return libyices.yices_assert_formula(ctx, t)

# int32_t yices_assert_formulas(context_t *ctx, uint32_t n, const term_t t[])
libyices.yices_assert_formulas.restype = c_int32
libyices.yices_assert_formulas.argtypes = [context_t, c_uint32, POINTER(term_t)]
@catch_error(-1)
def yices_assert_formulas(ctx, n, t):
    """Assert an array of formulas of length n in the context ctx."""
    return libyices.yices_assert_formulas(ctx, n, t)

# smt_status_t yices_check_context(context_t *ctx, const param_t *params)
libyices.yices_check_context.restype = smt_status_t
libyices.yices_check_context.argtypes = [context_t, param_t]
@catch_error(-1)
def yices_check_context(ctx, params):
    """Checks whether all the assertions stored in the context ctx are satisfiable.

    - params is an optional structure that stores heuristic parameters.
    - if params is NULL, default parameter settings are used.

    It's better to keep params=NULL unless you encounter performance
    problems.  Then you may want to play with the heuristics to see if
    performance improves.
    """
    return libyices.yices_check_context(ctx, params)

# int32_t yices_assert_blocking_clause(context_t *ctx)
libyices.yices_assert_blocking_clause.restype = c_int32
libyices.yices_assert_blocking_clause.argtypes = [context_t]
@catch_error(-1)
def yices_assert_blocking_clause(ctx):
    """Adds a blocking clause, this is intended to help enumerate different models for a set of assertions."""
    return libyices.yices_assert_blocking_clause(ctx)

# void yices_stop_search(context_t *ctx)
libyices.yices_stop_search.argtypes = [context_t]
@catch_error(-1)
def yices_stop_search(ctx):
    """Interupts the search."""
    libyices.yices_stop_search(ctx)

#
# SEARCH PARAMETERS
#

# param_t *yices_new_param_record(void)
libyices.yices_new_param_record.restype = param_t
@catch_error(-1)
def yices_new_param_record():
    """Creates a new param object, an opaque object that stores various search parameters and options that control the heuristics used by the solver."""
    return libyices.yices_new_param_record()

# void yices_default_params_for_context(context_t *ctx, param_t *params)
libyices.yices_default_params_for_context.argtypes = [context_t, param_t]
@catch_error(-1)
def yices_default_params_for_context(ctx, params):
    """Initializes the param object to have the default values."""
    libyices.yices_default_params_for_context(ctx, params)

# int32_t yices_set_param(param_t *p, const char *pname, const char *value)
libyices.yices_set_param.restype = c_int32
libyices.yices_set_param.argtypes = [param_t, c_char_p, c_char_p]
@catch_error(-1)
def yices_set_param(p, pname, value):
    """Sets the value of the parameter pname in the param object to be value."""
    return libyices.yices_set_param(p, pname, value)

# void yices_free_param_record(param_t *param)
libyices.yices_free_param_record.argtypes = [param_t]
@catch_error(-1)
def yices_free_param_record(param):
    """Frees an param object."""
    libyices.yices_free_param_record(param)


################
#   MODELS     #
################


# model_t *yices_get_model(context_t *ctx, int32_t keep_subst)
libyices.yices_get_model.restype = model_t
libyices.yices_get_model.argtypes = [context_t, c_int32]
@catch_error(-1)
def yices_get_model(ctx, keep_subst):
    """Builds a model from the context ctx.

    - keep_subst indicates whether the model should include
      the eliminated variables:
      keep_subst = 0 means don't keep substitutions,
      keep_subst != 0 means keep them
    - ctx status must be STATUS_SAT or STATUS_UNKNOWN

    The function returns NULL if the status isn't SAT or STATUS_UNKNOWN
    and sets an error report (code = CTX_INVALID_OPERATION).
    """
    #FIXME: ask Sam why we are doing @catch_error(-1) rather than @catch_error(0)or @catch_error(None)
    mdl = libyices.yices_get_model(ctx, keep_subst)
    if mdl is None:
        raise YicesException('Model not available - result of check_context should yield context_status of 2 (STATUS_SAT) or 3 (STATUS_UNKNOWN)')
    return mdl

# void yices_free_model(model_t *mdl)
libyices.yices_free_model.argtypes = [model_t]
@catch_error(-1)
def yices_free_model(mdl):
    """Frees the model."""
    libyices.yices_free_model(mdl)

# model_t *yices_model_from_map(uint32_t n, const term_t var[], const term_t map[])
libyices.yices_model_from_map.restype = model_t
libyices.yices_model_from_map.argtypes = [c_uint32, POINTER(term_t), POINTER(term_t)]
@catch_error(-1)
def yices_model_from_map(n, var, mp):
    """Builds a model from a term to term mapping.

    - the mapping is defined by two arrays var[] and map[]
    - every element of var must be an uninterpreted term
      every element of map must be a constant of primitive or tuple type
      map[i]'s type must be a subtype of var[i]
    - there must not be duplicates in array var

    The function returns NULL and sets up the error report if something
    goes wrong. It allocates and creates a new model otherwise. When
    the model is no longer used, it must be deleted by calling yices_free_model.
    """
    return libyices.yices_model_from_map(n, var, mp)


########################
#  VALUES IN A MODEL  #
########################


#
# EVALUATION FOR SIMPLE TYPES
#


# int32_t yices_get_bool_value(model_t *mdl, term_t t, int32_t *val)
libyices.yices_get_bool_value.restype = c_int32
libyices.yices_get_bool_value.argtypes = [model_t, term_t, POINTER(c_int32)]
@catch_error(-1)
def yices_get_bool_value(mdl, t, val):
    """Places the value of the bool term into val, returns 0 on success, and -1 on failure."""
    return libyices.yices_get_bool_value(mdl, t, val)

# int32_t yices_get_int32_value(model_t *mdl, term_t t, int32_t *val)
libyices.yices_get_int32_value.restype = c_int32
libyices.yices_get_int32_value.argtypes = [model_t, term_t, POINTER(c_int32)]
@catch_error(-1)
def yices_get_int32_value(mdl, t, val):
    """Places the value of the int32 term into val, returns 0 on success, and -1 on failure."""
    return libyices.yices_get_int32_value(mdl, t, val)

# int32_t yices_get_int64_value(model_t *mdl, term_t t, int64_t *val)
libyices.yices_get_int64_value.restype = c_int32
libyices.yices_get_int64_value.argtypes = [model_t, term_t, POINTER(c_int64)]
@catch_error(-1)
def yices_get_int64_value(mdl, t, val):
    """Places the value of the int64 term into val, returns 0 on success, and -1 on failure."""
    return libyices.yices_get_int64_value(mdl, t, val)

# int32_t yices_get_rational32_value(model_t *mdl, term_t t, int32_t *num, uint32_t *den)
libyices.yices_get_rational32_value.restype = c_int32
libyices.yices_get_rational32_value.argtypes = [model_t, term_t, POINTER(c_int32), POINTER(c_uint32)]
@catch_error(-1)
def yices_get_rational32_value(mdl, t, num, den):
    """Places the values of the numerator and denominator of the 32 bit rational term into num and dem, returns 0 on success, and -1 on failure."""
    return libyices.yices_get_rational32_value(mdl, t, num, den)

# int32_t yices_get_rational64_value(model_t *mdl, term_t t, int64_t *num, uint64_t *den)
libyices.yices_get_rational64_value.restype = c_int32
libyices.yices_get_rational64_value.argtypes = [model_t, term_t, POINTER(c_int64), POINTER(c_uint64)]
@catch_error(-1)
def yices_get_rational64_value(mdl, t, num, den):
    """Places the values of the numerator and denominator of the 64 bit rational term into num and dem, returns 0 on success, and -1 on failure."""
    return libyices.yices_get_rational64_value(mdl, t, num, den)

# int32_t yices_get_double_value(model_t *mdl, term_t t, double *val)
libyices.yices_get_double_value.restype = c_int32
libyices.yices_get_double_value.argtypes = [model_t, term_t, POINTER(c_double)]
@catch_error(-1)
def yices_get_double_value(mdl, t, val):
    """Places the value of the double term into val, returns 0 on success, and -1 on failure."""
    return libyices.yices_get_double_value(mdl, t, val)

# int32_t yices_get_mpz_value(model_t *mdl, term_t t, mpz_t val)
libyices.yices_get_mpz_value.restype = c_int32
libyices.yices_get_mpz_value.argtypes = [model_t, term_t, POINTER(mpz_t)]
@catch_error(-1)
def yices_get_mpz_value(mdl, t, val):
    """Places the value of the mpz term into val, returns 0 on success, and -1 on failure."""
    return libyices.yices_get_mpz_value(mdl, t, val)

# int32_t yices_get_mpq_value(model_t *mdl, term_t t, mpq_t val)
libyices.yices_get_mpq_value.restype = c_int32
libyices.yices_get_mpq_value.argtypes = [model_t, term_t, POINTER(mpq_t)]
@catch_error(-1)
def yices_get_mpq_value(mdl, t, val):
    """Places the value of the mpq term into val, returns 0 on success, and -1 on failure."""
    return libyices.yices_get_mpq_value(mdl, t, val)

# int32_t yices_get_algebraic_number_value(model_t *mdl, term_t t, lp_algebraic_number_t *a)
libyices.yices_get_algebraic_number_value.restype = c_int32
libyices.yices_get_algebraic_number_value.argtypes = [model_t, term_t, POINTER(lp_algebraic_number_t)]
@catch_error(-1)
def yices_get_algebraic_number_value(mdl, t, a):
    """Conversion to an algebraic number.

    get_algebraic_number_value(mdl, t, a):
    t must be an arithmetic term.

    Error codes:
    - if t's value is rational:
       code = EVAL_CONVERSION_FAILED
    - if yices is compiled without support for MCSAT
       code = EVAL_NOT_SUPPORTED.
    """
    return libyices.yices_get_algebraic_number_value(mdl, t, a)

# int32_t yices_get_bv_value(model_t *mdl, term_t t, int32_t val[])
libyices.yices_get_bv_value.restype = c_int32
libyices.yices_get_bv_value.argtypes = [model_t, term_t, POINTER(c_int32)]
@catch_error(-1)
def yices_get_bv_value(mdl, t, val):
    """Places the value of the bitvector term into val, returns 0 on success, and -1 on failure."""
    return libyices.yices_get_bv_value(mdl, t, val)

# int32_t yices_get_scalar_value(model_t *mdl, term_t t, int32_t *val)
libyices.yices_get_scalar_value.restype = c_int32
libyices.yices_get_scalar_value.argtypes = [model_t, term_t, POINTER(c_int32)]
@catch_error(-1)
def yices_get_scalar_value(mdl, t, val):
    """Places the value of the scalar term into val, returns 0 on success, and -1 on failure."""
    return libyices.yices_get_scalar_value(mdl, t, val)


#
# GENERIC FORM: VALUE DESCRIPTORS AND NODES
#

# void yices_init_yval_vector(yval_vector_t *v)
libyices.yices_init_yval_vector.argtypes = [POINTER(yval_vector_t)]
@catch_error(-1)
def yices_init_yval_vector(v):
    """Initialized a yval (node descriptor) vector, for storing non atomic values in models."""
    libyices.yices_init_yval_vector(pointer(v))

# void yices_delete_yval_vector(yval_vector_t *v)
libyices.yices_delete_yval_vector.argtypes = [POINTER(yval_vector_t)]
@catch_error(-1)
def yices_delete_yval_vector(v):
    """Frees a yval  (node descriptor) vector, for storing non atomic values in models."""
    libyices.yices_delete_yval_vector(pointer(v))

# void yices_reset_yval_vector(yval_vector_t *v)
libyices.yices_reset_yval_vector.argtypes = [POINTER(yval_vector_t)]
@catch_error(-1)
def yices_reset_yval_vector(v):
    """Resets a yval  (node descriptor) vector, for storing non atomic values in models."""
    libyices.yices_reset_yval_vector(pointer(v))

# int32_t yices_get_value(model_t *mdl, term_t t, yval_t *val)
libyices.yices_get_value.restype = c_int32
libyices.yices_get_value.argtypes = [model_t, term_t, POINTER(yval_t)]
@catch_error(-1)
def yices_get_value(mdl, t, val):
    """Retrieves the value of t in the model as a node descriptor."""
    return libyices.yices_get_value(mdl, t, val)

# int32_t yices_val_is_int32(model_t *mdl, const yval_t *v)
libyices.yices_val_is_int32.restype = c_int32
libyices.yices_val_is_int32.argtypes = [model_t, POINTER(yval_t)]
@catch_error(-1)
def yices_val_is_int32(mdl, v):
    """Tests if the node descriptor is a int32 value, returns 1 on success, 0 on failure."""
    return libyices.yices_val_is_int32(mdl, v)

# int32_t yices_val_is_int64(model_t *mdl, const yval_t *v)
libyices.yices_val_is_int64.restype = c_int32
libyices.yices_val_is_int64.argtypes = [model_t, POINTER(yval_t)]
@catch_error(-1)
def yices_val_is_int64(mdl, v):
    """Tests if the node descriptor is a int64 value, returns 1 on success, 0 on failure."""
    return libyices.yices_val_is_int64(mdl, v)

# int32_t yices_val_is_rational32(model_t *mdl, const yval_t *v)
libyices.yices_val_is_rational32.restype = c_int32
libyices.yices_val_is_rational32.argtypes = [model_t, POINTER(yval_t)]
@catch_error(-1)
def yices_val_is_rational32(mdl, v):
    """Tests if the node descriptor is a 32 bit rational value, returns 1 on success, 0 on failure."""
    return libyices.yices_val_is_rational32(mdl, v)

# int32_t yices_val_is_rational64(model_t *mdl, const yval_t *v)
libyices.yices_val_is_rational64.restype = c_int32
libyices.yices_val_is_rational64.argtypes = [model_t, POINTER(yval_t)]
@catch_error(-1)
def yices_val_is_rational64(mdl, v):
    """Tests if the node descriptor is a 64 bit rational value, returns 1 on success, 0 on failure."""
    return libyices.yices_val_is_rational64(mdl, v)

# int32_t yices_val_is_integer(model_t *mdl, const yval_t *v)
libyices.yices_val_is_integer.restype = c_int32
libyices.yices_val_is_integer.argtypes = [model_t, POINTER(yval_t)]
@catch_error(-1)
def yices_val_is_integer(mdl, v):
    """Tests if the node descriptor is a integer value, returns 1 on success, 0 on failure."""
    return libyices.yices_val_is_integer(mdl, v)

# uint32_t yices_val_bitsize(model_t *mdl, const yval_t *v)
libyices.yices_val_bitsize.restype = c_uint32
libyices.yices_val_bitsize.argtypes = [model_t, POINTER(yval_t)]
@catch_error(-1)
def yices_val_bitsize(mdl, v):
    """Gets the number of bits in the bitvector value, or 0 if v is not a bitvector."""
    return libyices.yices_val_bitsize(mdl, v)

# uint32_t yices_val_tuple_arity(model_t *mdl, const yval_t *v)
libyices.yices_val_tuple_arity.restype = c_uint32
libyices.yices_val_tuple_arity.argtypes = [model_t, POINTER(yval_t)]
@catch_error(-1)
def yices_val_tuple_arity(mdl, v):
    """Gets the arity of the tuple value, or 0 if v is not a tuple."""
    return libyices.yices_val_tuple_arity(mdl, v)

# uint32_t yices_val_mapping_arity(model_t *mdl, const yval_t *v)
libyices.yices_val_mapping_arity.restype = c_uint32
libyices.yices_val_mapping_arity.argtypes = [model_t, POINTER(yval_t)]
@catch_error(-1)
def yices_val_mapping_arity(mdl, v):
    """Gets the cardinality of the map value, or 0 if v is not a map."""
    return libyices.yices_val_mapping_arity(mdl, v)

# uint32_t yices_val_function_arity(model_t *mdl, const yval_t *v)
libyices.yices_val_function_arity.restype = c_uint32
libyices.yices_val_function_arity.argtypes = [model_t, POINTER(yval_t)]
@catch_error(-1)
def yices_val_function_arity(mdl, v):
    """Gets the arity of the function value, or 0 if v is not a function."""
    return libyices.yices_val_function_arity(mdl, v)

# int32_t yices_val_get_bool(model_t *mdl, const yval_t *v, int32_t *val)
libyices.yices_val_get_bool.restype = c_int32
libyices.yices_val_get_bool.argtypes = [model_t, POINTER(yval_t), POINTER(c_int32)]
@catch_error(-1)
def yices_val_get_bool(mdl, v, val):
    """Gets the bool value in the node descriptor v and places it in val, returns 0 if successful, -1 otherwise."""
    return libyices.yices_val_get_bool(mdl, pointer(v), val)

# int32_t yices_val_get_int32(model_t *mdl, const yval_t *v, int32_t *val)
libyices.yices_val_get_int32.restype = c_int32
libyices.yices_val_get_int32.argtypes = [model_t, POINTER(yval_t), POINTER(c_int32)]
@catch_error(-1)
def yices_val_get_int32(mdl, v, val):
    """Gets the int32 value in the node descriptor v and places it in val, returns 0 if successful, -1 otherwise."""
    return libyices.yices_val_get_int32(mdl, pointer(v), val)

# int32_t yices_val_get_int64(model_t *mdl, const yval_t *v, int64_t *val)
libyices.yices_val_get_int64.restype = c_int32
libyices.yices_val_get_int64.argtypes = [model_t, POINTER(yval_t), POINTER(c_int64)]
@catch_error(-1)
def yices_val_get_int64(mdl, v, val):
    """Gets the int64 value in the node descriptor v and places it in val, returns 0 if successful, -1 otherwise."""
    return libyices.yices_val_get_int64(mdl, pointer(v), val)

# int32_t yices_val_get_rational32(model_t *mdl, const yval_t *v, int32_t *num, uint32_t *den)
libyices.yices_val_get_rational32.restype = c_int32
libyices.yices_val_get_rational32.argtypes = [model_t, POINTER(yval_t), POINTER(c_int32), POINTER(c_uint32)]
@catch_error(-1)
def yices_val_get_rational32(mdl, v, num, den):
    """Gets the numerator and denominator of the 32 bit rational value in the node descriptor v and places them in num and den, returns 0 if successful, -1 otherwise."""
    return libyices.yices_val_get_rational32(mdl, pointer(v), num, den)

# int32_t yices_val_get_rational64(model_t *mdl, const yval_t *v, int64_t *num, uint64_t *den)
libyices.yices_val_get_rational64.restype = c_int32
libyices.yices_val_get_rational64.argtypes = [model_t, POINTER(yval_t), POINTER(c_int64), POINTER(c_uint64)]
@catch_error(-1)
def yices_val_get_rational64(mdl, v, num, den):
    """Gets the numerator and denominator of the 64 bit rational value in the node descriptor v and places them in num and den, returns 0 if successful, -1 otherwise."""
    return libyices.yices_val_get_rational64(mdl, pointer(v), num, den)

# int32_t yices_val_get_double(model_t *mdl, const yval_t *v, double *val)
libyices.yices_val_get_double.restype = c_int32
libyices.yices_val_get_double.argtypes = [model_t, POINTER(yval_t), POINTER(c_double)]
@catch_error(-1)
def yices_val_get_double(mdl, v, val):
    """Gets the double value in the node descriptor v and places it in val, returns 0 if successful, -1 otherwise."""
    return libyices.yices_val_get_double(mdl, pointer(v), val)

# int32_t yices_val_get_mpz(model_t *mdl, const yval_t *v, mpz_t val)
libyices.yices_val_get_mpz.restype = c_int32
libyices.yices_val_get_mpz.argtypes = [model_t, POINTER(yval_t), POINTER(mpz_t)]
@catch_error(-1)
def yices_val_get_mpz(mdl, v, val):
    """Gets the mpz value in the node descriptor v and places it in val, returns 0 if successful, -1 otherwise."""
    return libyices.yices_val_get_mpz(mdl, pointer(v), pointer(val))

# int32_t yices_val_get_mpq(model_t *mdl, const yval_t *v, mpq_t val)
libyices.yices_val_get_mpq.restype = c_int32
libyices.yices_val_get_mpq.argtypes = [model_t, POINTER(yval_t), POINTER(mpq_t)]
@catch_error(-1)
def yices_val_get_mpq(mdl, v, val):
    """Gets the mpq value in the node descriptor v and places it in val, returns 0 if successful, -1 otherwise."""
    return libyices.yices_val_get_mpq(mdl, pointer(v), pointer(val))

# int32_t yices_val_get_algebraic_number(model_t *mdl, const yval_t *v, lp_algebraic_number_t *a)
libyices.yices_val_get_algebraic_number.restype = c_int32
libyices.yices_val_get_algebraic_number.argtypes = [model_t, POINTER(yval_t), POINTER(lp_algebraic_number_t)]
@catch_error(-1)
def yices_val_get_algebraic_number(mdl, v, a):
    """Gets the algebraic value in the node descriptor v and places it in val, returns 0 if successful, -1 otherwise."""
    return libyices.yices_val_get_algebraic_number(mdl, pointer(v), pointer(a))

# int32_t yices_val_get_bv(model_t *mdl, const yval_t *v, int32_t val[])
libyices.yices_val_get_bv.restype = c_int32
libyices.yices_val_get_bv.argtypes = [model_t, POINTER(yval_t), POINTER(c_int32)]
@catch_error(-1)
def yices_val_get_bv(mdl, v, val):
    """Gets the bitvector value in the node descriptor v and places it in val, returns 0 if successful, -1 otherwise."""
    return libyices.yices_val_get_bv(mdl, pointer(v), val)

# int32_t yices_val_get_scalar(model_t *mdl, const yval_t *v, int32_t *val, type_t *tau)
libyices.yices_val_get_scalar.restype = c_int32
libyices.yices_val_get_scalar.argtypes = [model_t, POINTER(yval_t), POINTER(c_int32), POINTER(type_t)]
@catch_error(-1)
def yices_val_get_scalar(mdl, v, val, tau):
    """Gets the scalar value in the node descriptor v and places it in val, returns 0 if successful, -1 otherwise."""
    return libyices.yices_val_get_scalar(mdl, pointer(v), val, tau)

# int32_t yices_val_expand_tuple(model_t *mdl, const yval_t *v, yval_t child[])
libyices.yices_val_expand_tuple.restype = c_int32
libyices.yices_val_expand_tuple.argtypes = [model_t, POINTER(yval_t), POINTER(yval_t)]
@catch_error(-1)
def yices_val_expand_tuple(mdl, v, child):
    """Stores all the children of the tuple node v in the array child, returns 0 if successful, -1 otherwise."""
    return libyices.yices_val_expand_tuple(mdl, pointer(v), child)

# int32_t yices_val_expand_function(model_t *mdl, const yval_t *f, yval_t *def, yval_vector_t *v)
libyices.yices_val_expand_function.restype = c_int32
libyices.yices_val_expand_function.argtypes = [model_t, POINTER(yval_t), POINTER(yval_t), POINTER(yval_vector_t)]
@catch_error(-1)
def yices_val_expand_function(mdl, f, df, v):
    """Stores all the mappings of the function node f in the array v, also storing the default value of f in def, returns 0 if successful, -1 otherwise."""
    return libyices.yices_val_expand_function(mdl, pointer(f), pointer(df), pointer(v))

# int32_t yices_val_expand_mapping(model_t *mdl, const yval_t *m, yval_t tup[], yval_t *val)
libyices.yices_val_expand_mapping.restype = c_int32
libyices.yices_val_expand_mapping.argtypes = [model_t, POINTER(yval_t), POINTER(yval_t), POINTER(yval_t)]
@catch_error(-1)
def yices_val_expand_mapping(mdl, m, tup, val):
    """ Expand a mapping node m, returns 0 if successful, -1 otherwise.

     - the mapping is of the form [x_1 ... x_k -> v] where k = yices_val_mapping_arity(mdl, m)
     - tup must be an array of size at least k
     - the nodes (x_1 ... x_k) are stored in tup[0 ... k-1]
       the node v is stored in val.
    """
    return libyices.yices_val_expand_mapping(mdl, pointer(m), tup, pointer(val))


#
# CHECK THE VALUE OF BOOLEAN FORMULAS
#

# int32_t yices_formula_true_in_model(model_t *mdl, term_t f)
libyices.yices_formula_true_in_model.restype = c_int32
libyices.yices_formula_true_in_model.argtypes = [model_t, term_t]
@catch_error(-1)
def yices_formula_true_in_model(mdl, f):
    """Checks whether the formula f is true in the model, returns 1 if f is true, 0 if f is false, and -1 otherwise."""
    return libyices.yices_formula_true_in_model(mdl, f)


# int32_t yices_formulas_true_in_model(model_t *mdl, uint32_t n, const term_t f[])
libyices.yices_formulas_true_in_model.restype = c_int32
libyices.yices_formulas_true_in_model.argtypes = [model_t, c_int32, POINTER(term_t)]
@catch_error(-1)
def yices_formulas_true_in_model(mdl, n, f):
    """Checks whether the array of formulas of length n are all true in the model.

    formulas_true_in_model(mdl, n, f):
     - the returned value is as in the previous function:
         1 if all f[i] are true
         0 if one f[i] is false (and f[0 ... i-1] are all true)
        -1 if one f[i] can't be evaluated (and f[0 ... i-1] are all true)

     Error codes:
     - same as yices_get_bool_value

     NOTE: if n>1, it's more efficient to call this function once than to
     call formula_true_in_mode n times.
    """
    return libyices.yices_formula_true_in_model(mdl, n, f)

#
# CONVERSION OF VALUES TO CONSTANT TERMS
#

# term_t yices_get_value_as_term(model_t *mdl, term_t t)
libyices.yices_get_value_as_term.restype = term_t
libyices.yices_get_value_as_term.argtypes = [model_t, term_t]
@catch_error(-1)
def yices_get_value_as_term(mdl, t):
    """Converts the value of term t to a constant term, or NULL_TERM if there is an error."""
    return libyices.yices_get_value_as_term(mdl, t)

# int32_t yices_term_array_value(model_t *mdl, uint32_t n, const term_t a[], term_t b[])
libyices.yices_term_array_value.restype = c_int32
libyices.yices_term_array_value.argtypes = [model_t, c_uint32, POINTER(term_t), POINTER(term_t)]
@catch_error(-1)
def yices_term_array_value(mdl, n, a, b):
    """Converts the array of terms of length n into and array on n values in the model mdl, returning 0 if successful, and -1 otherwise."""
    return libyices.yices_term_array_value(mdl, n, a, b)

#
# IMPLICANTS
#


# int32_t yices_implicant_for_formula(model_t *mdl, term_t t, term_vector_t *v)
libyices.yices_implicant_for_formula.restype = c_int32
libyices.yices_implicant_for_formula.argtypes = [model_t, term_t, POINTER(term_vector_t)]
@catch_error(-1)
def yices_implicant_for_formula(mdl, t, v):
    """Compute an implicant for t in the model mdl and store it in v, returning 0 if successful, and -1 otherwise."""
    return libyices.yices_implicant_for_formula(mdl, t, v)

# int32_t yices_implicant_for_formulas(model_t *mdl, uint32_t n, const term_t a[], term_vector_t *v)
libyices.yices_implicant_for_formulas.restype = c_int32
libyices.yices_implicant_for_formulas.argtypes = [model_t, c_uint32, POINTER(term_t), POINTER(term_vector_t)]
@catch_error(-1)
def yices_implicant_for_formulas(mdl, n, a, v):
    """Compute an implicant for an array of formulas in the model mdl and store it in v, returning 0 if successful, and -1 otherwise."""
    return libyices.yices_implicant_for_formulas(mdl, n, a, v)


#
# MODEL GENERALIZATION
#

# int32_t yices_generalize_model(model_t *mdl, term_t t, uint32_t nelims, const term_t elim[],
libyices.yices_generalize_model.restype = c_int32
libyices.yices_generalize_model.argtypes = [model_t, term_t, c_uint32, POINTER(term_t), yices_gen_mode_t, POINTER(term_vector_t)]
@catch_error(-1)
def yices_generalize_model(mdl, t, nelims, elim, mode, v):
    """Computes a generalization of the model mdl for the formula t, placing it in v, returning 0 if successful, and -1 otherwise.

    - nelims = number of variables to eliminate
    - elim = variables to eliminate
    - each term in elim[i] must be an uninterpreted term (as returned by yices_new_uninterpreted_term)
      of one of the following types: Boolean, (bitvector k), or Real
    - mode defines the generalization algorithm
    - v: term_vector to return the result
    """
    return libyices.yices_generalize_model(mdl, t, nelims, elim, mode, v)

# int32_t yices_generalize_model_array(model_t *mdl, uint32_t n, const term_t a[], uint32_t nelims, const term_t elim[], yices_gen_mode_t mode, term_vector_t *v)
libyices.yices_generalize_model_array.restype = c_int32
libyices.yices_generalize_model_array.argtypes = [model_t, c_uint32, POINTER(term_t), c_uint32, POINTER(term_t), yices_gen_mode_t, POINTER(term_vector_t)]
@catch_error(-1)
def yices_generalize_model_array(mdl, n, a, nelims, elim, mode, v):
    """Compute a generalization of mdl for the conjunct of the formulas in the array, placing it in v, returning 0 if successful, and -1 otherwise."""
    return libyices.yices_generalize_model_array(mdl, n, a, nelims, elim, mode, v)

########################
#  PRETTY PRINTING     #
########################


# int32_t yices_pp_type_fd(int fd, type_t tau, uint32_t width, uint32_t height, uint32_t offset)
libyices.yices_pp_type_fd.restype = c_int32
libyices.yices_pp_type_fd.argtypes = [c_int, type_t, c_uint32, c_uint32, c_uint32]
@catch_error(-1)
def yices_pp_type_fd(fd, tau, width, height, offset):
    """Pretty print the type tau to the file descriptor fd, returning 0 on success, -1 on failure.

                     <----------- width ------------->
                      _______________________________
    <---- offset --->|                               |   ^
                     |                               |   |
                     |                               | Height
                     |                               |   |
                     |                               |   v
                      -------------------------------
    """
    return libyices.yices_pp_type_fd(fd, tau, width, height, offset)

# int32_t yices_pp_term_fd(int fd, term_t t, uint32_t width, uint32_t height, uint32_t offset)
libyices.yices_pp_term_fd.restype = c_int32
libyices.yices_pp_term_fd.argtypes = [c_int, term_t, c_uint32, c_uint32, c_uint32]
@catch_error(-1)
def yices_pp_term_fd(fd, t, width, height, offset):
    """Pretty print the term t to the file descriptor fd, returning 0 on success, -1 on failure.

                     <----------- width ------------->
                      _______________________________
    <---- offset --->|                               |   ^
                     |                               |   |
                     |                               | Height
                     |                               |   |
                     |                               |   v
                      -------------------------------
    """
    return libyices.yices_pp_term_fd(fd, t, width, height, offset)

# int32_t yices_pp_term_array_fd(int fd, uint32_t n, const term_t a[],
#                                uint32_t witdh, uint32_t height, uint32_t offset, int32_t horiz)
libyices.yices_pp_term_array_fd.restype = c_int32
libyices.yices_pp_term_array_fd.argtypes = [c_int, c_uint32, POINTER(term_t), c_uint32, c_uint32, c_uint32, c_int32]
@catch_error(-1)
def yices_pp_term_array_fd(fd, n, a, width, height, offset, horiz):
    """Pretty print an array of terms."""
    return libyices.yices_pp_term_array_fd(fd, n, a, width, height, offset, horiz)

# void yices_print_model_fd(int fd, model_t *mdl)
libyices.yices_print_model_fd.restype = c_int32
libyices.yices_print_model_fd.argtypes = [c_int, model_t]
@catch_error(-1)
def yices_print_model_fd(fd, mdl):
    """Print a model."""
    return libyices.yices_print_model_fd(fd, mdl)


# int32_t yices_pp_model_fd(int fd, model_t *mdl, uint32_t width, uint32_t height, uint32_t offset)
libyices.yices_pp_model_fd.restype = c_int32
libyices.yices_pp_model_fd.argtypes = [c_int, model_t, c_uint32, c_uint32, c_uint32]
@catch_error(-1)
def yices_pp_model_fd(fd, mdl, width, height, offset):
    """Pretty print an model."""
    return libyices.yices_pp_model_fd(fd, mdl, width, height, offset)

# char *yices_type_to_string(type_t tau, uint32_t width, uint32_t height, uint32_t offset)
# NOTE: restype is c_void_p in order not to trigger the automatic cast, which loses the pointer
libyices.yices_type_to_string.restype = c_void_p
libyices.yices_type_to_string.argtypes = [type_t, c_uint32, c_uint32, c_uint32]
@catch_error(-1)
def yices_type_to_string(tau, width, height, offset):
    """Convert a type tau to a string using the pretty printer."""
    cstrptr = libyices.yices_type_to_string(tau, width, height, offset)
    typestr = cast(cstrptr, c_char_p).value
    libyices.yices_free_string(cstrptr)
    return typestr

# char *yices_term_to_string(term_t t, uint32_t width, uint32_t height, uint32_t offset)
# NOTE: restype is c_void_p in order not to trigger the automatic cast, which loses the pointer
libyices.yices_term_to_string.restype = c_void_p
libyices.yices_term_to_string.argtypes = [term_t, c_uint32, c_uint32, c_uint32]
@catch_error(-1)
def yices_term_to_string(t, width, height, offset):
    """Convert a term t to a string using the pretty printer."""
    cstrptr = libyices.yices_term_to_string(t, width, height, offset)
    termstr = cast(cstrptr, c_char_p).value
    libyices.yices_free_string(cstrptr)
    return termstr


# char *yices_model_to_string(model_t *mdl, uint32_t width, uint32_t height, uint32_t offset)
# NOTE: restype is c_void_p in order not to trigger the automatic cast, which loses the pointer
libyices.yices_model_to_string.restype = c_void_p
libyices.yices_model_to_string.argtypes = [model_t, c_uint32, c_uint32, c_uint32]
@catch_error(-1)
def yices_model_to_string(mdl, width, height, offset):
    """Converts a model to a string using the pretty printer."""
    cstrptr = libyices.yices_model_to_string(mdl, width, height, offset)
    mdlstr = cast(cstrptr, c_char_p).value
    libyices.yices_free_string(cstrptr)
    return mdlstr


#############################
# Gnu  Multi Precision      #
#############################


@catch_uninitialized()
def yices_new_mpz(val=None):
    """Creates a new mpz object, or None if there is an error."""
    if not hasGMP():
        return None
    new_mpz_ = mpz_t()
    libgmp.__gmpz_init(byref(new_mpz_))
    if val:
        yices_set_mpz(new_mpz_, val)
    return new_mpz_

@catch_uninitialized()
def yices_new_mpq(num=None, den=None):
    """Creates a new mpq object, or None if there is an error."""
    if not hasGMP():
        return None
    new_mpq_ = mpq_t()
    libgmp.__gmpq_init(byref(new_mpq_))
    if num:
        if den is None:
            raise TypeError('new_mpq: num and den must be given together')
        yices_set_mpq(new_mpq_, num, den)
    return new_mpq_

@catch_uninitialized()
def yices_set_mpz(vmpz, val):
    """Sets the value of an existing mpz object."""
    if not hasGMP():
        return None
    if isinstance(val, basestring):
        ret = libgmp.__gmpz_set_str(byref(vmpz), val, 0)
        if ret == -1:
            raise TypeError('set_mpz: val is an invalid integer string: '
                            'should be decimal or start with 0x (hex), 0b (binary), or 0 (octal)')
    elif isinstance(val, (int, long)):
        libgmp.__gmpz_set_si(byref(vmpz), val)
    else:
        raise TypeError('set_mpz: val should be a string or integer')

@catch_uninitialized()
def yices_set_mpq(vmpq, num, den):
    """Sets the value of an existing mpz object."""
    if not hasGMP():
        return None
    if isinstance(num, basestring):
        if isinstance(den, basestring):
            ret = libgmp.__gmpq_set_str(byref(vmpq), num +'/'+ den, 0)
            if ret == -1:
                raise TypeError('set_mpq: num or den is an invalid integer string: '
                                'should be decimal or start with 0x (hex), 0b (binary), or 0 (octal)')
        else:
            raise TypeError('set_mpq: num and den should both be strings or integers')
    elif isinstance(num, (int, long)):
        if isinstance(den, (int, long)):
            libgmp.__gmpq_set_si(byref(vmpq), num, den)
        else:
            raise TypeError('set_mpq: num and den should both be strings or integers')
    else:
        raise TypeError('set_mpq: num and den should both be strings or integers')
    libgmp.__gmpq_canonicalize(byref(vmpq))
