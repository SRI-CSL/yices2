:tocdepth: 2

.. highlight:: c

.. _version_data:

Version Information
===================

The following macros are defined in :file:`yices.h`. They can be
used at compile time for checking the Yices version.

.. c:macro:: __YICES_VERSION

   Version number

.. c:macro:: __YICES_VERSION_MAJOR

   Revision number

.. c:macro:: __YICES_VERSION_PATCHLEVEL
 
   Patch level

For Yices 2.5.0, they are defined as follows::

   #define __YICES_VERSION            2
   #define __YICES_VERSION_MAJOR      5
   #define __YICES_VERSION_PATCHLEVEL 0

The same information is available in the following constant string.

.. c:var:: const char* yices_version

   Version as a string.

   The string includes the version number, followed by the revision
   number and the patch level, as in ``"2.5.0"``.

More details are given by three constant strings:

.. c:var:: const char* yices_build_arch

   Build architecture. 

   This is a string like ``"x86_64-unknown-linux-gnu"`` that
   specifies the processor and operating system for which the Yices
   library was built.

.. c:var:: const char* yices_build_mode

   Build mode.

   Typical values are ``"release"`` for a normal build, or ``"debug"``
   if the library was built with debug symbols.

.. c:var:: const char* yices_build_date

   Build date.

   This string uses the format ``"Year-Month-Day"``, as in ``"2015-12-11"``.
