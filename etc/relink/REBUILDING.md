# Rebuilding the libraries used by the relink kit

These are recipient instructions, not a requirement for installing or using
Yices. They use the published dependency sources and this kit's application
objects. You may modify the libraries and recombine them with those objects.
Keep the original downloads intact and work on copies. ABI-incompatible
changes may require rebuilding Yices too, from its separately published source.
Retain the applicable notices and license texts when redistributing your work.

The ordinary compiler, operating-system headers, linker and compiler runtime
are prerequisites, not payloads in this kit. These recipes do not reproduce a
distribution's complete toolchain or promise byte-identical binaries. See
BUILDINFO and the README for the target and C++ runtime compatibility. For
Linux, the tested build/relink toolchain is matched GCC/G++ 14.2.1 with a
compatible static libstdc++, including the glibc recipe below. Native macOS
needs the command-line developer tools for the kit's architecture. Do not
replace your system C library, use sudo, or install into an existing prefix.

## 1. Obtain and authenticate the material for your binary

Obtain the complete publication set (or the corresponding-source/relink
download links) for the same release as your binary. In addition to the
matching platform kit, the recipes below use:

* `RELEASE-INPUTS` and `RELEASE-INPUTS.sha256`;
* `gmp-6.3.0.tar.xz`;
* `libpoly-c342ff1ad2f0.tar.gz`;
* on Linux, `glibc-2.28-251.el8_10.40.src.rpm`.

Verify the outer `SHA256SUMS` against the complete downloaded asset set, using
`sha256sum --check --strict SHA256SUMS` on Linux or
`shasum -a 256 -c SHA256SUMS` on macOS. Obtain the manifest's checksum through
the trusted release channel; a checksum file alone does not authenticate its
publisher. Verify `./verify-manifest.sh` in the extracted kit before changes.
The SRPM hash pins the exact distribution source; RPM signature authentication
is a separate publisher/key check, not performed by the helper below.

Set these absolute paths for your own downloads and kit (replace the examples):

```sh
YICES_ASSETS=/path/to/verified-release-assets
YICES_KIT=/path/to/extracted/yices-2.8.0-relink-kit
# Choose a writable parent on a filesystem with several GB free.
YICES_REBUILD=$(mktemp -d /path/to/writable-parent/yices-libraries.XXXXXX)
export YICES_ASSETS YICES_KIT YICES_REBUILD
```

Use paths without whitespace for dependency source/build directories: the
upstream GMP and glibc build systems do not support every such path. The kit
itself and ordinary relink output may still be in whitespace-containing paths.
All prefixes and logs below are within this newly created workspace.

## 2. Rebuild GMP and LibPoly, with your changes

Prerequisites: Bash (3.2 or later), compatible C and C++ compilers, GNU m4,
make, cmake, ctest, ninja, tar and xz. This helper requires GNU m4. GMP needs
a suitable m4 for assembly builds and, on x86-64, even with assembly disabled.
Install prerequisites through your normal administrator
process if unavailable; this recipe never installs them. Use the same target
architecture as the kit, not translated macOS execution.

Choose the compiler pair explicitly and retain the same selection for the
build and relink commands. CC, CXX and M4 must each name one executable without
whitespace, not a command with extra arguments: upstream GMP splits these
values. The helper resolves each selection to an absolute executable path in
the caller's directory and fixes relative/empty PATH entries there before any
build changes directory. A relative selection such as toolbin/gcc therefore
continues to name the same tool. Missing tools or whitespace in the selection
or its resolved directory are rejected before creating the build directory.
Replace the Linux example paths with your installed
compatible GCC/G++ pair; on macOS use the matching native Apple tools:

```sh
# Linux example (see the toolchain compatibility discussion above):
CC=/path/to/compatible/gcc
CXX=/path/to/compatible/g++
# macOS instead: CC=/usr/bin/clang; CXX=/usr/bin/clang++
export CC CXX
# Normally GNU m4 is named m4 on PATH. If necessary, select its actual path:
# M4=/path/to/gnu/m4; export M4
```

```sh
tar -xf "$YICES_ASSETS/gmp-6.3.0.tar.xz" -C "$YICES_REBUILD"
tar -xf "$YICES_ASSETS/libpoly-c342ff1ad2f0.tar.gz" -C "$YICES_REBUILD"
# Make your intended source changes in the two extracted directories now.
# CC and CXX above select the same toolchain for all following commands.
"$YICES_KIT/rebuild-gmp-libpoly.sh" \
  "$YICES_REBUILD/gmp-6.3.0" "$YICES_REBUILD/libpoly-c342ff1ad2f0" \
  "$YICES_REBUILD/libraries" 4
```

The script builds/tests/installs only into new private prefixes. GMP's normal
x86-64 build enables its fat CPU dispatch; the Linux normal archive is non-PIC
and the macOS normal archive is PIC. The separate PIC recipe disables assembly
and uses `-O2 -fPIC` for portability. Native arm64's normal build uses PIC with
its native assembly. LibPoly builds both `libpoly.a` and `libpicpoly.a`, with
its Python API disabled, using the private PIC GMP. It runs GMP's `make check`
for each build and LibPoly's CTest suite. Logs remain in `libraries/`; if any
command fails, the helper prints the failing phase and log path. Stop and
inspect those logs. Do not reuse a failed work directory
without understanding and recording what changed.

The recipe is a compatible replacement build, not a claim to duplicate all
production options. The production arguments are separately recorded in
BUILDINFO. You can use other compatible library build procedures.

```sh
CC="$CC" GMP_A="$YICES_REBUILD/libraries/gmp-normal/lib/libgmp.a" \
LIBPOLY_A="$YICES_REBUILD/libraries/libpoly/lib/libpoly.a" \
  "$YICES_KIT/relink-executables.sh" "$YICES_REBUILD/modified-executables"
CC="$CC" GMP_A="$YICES_REBUILD/libraries/gmp-pic/lib/libgmp.a" \
LIBPOLY_A="$YICES_REBUILD/libraries/libpoly/lib/libpicpoly.a" \
  "$YICES_KIT/relink-library.sh" "$YICES_REBUILD/modified-library"
```

No `SKIP_VERIFY=1` is needed: the kit is unchanged and the replacement archives
are external. Only intentional edits inside the kit require a manifest override.
On macOS the scripts ad hoc sign their new outputs. This does not notarize them.

Test all outputs before using them. For example:

```sh
"$YICES_REBUILD/modified-executables/yices" --version
printf '(set-logic QF_LIA)\n(assert (= 1 1))\n(check-sat)\n' |
  "$YICES_REBUILD/modified-executables/yices-smt2"
printf '(set-logic QF_NRA)\n(declare-fun x () Real)\n(assert (= (* x x) 2))\n(check-sat)\n' |
  "$YICES_REBUILD/modified-executables/yices-smt2" --mcsat
```

Both solve checks should report `sat`. Run an API client against the rebuilt
shared library too, using the matching binary archive's headers and the
README's runtime-library-path instructions. To establish that your replacement
was selected, use a controlled, observable change in the library and exercise
that code path. A version banner or checksum alone does not prove every path.
`yices-sat` uses neither GMP nor LibPoly, so replacing just these libraries does
not change its numerical library inputs.

## 3. Linux only: rebuild the patched glibc source without installing it

The four published Linux executables incorporate glibc statically. The Yices
shared library instead uses the system C library dynamically. Do not inject a
custom glibc into an existing process or overwrite your host's libraries.

The Linux kit provides `prepare-glibc-source.py` and `relink-with-glibc.sh`.
Preparation requires Python 3, `rpm2cpio`, GNU patch and xz support in Python.
Building glibc also requires its documented GNU make, GCC, binutils, gawk,
bison and Linux kernel-header prerequisites (see its INSTALL file).

```sh
python3 "$YICES_KIT/prepare-glibc-source.py" \
  "$YICES_ASSETS/glibc-2.28-251.el8_10.40.src.rpm" "$YICES_REBUILD/glibc-source"
```

This helper accepts only the exact published SRPM. It converts its payload,
preserves the spec and patches, unpacks glibc 2.28 and applies all 1,096 patches
with `-p1`, sorted by their numeric Patch identifiers. This is not an RPM
macro interpreter: the spec declares Patch52 before Patch47--51. For this
exact pinned SRPM, numeric and declaration order were checked to produce
identical patched source bytes, excluding backup files. The helper deliberately
retains patch's `.orig` backup files as evidence; they are not build inputs.
It checks the patched locale list and records `PATCHES-APPLIED.json`.
It executes neither an RPM installation
nor package scriptlets/macros. It is deliberately not a general RPM builder.
The source tree is `glibc-source/glibc-2.28`; make your changes there.

For example, a harmless local experiment is adding a distinctive stderr marker
to `__printf` in `stdio-common/printf.c`. Keep this demonstration change out of
normal deployment; it is only a way to observe a replaced runtime code path.

```sh
mkdir "$YICES_REBUILD/glibc-build"
cd "$YICES_REBUILD/glibc-build"
# Retain the explicit compatible Linux CC/CXX selection from section 2.
# The local recipient proof used matched GCC/G++ 14.2.1.
"$YICES_REBUILD/glibc-source/glibc-2.28/configure" \
  CC="$CC" CXX="$CXX" CFLAGS=-O2 \
  --prefix="$YICES_REBUILD/unused-glibc-prefix" \
  --disable-werror --disable-profile --disable-crypt --enable-kernel=3.2.0
make -j4
# No make install: all subsequent inputs come from this build directory.
CC="$CC" \
  "$YICES_KIT/relink-with-glibc.sh" "$YICES_REBUILD/glibc-build" \
  "$YICES_REBUILD/modified-glibc-executables"
```

The last helper uses `-nostdlib -static -no-pie`, explicitly names your glibc's
`crt1.o`, `crti.o`, `crtn.o`, `libc.a`, `libm.a` and `libpthread.a`, and asks the
selected GCC for its own `crtbeginT.o`, `crtend.o`, `libgcc.a`, `libgcc_eh.a`
and `libstdc++.a`. It creates one linker map per executable. The compiler
runtime remains a normal prerequisite; these archives are not silently taken
from a second relink kit. The helper does not promise that arbitrary C library
versions or ABI changes will work. You may also construct your own link command
using the supplied application objects and appropriate startup/runtime inputs.

To combine the rebuilt glibc with your modified GMP and LibPoly from section 2,
pass their external archives explicitly and choose another new output directory:

```sh
CC="$CC" GMP_A="$YICES_REBUILD/libraries/gmp-normal/lib/libgmp.a" \
LIBPOLY_A="$YICES_REBUILD/libraries/libpoly/lib/libpoly.a" \
  "$YICES_KIT/relink-with-glibc.sh" "$YICES_REBUILD/glibc-build" \
  "$YICES_REBUILD/modified-all-libraries-executables"
```

The glibc helper always verifies the unchanged kit and does not accept
SKIP_VERIFY as a bypass. Keep replacement archives external for this route.
If you previously edited deps/, use a freshly extracted, verified kit.

Inspect the four `.map` files and run the version/solve checks above against
`modified-glibc-executables` (plus a small DIMACS case with `yices-sat`). Confirm
your observed marker, not merely the absence of a link error. Validate your
modified glibc with its own applicable tests before deploying it: this recipe's
relink demonstration is not certification of a replacement operating-system
runtime. It never installs or replaces the host glibc.

## Distribution and access

The binary and corresponding source/application-object material belong to the
same release. Every binary recipient must have the required source/relink
access, even if they download only the smaller platform archive. Sending source
to a different reviewer group does not by itself provide that access. The
publisher must supply the matching links and retain the required availability;
this document does not turn a technical test into legal sign-off.
