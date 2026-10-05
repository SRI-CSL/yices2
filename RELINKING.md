# Relinking Yices

You do not need this to install or run Yices. If you want to use Yices,
download a binary distribution from <https://yices.csl.sri.com> or build from
source, and ignore this file.

## Why this exists

Some of the libraries built into the Yices binaries are distributed under the
GNU Lesser General Public License. That license gives you the right to modify
those libraries and rebuild the Yices programs against your modified version.

We publish the material you need to do that for GMP and LibPoly, as a separate
download called the relink kit. It does not cover the C library case, and the
next section says what that leaves to the machine you relink on. This file
says what the kit is and where to get it. The kit's own README has the
instructions.

## Which libraries

| Library | Where it is built in |
|---|---|
| GNU C Library | The four Linux command-line executables. Not the Linux shared library, which loads the system copy at run time. Not the macOS builds, which use the system C library |
| GMP | `yices`, `yices-smt`, `yices-smt2`, and the shared library, on every platform. Not `yices-sat` |
| LibPoly | The same set as GMP |

The scripts automate the GMP and LibPoly cases. They do not automate the C
library case. There is no script input for a libc archive, and none for
startup object files or a sysroot, so the link takes the C library and the
startup files from the machine you run it on. The kit's `README` says the same
under "What this kit does not do".

Other libraries in the build, namely CUDD, CaDiCaL, Kissat, and
CryptoMiniSat, are distributed under permissive terms that carry no relinking
requirement.

The published shared libraries statically incorporate GMP, LibPoly, CUDD,
CaDiCaL, Kissat, and CryptoMiniSat, and their current links export those
libraries' global symbols alongside the Yices API. A process that loads
libyices together with another copy of one of those libraries can silently
interpose one copy's symbols on the other; dynamic linking does not isolate
them. Only the interfaces declared in the installed Yices headers are Yices
public API. Do not call or rely on the exported dependency symbols.

The `NOTICES` file in the Yices 2.8.0 source archive, three binary archives,
and three relink kits identifies third-party components, where they came from,
and the terms their own authors distribute them under where the repository
evidence establishes them, and records the gap where it does not.

## Where to get the kit

The relink kit is published as a release asset on the GitHub release, next to
the binary archives:

<https://github.com/SRI-CSL/yices2/releases>

There is one kit for each published binary archive. Each kit's `BUILDINFO`
names the archive it corresponds to and records that archive's SHA-256. The
source for the libraries above is published as release assets on the same
release, including the complete distribution source package for the C library
that was built in.

## What is in it

- The Yices object code, for both the command-line executables and the shared
  library. On Linux these are two payloads compiled with different options. On
  macOS the dynamic-library payload contains exactly the subset of the same
  objects used by the production dynamic-library rule. In both cases the two
  payloads are not interchangeable.
- The dependency archives used in the official build, with checksums.
- Scripts that relink the published object code against the archives in the
  kit. They build their link command from their own defaults, which are close
  to the recorded production values but not identical to them. The kit's
  `README` lists every difference.
- The toolchain, flags, and link order that produced the published binaries,
  as recorded in a file called `BUILDINFO`.
- The license texts and notices for the components the kit redistributes.

## How to use it

Unpack the kit and read its `README`. In outline:

```sh
./verify-manifest.sh          # check the download is intact
                              # then replace a library in deps/
./relink-executables.sh       # rebuild the command-line tools
./relink-library.sh           # rebuild the shared library
```

Two things the kit's README explains and that are easy to get wrong. The Linux
and Apple Silicon kits contain two different builds of GMP, one for the
executables and one for the shared library, and they cannot be swapped. The
Intel macOS kit instead uses one fat, position-independent GMP archive for
both links. And `yices-sat` is linked differently from the other three tools,
so a change to GMP or LibPoly does not affect it.

## A relinked binary will not match the shipped one byte for byte

This is expected and does not mean anything went wrong. Each output carries a
build identifier that changes whenever the output changes, a GNU BuildID on
Linux and an LC_UUID on macOS, so any difference at all produces a different
one. The Linux release build also compiles with
`-ffile-prefix-map`, which rewrites source paths recorded in the object files.
That flag affects compilation, not linking, so it has already done its work by
the time the kit's object files exist and there is nothing for a relink to
reproduce. What you should compare against is `BUILDINFO`, which records, for
each output, a link command assembled from the same variables the production
rules used. It is not a capture of the command line the linker received. Treat
it as the reference command. The kit's scripts build their command from their
own defaults, which differ from the recorded values. The kit's `README` lists
the differences and says which of them a setting can close. Some of them no
setting closes, because they follow from where you unpacked the kit and where
you sent the output. If your link uses the same inputs in the same order as
the reference command and the binary runs, the relink has done its job.

## Reporting a problem

If the published materials do not let you rebuild a binary, that is a defect
and we want to know. Open an issue at
<https://github.com/SRI-CSL/yices2/issues> with the output of
`verify-manifest.sh`, the contents of `BUILDINFO`, and the command that
failed.
