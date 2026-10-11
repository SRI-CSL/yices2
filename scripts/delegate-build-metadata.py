#!/usr/bin/env python3
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
"""Omit host identity from generated CaDiCaL/Kissat build metadata.

Canonical source scripts remain byte-unchanged. Only the configured makefile
recipe is redirected through this checked generator; every regeneration uses
the same rule, including make test. This is a release build transformation,
not an upstream source export or a binary rewrite.
"""
import argparse
import hashlib
import os
from pathlib import Path
import re
import shlex
import stat
import subprocess
import sys
import tempfile

PROFILE = "yices-delegate-metadata-v1"
COMPONENTS = {
    "cadical": ("make-build-header.sh", "build.hpp", "DATE",
                "d08d2b1c7a81cbc1a0c1a7c26e84aad9b759c562d343d80e1971de8955142f8a"),
    "kissat": ("generate-build-header.sh", "build.h", "BUILD",
               "6a5e1d5ed086f548d6f95f248207a7df4c2d2254040737bf9f75b240d05aeab0"),
}
OLD_UNAME = b'OS="`uname -srmn 2>/dev/null`"'
NEW_UNAME = b'OS="`uname -srm 2>/dev/null`"'
LEGACY_BANNER = re.compile(
    rb'(?:Mon|Tue|Wed|Thu|Fri|Sat|Sun) [^\x00\r\n]{0,512} '
    rb'(?:Linux|Darwin) [^ \x00\r\n]+ [0-9][^ \x00\r\n]* '
    rb'(?:x86_64|arm64|aarch64)(?: |\x00)')


def require(value, message):
    if not value:
        raise ValueError(message)


def regular(path):
    require(stat.S_ISREG(path.lstat().st_mode), "not a direct regular file: " + str(path))
    data = path.read_bytes()
    require(data, "empty file: " + str(path))
    return data


def marker(component):
    return "[" + PROFILE + ":" + component + "; hostname=not-recorded]"


def generator(component, build):
    name, _, _, digest = COMPONENTS[component]
    path = build.parent / "scripts" / name
    data = regular(path)
    require(hashlib.sha256(data).hexdigest() == digest,
            "canonical generator hash differs: " + str(path))
    require(data.count(OLD_UNAME) == 1, "expected one canonical uname invocation")
    return path, data


def prepare(component, build):
    build = Path(build).resolve(strict=True)
    generator(component, build)
    makefile = build / "makefile"
    original = regular(makefile)
    name, header, _, _ = COMPONENTS[component]
    destination = "build.hpp" if component == "cadical" else "$@"
    old = ("\t../scripts/" + name + " > " + destination + "\n").encode()
    require(original.count(old) == 1, "expected one unchanged generated header recipe")
    command = [str(Path(sys.executable).absolute()), "-I", "-B", str(Path(__file__).resolve()),
               "generate", component]
    # Make expands dollar signs even in shell quotes. The controlled release
    # workflow paths must be representable without a make expansion or newline.
    require(all(not any(c in value for c in "$\r\n") for value in command),
            "metadata generator path is unsafe for a make recipe")
    new = ("\t" + " ".join(shlex.quote(arg) for arg in command) + " > " + destination + "\n").encode()
    fd, temporary = tempfile.mkstemp(prefix=".release-metadata-", dir=build)
    with os.fdopen(fd, "wb") as stream:
        stream.write(original.replace(old, new))
    os.chmod(temporary, stat.S_IMODE(makefile.stat().st_mode))
    os.replace(temporary, makefile)
    print("prepared " + PROFILE + ": " + component + "/" + header)


def generate(component):
    path, data = generator(component, Path.cwd())
    transformed = data.replace(OLD_UNAME, NEW_UNAME)
    result = subprocess.run(["/bin/sh", "-c", transformed.decode(), str(path)],
                            stdout=subprocess.PIPE, check=False)
    require(result.returncode == 0, "upstream metadata generator failed: exit " + str(result.returncode))
    field = COMPONENTS[component][2].encode()
    pattern = re.compile(rb'^#define ' + field + rb' "([^"\r\n]*)"$', re.M)
    matches = list(pattern.finditer(result.stdout))
    require(len(matches) == 1 and b"\\" not in matches[0][1], "unexpected generated metadata field")
    match = matches[0]
    replacement = b'#define ' + field + b' "' + match[1] + b' ' + marker(component).encode() + b'"'
    output = result.stdout[:match.start()] + replacement + result.stdout[match.end():]
    require(not LEGACY_BANNER.search(output), "generated field still has a legacy hostname banner")
    sys.stdout.buffer.write(output)


def check_files(component, paths):
    host = os.uname().nodename.encode()
    require(host and b"\x00" not in host, "cannot identify current producer hostname")
    host_token = re.compile(rb'(?<![A-Za-z0-9_.-])' + re.escape(host) + rb'(?![A-Za-z0-9_.-])')
    for name in paths:
        data = regular(Path(name))
        require(not host_token.search(data), "compiled payload contains current host identity: " + str(name))
        require(not LEGACY_BANNER.search(data), "compiled payload has a legacy hostname banner: " + str(name))
        if component == "any":
            require(any(marker(key).encode() in data for key in COMPONENTS),
                    "compiled payload lacks normalized delegate metadata: " + str(name))
        elif component != "none":
            require(marker(component).encode() in data,
                    "compiled payload lacks normalized " + component + " metadata: " + str(name))
    print("PASS: " + PROFILE + "; " + str(len(paths)) + " compiled payloads; " + component)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    operations = parser.add_subparsers(dest="operation", required=True)
    for operation in ("prepare", "generate"):
        command = operations.add_parser(operation)
        command.add_argument("component", choices=COMPONENTS)
        if operation == "prepare":
            command.add_argument("build_directory")
    command = operations.add_parser("check")
    command.add_argument("component", choices=[*COMPONENTS, "any", "none"])
    command.add_argument("files", nargs="+")
    args = parser.parse_args()
    if args.operation == "prepare":
        prepare(args.component, args.build_directory)
    elif args.operation == "generate":
        generate(args.component)
    else:
        check_files(args.component, args.files)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, UnicodeError) as error:
        print("delegate-build-metadata: ERROR: " + str(error), file=sys.stderr)
        raise SystemExit(1)
