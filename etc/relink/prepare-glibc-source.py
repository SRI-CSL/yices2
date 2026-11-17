#!/usr/bin/env python3
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
"""Prepare the release's exact patched glibc source, without installing an RPM.

Usage: python3 prepare-glibc-source.py glibc-2.28-251.el8_10.40.src.rpm NEW-DIRECTORY
Requires Python 3, rpm2cpio, GNU patch. Never writes outside NEW-DIRECTORY.
This supports this exact SRPM, not arbitrary spec-file interpretation.
"""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys
import tarfile

RPM_SHA = "1524e3ce370f4b194f3fc0402f9ab5263a760cb3c3ee973a5bd2965532380642"
SPEC_SHA = "be13059ea210e82ea41f8c535065ddbedbe3e950ccb8487330aff8d80b798ee6"
TAR_SHA = "b1900051afad76f7a4f73e71413df4826dce085ef8ddb785a945b66d7d513082"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    require(len(sys.argv) == 3, __doc__)
    rpm, dest = map(Path, sys.argv[1:])
    require(rpm.is_file() and not rpm.is_symlink() and digest(rpm) == RPM_SHA,
            "SRPM does not match the exact published release input")
    require(not dest.exists() and not dest.is_symlink(), "destination already exists")
    # Conversion only: no RPM installation, scriptlet, spec macro or network.
    payload = subprocess.check_output(["rpm2cpio", str(rpm.resolve())])
    dest.mkdir()
    dest = dest.resolve()
    sources = dest / "srpm"
    sources.mkdir()
    offset, count = 0, 0
    while True:
        header = payload[offset:offset + 110]
        require(len(header) == 110 and header[:6] == b"070701", "unsupported CPIO header")
        fields = [int(header[i:i + 8], 16) for i in range(6, 110, 8)]
        mode, size, namesize = fields[1], fields[6], fields[11]
        start = offset + 110
        raw_name = payload[start:start + namesize]
        require(raw_name.endswith(b"\0"), "invalid CPIO name")
        name = raw_name[:-1].decode("utf-8")
        offset = (start + namesize + 3) & ~3
        if name == "TRAILER!!!":
            break
        require(name == Path(name).name and name not in ("", ".", "..")
                and stat.S_ISREG(mode), "unsafe/non-regular SRPM member: " + name)
        data = payload[offset:offset + size]
        require(len(data) == size, "truncated CPIO member")
        with (sources / name).open("xb") as out:
            out.write(data)
        (sources / name).chmod(mode & 0o777)
        offset = (offset + size + 3) & ~3
        count += 1
    require(count == 1106, "unexpected SRPM member count")
    specfile = sources / "glibc.spec"
    require(digest(specfile) == SPEC_SHA, "unexpected glibc.spec")
    archive = sources / "glibc-2.28.tar.xz"
    require(digest(archive) == TAR_SHA, "unexpected upstream glibc tarball")
    spec = specfile.read_text()
    require("%autosetup -n %{glibcsrcdir} -p1" in spec, "unexpected prep contract")
    patches = sorted((int(n), p) for n, p in re.findall(r"^Patch(\d+): (\S+)\s*$", spec, re.M))
    require(len(patches) == len({n for n, _ in patches}) == 1096, "unexpected patch series")
    with tarfile.open(archive) as tar:
        names = set()
        for member in tar.getmembers():
            path = PurePosixPath(member.name)
            require(path.parts[0] == "glibc-2.28" and ".." not in path.parts
                    and not path.is_absolute() and member.name not in names,
                    "unsafe/duplicate glibc tar member")
            require(member.isfile() or member.isdir() or member.issym() or member.islnk(),
                    "unsupported glibc tar member type")
            if member.issym() or member.islnk():
                target = (PurePosixPath(member.name).parent / member.linkname
                          if member.issym() else PurePosixPath(member.linkname))
                normalized = os.path.normpath(str(target))
                require(normalized == "glibc-2.28" or normalized.startswith("glibc-2.28/"),
                        "escaping glibc tar link")
            names.add(member.name)
        tar.extractall(dest)
    tree = dest / "glibc-2.28"
    applied = []
    for number, name in patches:
        require(name == Path(name).name, "nonliteral patch name")
        patch = sources / name
        print("Applying Patch%d: %s" % (number, name), flush=True)
        subprocess.run(["patch", "--batch", "--forward", "-p1", "-i", str(patch)],
                       cwd=tree, check=True)
        applied.append(dict(number=number, file=name, sha256=digest(patch)))
    # Relevant additional %prep actions. Keep .orig backup evidence instead of
    # deleting it; it is not a build input. No installed-system files are used.
    for file in list((tree / "benchtests/scripts").glob("*.py")) + [tree / "scripts/pylint"]:
        file.chmod(file.stat().st_mode | 0o111)
    for file in list(tree.rglob("configure")) + list((tree / "locale/programs").glob("*-kw.h")):
        file.touch()
    require((sources / "SUPPORTED").read_bytes() == (tree / "localedata/SUPPORTED").read_bytes(),
            "patched locale list does not match the SRPM's SOURCE11")
    (dest / "PATCHES-APPLIED.json").write_text(json.dumps(dict(
        srpm_sha256=RPM_SHA, spec_sha256=SPEC_SHA, source_sha256=TAR_SHA,
        patches=applied), indent=2) + "\n")
    print("Prepared", tree, "with all 1096 distribution patches; nothing installed.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError, tarfile.TarError) as error:
        raise SystemExit("prepare-glibc-source: ERROR: " + str(error))
