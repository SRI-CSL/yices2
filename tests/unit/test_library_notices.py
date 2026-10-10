#!/usr/bin/env python3
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
"""Compile the actual frontend notice functions, with and without MCSAT.

Run from any directory with Python 3 and a C compiler (CC is one executable).
Only temporary test outputs are written; TMPDIR selects their filesystem.
"""
import os
from pathlib import Path
import re
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    cases = [
        ("frontend/yices/yices_reval.c", "print_version", "stdout"),
        ("frontend/yices_smt2.c", "print_version", ""),
        ("frontend/yices_smt.c", "print_version", ""),
        ("frontend/yices_smtcomp.c", "print_version", ""),
        ("frontend/yices_smt.c", "print_yices_header", "stdout"),
        ("frontend/yices_smtcomp.c", "print_yices_header", "stdout"),
    ]
    header = '#include <stdio.h>\n#include "frontend/common/library_notices.h"\n'
    for name in ("yices_version", "gmp_version", "yices_build_date", "yices_build_arch", "yices_build_mode", "yices_rev"):
        header += 'const char *const ' + name + ' = "test-value";\n'
    notices = ["LibPoly source-file notices (MCSAT support):",
               "Copyright 2015, SRI International.", "Copyright 2024, SRI International.",
               "LibPoly u_memstream: Copyright 2020 Lag Free Games, LLC"]
    count = 0
    with tempfile.TemporaryDirectory(prefix="yices-notices-") as directory:
        directory = Path(directory)
        for i, (path, function, args) in enumerate(cases):
            text = (root / "src" / path).read_text()
            pattern = r"static void " + function + r"\([^\n]*\) \{\n.*?^\}"
            matches = re.findall(pattern, text, re.S | re.M)
            assert len(matches) == 1, (path, function)
            assert '#include "frontend/common/library_notices.h"' in text
            code = header + matches[0] + "\nint main(void) { " + function + "(" + args + "); return 0; }\n"
            source = directory / (str(i) + ".c")
            source.write_text(code)
            for enabled in (False, True):
                binary = directory / (str(i) + "-" + str(enabled))
                command = [os.environ.get("CC", "cc"), "-std=c99", "-Wall", "-Wextra", "-Werror",
                           "-I" + str(root / "src"), str(source), "-o", str(binary)]
                if enabled:
                    command.append("-DHAVE_MCSAT")
                subprocess.run(command, check=True)
                output = subprocess.check_output([str(binary)], text=True)
                assert "Copyright (c) 2026, SRI International." in output
                assert "Copyright Free Software Foundation, Inc" in output
                assert "GNU Lesser General Public" in output and "GNU General Public License" in output
                for notice in notices:
                    assert output.count(notice) == int(enabled), (path, function, enabled, notice)
                count += 1
        for name in ("yices_sat.c", "yices_sat_new.c"):
            assert "YICES_LIBPOLY_NOTICES" not in (root / "src/frontend" / name).read_text()
    print("PASS:", count, "actual display-function/feature combinations; SAT frontends unaffected")


if __name__ == "__main__":
    main()
