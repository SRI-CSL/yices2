#!/usr/bin/env python3
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
"""Fast recipient-helper control tests; fixtures are NOT actual library builds.

Run with TMPDIR on a suitable scratch filesystem. Each test preserves its small
fixture directory so a failure can be inspected. Real library build/relink
proofs require the documented compilers and dependency sources separately.
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

HELPER = Path(__file__).resolve().parents[2] / "etc/relink/rebuild-gmp-libpoly.sh"


def script(path, body):
    path.write_text("#!/bin/bash\nset -eu\n" + body + "\n")
    path.chmod(0o755)


class RecipientRebuild(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp(prefix="yices-recipient-control-"))
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.gmp = self.root / "gmp"
        self.poly = self.root / "poly"
        self.gmp.mkdir()
        self.poly.mkdir()
        self.work = self.root / "libraries"
        self.env = {key: value for key, value in os.environ.items()
                    if key not in ("CC", "CXX", "M4", "BASH_ENV", "ENV", "FAIL_STEP")}
        self.env.update(PATH=str(self.bin), LC_ALL="C", TEST_PLATFORM="Linux", TEST_ARCH="x86_64")
        for name in ("mkdir", "dirname", "basename"):
            (self.bin / name).symlink_to(shutil.which(name))
        script(self.bin / "uname", 'if [[ $1 == -s ]]; then echo "$TEST_PLATFORM"; else echo "$TEST_ARCH"; fi')
        for name in ("cc", "c++"):
            script(self.bin / name, "exit 0")
        script(self.bin / "m4", 'echo "m4 (GNU M4) fixture"')
        script(self.gmp / "configure", '''
case "$PWD:${FAIL_STEP:-}" in
  */gmp-normal-build:gmp-normal-configure) echo 'fixture configure failure'; exit 73;;
esac
prefix=
for arg; do case "$arg" in --prefix=*) prefix=${arg#--prefix=};; esac; done
printf '%s\\n' "$prefix" > fixture-prefix
printf 'CC=%s CXX=%s M4=%s DEPLOY=%s\\n' "$CC" "$CXX" "$M4" "${MACOSX_DEPLOYMENT_TARGET:-NONE}"
''')
        (self.poly / "CMakeLists.txt").write_text("# fixture only\n")
        script(self.bin / "make", '''
case "$PWD:${FAIL_STEP:-}:$*" in
  */gmp-pic-build:gmp-pic-make:*) echo 'fixture make failure'; exit 74;;
esac
if [[ $1 == install ]]; then
  IFS= read -r prefix < fixture-prefix
  mkdir -p "$prefix/lib"
  printf 'fixture archive\\n' > "$prefix/lib/libgmp.a"
fi
''')
        script(self.bin / "cmake", '''
case "$1" in
  -S)
    [[ ${FAIL_STEP:-} != libpoly-configure ]] || { echo 'fixture cmake failure'; exit 75; }
    build= prefix=
    while [[ $# -gt 0 ]]; do
      case "$1" in -B) shift; build=$1;; -DCMAKE_INSTALL_PREFIX=*) prefix=${1#*=};; esac
      shift
    done
    mkdir -p "$build"
    printf '%s\\n' "$prefix" > "$build/fixture-prefix";;
  --build)
    [[ ${FAIL_STEP:-} != libpoly-build ]] || { echo 'fixture build failure'; exit 76; };;
  --install)
    [[ ${FAIL_STEP:-} != libpoly-install ]] || { echo 'fixture install failure'; exit 78; }
    IFS= read -r prefix < "$2/fixture-prefix"
    mkdir -p "$prefix/lib"
    printf 'fixture archive\\n' > "$prefix/lib/libpoly.a"
    printf 'fixture archive\\n' > "$prefix/lib/libpicpoly.a";;
  *) exit 90;;
esac
''')
        script(self.bin / "ctest", '[[ ${FAIL_STEP:-} != libpoly-test ]] || { echo "fixture test failure"; exit 77; }')
        script(self.bin / "ninja", "exit 0")

    def run_helper(self, **updates):
        env = dict(self.env, **updates)
        result = subprocess.run(["/bin/bash", str(HELPER), str(self.gmp), str(self.poly),
                                 str(self.work), "2"], env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=15)
        (self.root / "terminal.log").write_text(result.stdout)
        return result

    def test_missing_m4_is_explicit_before_reservation(self):
        (self.bin / "m4").rename(self.bin / "not-on-path-m4")
        result = self.run_helper()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("GNU m4 is required", result.stdout)
        self.assertFalse(self.work.exists())

    def test_missing_cmake_before_reservation(self):
        (self.bin / "cmake").rename(self.bin / "not-on-path-cmake")
        result = self.run_helper()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("required tool is unavailable: cmake", result.stdout)
        self.assertFalse(self.work.exists())

    def test_nongnu_m4_is_rejected(self):
        script(self.bin / "m4", 'echo "BSD m4 fixture"')
        result = self.run_helper()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("did not identify GNU M4", result.stdout)
        self.assertFalse(self.work.exists())

    def test_failing_m4_version_is_rejected(self):
        script(self.bin / "m4", "exit 9")
        result = self.run_helper()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("--version failed", result.stdout)
        self.assertFalse(self.work.exists())

    def test_external_m4_and_compiler_selection(self):
        override = self.root / "gnu m4"
        (self.bin / "m4").rename(override)
        result = self.run_helper(M4=str(override), CC=str(self.bin / "cc"), CXX=str(self.bin / "c++"))
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("PASS: recipient", result.stdout)
        log = (self.work / "gmp-normal.log").read_text()
        self.assertIn("M4=" + str(override), log)
        self.assertIn("CC=" + str(self.bin / "cc"), log)

    def test_compiler_must_be_one_executable(self):
        result = self.run_helper(CC="cc --unrequested-flags")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("CC/CXX must each name one executable", result.stdout)
        self.assertFalse(self.work.exists())

    def test_gmp_normal_failure_preserves_status_and_log(self):
        result = self.run_helper(FAIL_STEP="gmp-normal-configure")
        self.assertEqual(result.returncode, 73, result.stdout)
        self.assertIn("GMP normal", result.stdout)
        self.assertIn(str(self.work / "gmp-normal.log"), result.stdout)
        self.assertIn("fixture configure failure", (self.work / "gmp-normal.log").read_text())
        self.assertFalse((self.work / "gmp-pic-build").exists())

    def test_gmp_pic_failure_preserves_status_and_log(self):
        result = self.run_helper(FAIL_STEP="gmp-pic-make")
        self.assertEqual(result.returncode, 74, result.stdout)
        self.assertIn("GMP pic", result.stdout)
        self.assertIn(str(self.work / "gmp-pic.log"), result.stdout)

    def test_libpoly_failure_phases(self):
        for phase, status in (("configure", 75), ("build", 76), ("test", 77), ("install", 78)):
            with self.subTest(phase=phase):
                self.work = self.root / ("libraries-" + phase)
                result = self.run_helper(FAIL_STEP="libpoly-" + phase)
                self.assertEqual(result.returncode, status, result.stdout)
                self.assertIn("LibPoly", result.stdout)
                self.assertIn(str(self.work / "libpoly.log"), result.stdout)
                self.assertIn("partial workspace preserved", result.stdout)

    def test_existing_work_is_not_changed(self):
        self.work.mkdir()
        (self.work / "keep").write_text("original\n")
        result = self.run_helper()
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(list(self.work.iterdir()), [self.work / "keep"])
        self.assertEqual((self.work / "keep").read_text(), "original\n")

    def test_supported_platform_control_branches(self):
        for platform, arch in (("Linux", "x86_64"), ("Darwin", "x86_64"), ("Darwin", "arm64")):
            with self.subTest(platform=platform, arch=arch):
                self.work = self.root / ("libraries-" + platform + "-" + arch)
                result = self.run_helper(TEST_PLATFORM=platform, TEST_ARCH=arch)
                self.assertEqual(result.returncode, 0, result.stdout)
                self.assertTrue((self.work / "libpoly/lib/libpicpoly.a").is_file())
                if platform == "Darwin":
                    self.assertIn("DEPLOY=11.0", (self.work / "gmp-normal.log").read_text())


if __name__ == "__main__":
    unittest.main(verbosity=2)
