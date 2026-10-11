#!/usr/bin/env python3
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause
"""Fast recipient-helper control tests; fixtures are NOT actual library builds.

Run with TMPDIR on a suitable scratch filesystem. Each test preserves its small
fixture directory so a failure can be inspected. Real library build/relink
proofs require the documented compilers and dependency sources separately.
Release preflights run these controls with /bin/bash and preserve the helper
and test hashes, tool identities and complete output. PASS is fixture coverage,
not proof that dependencies were rebuilt on the reported target platform.
"""
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys
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
                    if key not in ("CC", "CXX", "M4", "BASH_ENV", "ENV", "FAIL_STEP",
                                   "OMIT_ARCHIVE", "EMPTY_ARCHIVE", "MAKE_ACTION_LOG",
                                   "FIXTURE_ACTION_PREFIX", "MACOSX_DEPLOYMENT_TARGET")}
        self.env.update(PATH=str(self.bin), LC_ALL="C", TEST_PLATFORM="Linux", TEST_ARCH="x86_64")
        for name in ("mkdir", "dirname", "basename"):
            (self.bin / name).symlink_to(shutil.which(name))
        script(self.bin / "uname", 'if [[ $1 == -s ]]; then echo "$TEST_PLATFORM"; else echo "$TEST_ARCH"; fi')
        for name in ("cc", "c++"):
            script(self.bin / name, "exit 0")
        script(self.bin / "m4", 'echo "m4 (GNU M4) fixture"')
        script(self.gmp / "configure", '''
printf '%s\\0' "$@" > fixture-args
case "$PWD:${FAIL_STEP:-}" in
  */gmp-normal-build:gmp-normal-configure) echo 'fixture configure failure'; exit 73;;
esac
prefix=
for arg; do case "$arg" in --prefix=*) prefix=${arg#--prefix=};; esac; done
printf '%s\\n' "$prefix" > fixture-prefix
printf 'CC=%s CXX=%s M4=%s DEPLOY=%s\\n' "$CC" "$CXX" "$M4" "${MACOSX_DEPLOYMENT_TARGET:-NONE}"
"$CC" --version
"$CXX" --version
"$M4" --version
''')
        (self.poly / "CMakeLists.txt").write_text("# fixture only\n")
        script(self.bin / "make", '''
printf '%s|%s\\n' "${PWD##*/}" "$*" >> "$MAKE_ACTION_LOG"
case "$PWD:${FAIL_STEP:-}:$*" in
  */gmp-pic-build:gmp-pic-make:*) echo 'fixture make failure'; exit 74;;
  */gmp-normal-build:gmp-normal-check:*-j\\ 2\\ check) echo 'fixture check failure'; exit 79;;
  */gmp-pic-build:gmp-pic-check:*-j\\ 2\\ check) echo 'fixture check failure'; exit 80;;
esac
if [[ $1 == install ]]; then
  IFS= read -r prefix < fixture-prefix
  mkdir -p "$prefix/lib"
  output=${prefix##*/}/lib/libgmp.a
  if [[ ${OMIT_ARCHIVE:-} != "$output" ]]; then
    if [[ ${EMPTY_ARCHIVE:-} == "$output" ]]; then
      : > "$prefix/lib/libgmp.a"
    else
      printf 'fixture archive\\n' > "$prefix/lib/libgmp.a"
    fi
  fi
fi
''')
        script(self.bin / "cmake", '''
case "$1" in -S) operation=configure;; --build) operation=build;; --install) operation=install;; *) exit 90;; esac
printf '%s\\0' "$@" > "$FIXTURE_ACTION_PREFIX-cmake-$operation.args"
printf 'CC=%s CXX=%s DEPLOY=%s\\n' "$CC" "$CXX" "${MACOSX_DEPLOYMENT_TARGET:-NONE}" > "$FIXTURE_ACTION_PREFIX-cmake-$operation.env"
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
    for archive in libpoly.a libpicpoly.a; do
      output=libpoly/lib/$archive
      if [[ ${OMIT_ARCHIVE:-} != "$output" ]]; then
        if [[ ${EMPTY_ARCHIVE:-} == "$output" ]]; then
          : > "$prefix/lib/$archive"
        else
          printf 'fixture archive\\n' > "$prefix/lib/$archive"
        fi
      fi
    done;;
  *) exit 90;;
esac
''')
        script(self.bin / "ctest", '''
printf '%s\\0' "$@" > "$FIXTURE_ACTION_PREFIX-ctest.args"
[[ ${FAIL_STEP:-} != libpoly-test ]] || { echo "fixture test failure"; exit 77; }
''')
        script(self.bin / "ninja", "exit 0")

    def run_helper(self, source_arguments=None, work_argument=None, jobs="2", **updates):
        self.make_log = self.root / (self.work.name + "-make-actions.log")
        self.action_prefix = str(self.root / self.work.name)
        env = dict(self.env, MAKE_ACTION_LOG=str(self.make_log),
                   FIXTURE_ACTION_PREFIX=self.action_prefix, **updates)
        sources = source_arguments or [str(self.gmp), str(self.poly)]
        result = subprocess.run(["/bin/bash", str(HELPER), *sources,
                                 work_argument or str(self.work), jobs], env=env, text=True, cwd=self.root,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=15)
        (self.root / (self.work.name + "-terminal.log")).write_text(result.stdout)
        return result

    def arguments(self, path):
        data = Path(path).read_bytes()
        self.assertTrue(data.endswith(b"\0"), repr(data))
        return data[:-1].decode().split("\0")

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
        override = self.root / "gnu-m4"
        (self.bin / "m4").rename(override)
        result = self.run_helper(M4=str(override), CC=str(self.bin / "cc"), CXX=str(self.bin / "c++"))
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("PASS: recipient", result.stdout)
        log = (self.work / "gmp-normal.log").read_text()
        self.assertIn("M4=" + str(override), log)
        self.assertIn("CC=" + str(self.bin / "cc"), log)
        self.assertIn("CXX=" + str(self.bin / "c++"), log)

    def test_whitespace_tool_paths_fail_before_reservation(self):
        for variable, executable in (("CC", "cc"), ("CXX", "c++"), ("M4", "m4")):
            for index, whitespace in enumerate((" ", "\t", "\n", "\r", "\v", "\f")):
                with self.subTest(variable=variable, whitespace=repr(whitespace)):
                    override = self.root / (variable + whitespace + "tool")
                    shutil.copy2(self.bin / executable, override)
                    self.work = self.root / ("libraries-" + variable + "-" + str(index))
                    result = self.run_helper(**{variable: str(override)})
                    self.assertEqual(result.returncode, 1, result.stdout)
                    self.assertIn(variable + " must name one executable without whitespace", result.stdout)
                    self.assertIn("input and prerequisite checks failed", result.stdout)
                    self.assertNotIn("partial workspace preserved", result.stdout)
                    self.assertNotIn("PASS: recipient", result.stdout)
                    self.assertFalse(self.work.exists())
                    self.assertFalse(self.make_log.exists())

    def test_compiler_must_be_one_executable(self):
        result = self.run_helper(CC="cc --unrequested-flags")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("CC must name one executable without whitespace", result.stdout)
        self.assertFalse(self.work.exists())

    def test_relative_tools_are_absolute_before_changing_directory(self):
        (self.root / "toolbin").symlink_to(self.bin, target_is_directory=True)
        for prefix in ("bin/", "./bin/", "toolbin/", "bin/../bin/"):
            with self.subTest(prefix=prefix):
                self.work = self.root / ("libraries-relative-" + str(len(list(self.root.glob('libraries-relative-*')))))
                result = self.run_helper(CC=prefix + "cc", CXX=prefix + "c++", M4=prefix + "m4")
                self.assertEqual(result.returncode, 0, result.stdout)
                for variant in ("normal", "pic"):
                    log = (self.work / ("gmp-" + variant + ".log")).read_text()
                    for variable, tool in (("CC", "cc"), ("CXX", "c++"), ("M4", "m4")):
                        self.assertIn(variable + "=" + str(self.bin / tool), log)

    def test_relative_and_empty_path_entries_remain_bound_to_caller(self):
        for name in ("cc", "c++", "m4"):
            (self.root / name).symlink_to(self.bin / name)
        for index, selection in enumerate(("bin", "./bin", "bin:", ":bin", ".:bin", str(self.bin) + ":bin")):
            with self.subTest(path=selection):
                self.work = self.root / ("libraries-path-" + str(index))
                result = self.run_helper(PATH=selection)
                self.assertEqual(result.returncode, 0, result.stdout)
                expected = self.root if selection.startswith((":", ".:")) else self.bin
                log = (self.work / "gmp-pic.log").read_text()
                self.assertIn("CC=" + str(expected / "cc"), log)
                self.assertIn("M4=" + str(expected / "m4"), log)
                self.assertIn("gmp-pic-build|-j 2 check", self.make_log.read_text())

    def test_resolved_tool_directory_with_whitespace_is_rejected(self):
        actual = self.root / "tool directory"
        actual.mkdir()
        for name in ("cc", "c++", "m4"):
            shutil.copy2(self.bin / name, actual / name)
        (self.root / "alias").symlink_to(actual, target_is_directory=True)
        for variable, name in (("CC", "cc"), ("CXX", "c++"), ("M4", "m4")):
            with self.subTest(variable=variable):
                self.work = self.root / ("libraries-alias-" + variable)
                result = self.run_helper(**{variable: "alias/" + name})
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn(variable + " must name one executable without whitespace", result.stdout)
                self.assertFalse(self.work.exists())

    def test_missing_relative_tools_fail_before_reservation(self):
        for variable in ("CC", "CXX", "M4"):
            with self.subTest(variable=variable):
                result = self.run_helper(**{variable: "missing/tool"})
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn("input and prerequisite checks failed", result.stdout)
                self.assertFalse(self.work.exists())
                self.assertFalse(self.make_log.exists())

    def test_unsupported_platforms_fail_before_reservation(self):
        for platform, arch in (("Linux", "aarch64"), ("Darwin", "i386"), ("FreeBSD", "x86_64")):
            with self.subTest(platform=platform, arch=arch):
                result = self.run_helper(TEST_PLATFORM=platform, TEST_ARCH=arch)
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn("recipe supports Linux", result.stdout)
                self.assertFalse(self.work.exists())

    def test_whitespace_build_paths_fail_before_reservation(self):
        self.work = self.root / "space in work"
        result = self.run_helper()
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("require paths without whitespace", result.stdout)
        self.assertFalse(self.work.exists())

    def test_relative_source_and_work_paths_remain_in_caller_directory(self):
        result = self.run_helper(source_arguments=["gmp", "./poly"], work_argument="libraries")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertTrue((self.work / "gmp-pic/lib/libgmp.a").is_file())
        self.assertIn(str(self.work), result.stdout)

    def test_dangling_work_symlink_is_not_followed_or_replaced(self):
        target = self.root / "not-created"
        self.work.symlink_to(target, target_is_directory=True)
        result = self.run_helper()
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertTrue(self.work.is_symlink())
        self.assertEqual(self.work.readlink(), target)
        self.assertFalse(target.exists())

    def test_gmp_normal_failure_preserves_status_and_log(self):
        result = self.run_helper(FAIL_STEP="gmp-normal-configure")
        self.assertEqual(result.returncode, 73, result.stdout)
        self.assertIn("GMP normal configure/build/check/install failed (exit 73)", result.stdout)
        self.assertIn(str(self.work / "gmp-normal.log"), result.stdout)
        self.assertIn("fixture configure failure", (self.work / "gmp-normal.log").read_text())
        self.assertFalse((self.work / "gmp-pic-build").exists())

    def test_gmp_pic_failure_preserves_status_and_log(self):
        result = self.run_helper(FAIL_STEP="gmp-pic-make")
        self.assertEqual(result.returncode, 74, result.stdout)
        self.assertIn("GMP pic configure/build/check/install failed (exit 74)", result.stdout)
        self.assertIn(str(self.work / "gmp-pic.log"), result.stdout)

    def test_both_gmp_checks_run_once_before_installation(self):
        result = self.run_helper()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(self.make_log.read_text().splitlines(), [
            variant + "|" + action
            for variant in ("gmp-normal-build", "gmp-pic-build")
            for action in ("-j 2", "-j 2 check", "install")])

    def test_gmp_check_failures_stop_before_installation(self):
        for variant, status in (("normal", 79), ("pic", 80)):
            with self.subTest(variant=variant):
                self.work = self.root / ("libraries-check-" + variant)
                result = self.run_helper(FAIL_STEP="gmp-" + variant + "-check")
                self.assertEqual(result.returncode, status, result.stdout)
                self.assertIn("GMP " + variant + " configure/build/check/install failed (exit " +
                              str(status) + ")", result.stdout)
                self.assertIn(str(self.work / ("gmp-" + variant + ".log")), result.stdout)
                actions = self.make_log.read_text().splitlines()
                self.assertEqual(actions[-1], "gmp-" + variant + "-build|-j 2 check")
                self.assertNotIn("gmp-" + variant + "-build|install", actions)
                self.assertFalse((self.work / ("gmp-" + variant)).exists())
                self.assertFalse((self.work / "libpoly-build").exists())
                self.assertNotIn("PASS: recipient", result.stdout)

    def test_libpoly_failure_phases(self):
        for phase, status, label in (("configure", 75, "LibPoly configure"),
                                     ("build", 76, "LibPoly build"),
                                     ("test", 77, "LibPoly tests"),
                                     ("install", 78, "LibPoly installation into the new private prefix")):
            with self.subTest(phase=phase):
                self.work = self.root / ("libraries-" + phase)
                result = self.run_helper(FAIL_STEP="libpoly-" + phase)
                self.assertEqual(result.returncode, status, result.stdout)
                self.assertIn(label + " failed (exit " + str(status) + ")", result.stdout)
                self.assertIn(str(self.work / "libpoly.log"), result.stdout)
                self.assertIn("partial workspace preserved", result.stdout)
                self.assertNotIn("PASS: recipient", result.stdout)

    def test_missing_or_empty_output_archives_are_rejected(self):
        for setting in ("OMIT_ARCHIVE", "EMPTY_ARCHIVE"):
            for index, archive in enumerate(("gmp-normal/lib/libgmp.a", "gmp-pic/lib/libgmp.a",
                                             "libpoly/lib/libpoly.a", "libpoly/lib/libpicpoly.a")):
                with self.subTest(setting=setting, archive=archive):
                    self.work = self.root / ("libraries-output-" + setting + "-" + str(index))
                    result = self.run_helper(**{setting: archive})
                    self.assertEqual(result.returncode, 1, result.stdout)
                    self.assertIn("missing output: " + str(self.work / archive), result.stdout)
                    self.assertIn("output archive verification failed (exit 1)", result.stdout)
                    self.assertIn("partial workspace preserved", result.stdout)
                    self.assertNotIn("PASS: recipient", result.stdout)

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
                normal_options = (["--enable-fat", "--without-pic"] if platform == "Linux" else
                                  ["--enable-fat", "--with-pic"] if arch == "x86_64" else ["--with-pic"])
                for variant in ("normal", "pic"):
                    options = normal_options if variant == "normal" else ["--disable-assembly", "--with-pic"]
                    flags = "-O2" if platform == "Linux" and variant == "normal" else "-O2 -fPIC"
                    self.assertEqual(self.arguments(self.work / ("gmp-" + variant + "-build/fixture-args")),
                                     ["--prefix=" + str(self.work / ("gmp-" + variant)),
                                      "--disable-shared", "--enable-static", "--enable-cxx", *options,
                                      "CFLAGS=" + flags, "CXXFLAGS=" + flags])
                    deploy = "11.0" if platform == "Darwin" else "NONE"
                    self.assertIn("DEPLOY=" + deploy, (self.work / ("gmp-" + variant + ".log")).read_text())
                self.assertEqual(self.arguments(self.action_prefix + "-cmake-configure.args"), [
                    "-S", str(self.poly), "-B", str(self.work / "libpoly-build"), "-G", "Ninja",
                    "-DCMAKE_BUILD_TYPE=Release", "-DCMAKE_INSTALL_PREFIX=" + str(self.work / "libpoly"),
                    "-DCMAKE_C_FLAGS=-O2", "-DCMAKE_CXX_FLAGS=-O2",
                    "-DGMP_INCLUDE_DIR=" + str(self.work / "gmp-pic/include"),
                    "-DGMP_LIBRARY=" + str(self.work / "gmp-pic/lib/libgmp.a"),
                    "-DLIBPOLY_BUILD_PYTHON_API=OFF", "-DLIBPOLY_BUILD_STATIC=ON",
                    "-DLIBPOLY_BUILD_STATIC_PIC=ON", "-DBUILD_TESTING=ON"])
                self.assertEqual(self.arguments(self.action_prefix + "-cmake-build.args"),
                                 ["--build", str(self.work / "libpoly-build"), "--parallel", "2"])
                self.assertEqual(self.arguments(self.action_prefix + "-ctest.args"),
                                 ["--test-dir", str(self.work / "libpoly-build"), "--output-on-failure", "-j", "2"])
                self.assertEqual(self.arguments(self.action_prefix + "-cmake-install.args"),
                                 ["--install", str(self.work / "libpoly-build")])
                environment = Path(self.action_prefix + "-cmake-configure.env").read_text()
                self.assertIn("CC=" + str(self.bin / "cc"), environment)
                self.assertIn("CXX=" + str(self.bin / "c++"), environment)
                self.assertIn("DEPLOY=" + deploy, environment)


if __name__ == "__main__":
    print("Recipient-helper controls: fixtures only, not actual dependency builds.", flush=True)
    print("helper-sha256: " + hashlib.sha256(HELPER.read_bytes()).hexdigest(), flush=True)
    print("tests-sha256: " + hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), flush=True)
    print("python: " + sys.version.splitlines()[0], flush=True)
    print("bash: " + subprocess.check_output(["/bin/bash", "--version"], text=True).splitlines()[0], flush=True)
    program = unittest.main(verbosity=2, exit=False)
    if not program.result.wasSuccessful() or program.result.testsRun == 0 or program.result.skipped:
        raise SystemExit(1)
    print("PASS: recipient-helper controls; " + str(program.result.testsRun) + " tests; fixtures only", flush=True)
