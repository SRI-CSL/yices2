#!/usr/bin/env python3
# Copyright (c) 2026, SRI International
# SPDX-License-Identifier: BSD-3-Clause

"""Test the regression scripts without building Yices (Python 3 required).

Run: python3 tests/unit/test_regress_harness.py

All fixtures live in a private TemporaryDirectory under TMPDIR. The fake
solvers test orchestration, not SMT correctness. The two parallel fixtures
exercise the GNU/moreutils argument protocols with concurrent subprocesses;
they do not certify either external parallel implementation. An installed
parallel can be exercised separately with real regression suites.
"""

from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest


SCRIPT = Path(__file__).resolve()
REGRESS = SCRIPT.parents[1] / "regress"
BASH = shutil.which("bash")


def event(kind, **values):
    data = json.dumps(dict(kind=kind, time=time.monotonic(), **values)) + "\n"
    fd = os.open(os.environ["HARNESS_EVENTS"], os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    try:
        os.write(fd, data.encode())
    finally:
        os.close(fd)


def fixture(kind, args):
    """Private fixture entry points, reached only by scripts we create."""
    if kind == "solver":
        unavailable = os.environ.get("HARNESS_UNSUPPORTED", "").split(",")
        for argument in args:
            delegate = argument[len("--delegate="):] if argument.startswith("--delegate=") else argument
            if delegate in unavailable or argument in unavailable:
                return 1
        if not args or args[-1].startswith("--"):
            return 0  # feature probe, not a test execution
        source = Path(args[-1]).read_text()
        if "; wait-for-signal" in source:
            for number in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
                signal.signal(number, signal.SIG_DFL)
            event("solver-wait", test=args[-1])
            time.sleep(20)  # the bounded signal probe must stop us first
        if "; require-option" in source and "--fixture-option" not in args:
            return 8
        if "; mode-specific" in source and "--mcsat" in args:
            print("unsat")
        else:
            print("sat")
        if "; exit-130" in source:
            return 130  # ordinary solver failure, not a caught signal
        if "; fail" in source or (os.environ.get("HARNESS_DELEGATE_FAIL") and "--delegate=cadical" in args):
            return 9
        return 0

    if kind == "worker":
        # check.sh invokes bash run_test.sh [options] TEST BIN OUT.
        test, _, output = args[-3:]
        fault = os.environ.get("HARNESS_WORKER_FAULT", "") if Path(test).stem == "fault" else ""
        event("worker", test=test, fault=fault)
        if fault == "exit-before":
            return 7
        if fault == "silent-before":
            return 0
        if fault == "killed-before":
            os.kill(os.getpid(), signal.SIGKILL)
        status = subprocess.call([os.environ["HARNESS_BASH"], *args])
        if fault == "exit-after":
            return 7
        if fault == "delete-marker":
            for marker in Path(output).glob("*.pass"):
                if marker.read_text().splitlines()[0] == test:
                    marker.unlink()
        return status

    if kind == "mv":
        if os.environ.get("HARNESS_MARKER_FAILURE"):
            return 1
        result = subprocess.call([os.environ["HARNESS_MV"], *args])
        if result == 0 and os.environ.get("HARNESS_TRACE_MARKERS"):
            marker = Path(args[-1])
            event("marker", test=marker.read_text().splitlines()[0], suffix=marker.suffix)
        return result

    if kind == "parallel":
        backend = os.environ["HARNESS_BACKEND"]
        if args == ["--version"]:
            print("GNU parallel (test protocol fixture)" if backend == "gnu" else "moreutils protocol fixture")
            return 0 if backend == "gnu" else 1
        flag, delimiter = ("-q", ":::") if backend == "gnu" else ("-i", "--")
        assert args.pop(0) == flag, args
        jobs = 4
        if args[0].startswith("-j"):
            jobs = int(args.pop(0)[2:]) or 4
        split = args.index(delimiter)
        command, inputs = args[:split], args[split + 1:]
        assert command[0] == "bash" and command.count("{}") == 1, command
        fault = os.environ.get("HARNESS_PARALLEL_FAULT", "")
        if fault == "exit-before":
            return 19
        if fault == "drop-last":
            inputs = inputs[:-1]
        if fault == "repeat-first":
            inputs[-1] = inputs[0]

        def execute(item):
            event("dispatch-start", test=item, backend=backend)
            try:
                return subprocess.call([item if arg == "{}" else arg for arg in command])
            finally:
                event("dispatch-end", test=item, backend=backend)

        with ThreadPoolExecutor(max_workers=jobs) as pool:
            statuses = list(pool.map(execute, inputs))
        if fault == "exit-after":
            return 19
        if fault == "hide-status":
            return 0
        return int(any(status != 0 for status in statuses))
    raise AssertionError(kind)


class HarnessTests(unittest.TestCase):
    backends = ("serial", "gnu", "more")
    invocations = dict.fromkeys(backends, 0)

    def setUp(self):
        previous_directory = Path.cwd()
        self.temp = tempfile.TemporaryDirectory(prefix="yices-harness-test-")
        self.addCleanup(self.temp.cleanup)
        self.addCleanup(os.chdir, previous_directory)
        self.root = Path(self.temp.name)
        os.chdir(self.root)
        self.scripts = self.root / "scripts with spaces"
        self.scripts.mkdir()
        for name in ("check.sh", "run_test.sh"):
            shutil.copyfile(REGRESS / name, self.scripts / name)
        self.tmp = self.root / "tmp"
        self.tmp.mkdir()
        self.binaries = self.root / "bin"
        self.binaries.mkdir()
        for name in ("yices_smt2", "yices_smtcomp", "yices"):
            self.wrapper(self.binaries / name, "solver")
        self.cases = self.root / "cases"
        self.cases.mkdir()
        self.events = self.root / "events.jsonl"
        self.env = dict(os.environ)
        for key in tuple(self.env):
            if key.startswith(("REGRESS_", "HARNESS_")) or key in (
                "MAKEFLAGS", "MFLAGS", "BASH_ENV", "ENV", "SHELLOPTS", "BASHOPTS",
                "PYTHONPATH", "PYTHONHOME", "TIME_LIMIT", "CDPATH",
            ):
                del self.env[key]
        self.env.update(TMPDIR=str(self.tmp), LC_ALL="C", PYTHONDONTWRITEBYTECODE="1",
                        PYTHONNOUSERSITE="1", HARNESS_BASH=BASH,
                        HARNESS_MV=shutil.which("mv"), HARNESS_EVENTS=str(self.events))
        self.tools = {}
        for backend in self.backends:
            tools = self.root / ("tools-" + backend)
            tools.mkdir()
            for name in ("basename", "mktemp", "mkdir", "cat", "rm", "grep", "sort", "cmp", "diff", "find", "sed", "tput"):
                target = shutil.which(name)
                self.assertIsNotNone(target, "required test utility: " + name)
                (tools / name).symlink_to(target)
            self.wrapper(tools / "bash", "worker")
            self.wrapper(tools / "mv", "mv")
            if backend != "serial":
                self.wrapper(tools / "parallel", "parallel")
            self.tools[backend] = tools

    @staticmethod
    def wrapper(path, kind):
        path.write_text("#!/bin/sh\nexec " + " ".join(map(shlex.quote, (
            sys.executable, "-B", str(SCRIPT), "--fixture", kind))) + ' "$@"\n')
        path.chmod(0o700)

    def case(self, name="good.smt2", gold="sat\n", content=""):
        path = self.cases / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("(set-logic QF_BV)\n(check-sat)\n" + content)
        if gold is not None:
            Path(str(path) + ".gold").write_text(gold)
        return path

    def run_command(self, args, backend, settings):
        self.invocations[backend] += 1
        env = dict(self.env, PATH=str(self.tools[backend]), HARNESS_BACKEND=backend, **settings)
        with subprocess.Popen([BASH, *map(str, args)], env=env, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, universal_newlines=True, start_new_session=True) as proc:
            try:
                output = proc.communicate(timeout=30)[0]
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                output = proc.communicate()[0]
                self.fail("harness exceeded 30 seconds:\n" + output)
        return proc.returncode, output

    def check(self, backend, paths=None, *, status=0, counts=None, directory="cases", binaries="bin", **settings):
        args = [self.scripts / "check.sh"]
        if backend != "serial":
            args.append("-j")
        args += [directory, binaries]
        args += [] if paths is None else paths
        code, output = self.run_command(args, backend, settings)
        if status == 0:
            self.assertEqual(code, 0, output)
        else:
            self.assertNotEqual(code, 0, output)
        if counts is not None:
            self.assertRegex(output, r"(?m)^Pass: {}$".format(counts[0]))
            self.assertRegex(output, r"(?m)^Fail: {}$".format(counts[1]))
        self.assertEqual(list(self.tmp.iterdir()), [], "temporary files leaked:\n" + output)
        return output

    def test_relative_absolute_and_duplicate_paths(self):
        good = self.case()
        for backend in self.backends:
            for directory in ("cases", self.cases):
                for binaries in ("bin", self.binaries):
                    with self.subTest(backend=backend, directory=directory, binaries=binaries):
                        self.check(backend, directory=directory, binaries=binaries, counts=(1, 0))
            self.check(backend, [good, good], counts=(2, 0))
            self.check(backend, ["cases/good.smt2", good], counts=(2, 0))

    def test_spaces_metacharacters_and_long_paths(self):
        name = "a directory/quoted ' $x [*] ; case.smt2"
        spaced = self.case(name)
        long_path = self.case("/".join(["long-component-" * 5] * 5) + "/long.smt2")
        special_bin = self.root / "bin with [spaces]"
        shutil.copytree(self.binaries, special_bin)
        leading = self.root / "-leading.smt2"
        leading.write_text(spaced.read_text())
        Path(str(leading) + ".gold").write_text("sat\n")
        for backend in self.backends:
            self.check(backend, ["cases/" + name, long_path, "-leading.smt2"],
                       binaries=special_bin, counts=(3, 0))
            self.check(backend, binaries=special_bin, counts=(2, 0))

    def test_missing_input_gold_and_unknown_extension(self):
        good = self.case()
        bad_inputs = [self.case("missing-gold.smt2", gold=None),
                      self.cases / "missing-input.smt2", self.case("unknown.txt")]
        for backend in self.backends:
            for bad in bad_inputs:
                for order in ([bad, good], [good, bad]):
                    with self.subTest(backend=backend, paths=order):
                        self.check(backend, order, status=1, counts=(1, 1))
            self.check(backend, status=1, counts=(1, 1))  # discovery includes missing-gold

    def test_wrong_answer_and_nonzero_solver_exit(self):
        good = self.case()
        wrong = self.case("wrong.smt2", gold="unsat\n")
        failed = self.case("failed.smt2", content="; fail\n")
        for backend in self.backends:
            for bad in (wrong, failed):
                self.check(backend, [good, bad], status=1, counts=(1, 1))

    def test_solver_exit_130_is_a_failure_not_cancellation(self):
        failed = self.case("exit-130.smt2", content="; exit-130\n")
        good = self.case()
        for backend in self.backends:
            self.check(backend, [failed, good], status=1, counts=(1, 1))

    def test_languages_and_both_modes(self):
        self.case("case.smt")
        self.case("case.ys")
        both = self.case("both/case.smt2", content="; mode-specific\n")
        Path(str(both) + ".mcsat.gold").write_text("unsat\n")
        Path(str(both) + ".dpllt.gold").write_text("sat\n")
        for backend in self.backends:
            self.check(backend, counts=(3, 0))
            Path(str(both) + ".mcsat.gold").write_text("sat\n")
            self.check(backend, status=1, counts=(2, 1))
            Path(str(both) + ".mcsat.gold").write_text("unsat\n")
            self.check(backend, counts=(2, 0), HARNESS_UNSUPPORTED="--mcsat")

    def test_worker_status_and_missing_terminal_records(self):
        good = self.case()
        bad = self.case("fault.smt2")
        for backend in self.backends:
            for fault in ("exit-before", "silent-before", "killed-before", "exit-after", "delete-marker"):
                with self.subTest(backend=backend, fault=fault):
                    output = self.check(backend, [bad, good], status=1, HARNESS_WORKER_FAULT=fault)
                    if fault == "exit-after":
                        self.assertIn("worker or dispatcher failed", output)
                    else:
                        self.assertIn("result accounting failed", output)

    def test_parallel_status_and_exact_multiset(self):
        one, two = self.case("one.smt2"), self.case("two.smt2")
        for backend in ("gnu", "more"):
            for fault in ("exit-before", "exit-after", "drop-last", "repeat-first"):
                with self.subTest(backend=backend, fault=fault):
                    output = self.check(backend, [one, two], status=1, HARNESS_PARALLEL_FAULT=fault)
                    if fault in ("drop-last", "repeat-first"):
                        self.assertIn("result accounting failed", output)
                    else:
                        self.assertIn("worker or dispatcher failed", output)
            missing_gold = self.case("missing-gold.smt2", gold=None)
            self.check(backend, [one, missing_gold], status=1, counts=(1, 1), HARNESS_PARALLEL_FAULT="hide-status")

    def test_parallel_fixture_really_dispatches_concurrently(self):
        inputs = [self.case("case%d.smt2" % n) for n in range(8)]
        for backend in ("gnu", "more"):
            if self.events.exists():
                self.events.unlink()
            self.check(backend, inputs, counts=(8, 0))
            active = peak = 0
            for entry in map(json.loads, self.events.read_text().splitlines()):
                if entry["kind"] == "dispatch-start":
                    active += 1
                    peak = max(peak, active)
                elif entry["kind"] == "dispatch-end":
                    active -= 1
            self.assertEqual(active, 0)
            self.assertGreater(peak, 1, "parallel fixture did not overlap child processes")

    def test_delegate_batches_do_not_overwrite_a_failure(self):
        self.case()
        for backend in self.backends:
            self.check(backend, counts=(4, 0), REGRESS_DELEGATE_MODE="auto")
            self.check(backend, counts=(3, 0), REGRESS_DELEGATE_MODE="only")
            self.check(backend, status=1, counts=(3, 1), REGRESS_DELEGATE_MODE="auto", HARNESS_DELEGATE_FAIL="1")
            self.check(backend, status=1, counts=(2, 1), REGRESS_DELEGATE_MODE="only", HARNESS_DELEGATE_FAIL="1")
            self.check(backend, status=1, counts=(0, 0), REGRESS_DELEGATE_MODE="only",
                       HARNESS_UNSUPPORTED="cadical,cryptominisat,kissat")

    def test_unsupported_option_delegate_is_explicitly_skipped(self):
        good = self.case()
        optional = self.case("optional.smt2")
        Path(str(optional) + ".options").write_text("--delegate=kissat\n")
        for backend in self.backends:
            output = self.check(backend, [good, optional], counts=(1, 0), HARNESS_UNSUPPORTED="kissat")
            self.assertIn("Skipping", output)
            self.check(backend, [optional], status=1, HARNESS_UNSUPPORTED="kissat")

    def test_empty_missing_and_newline_paths_fail(self):
        for backend in self.backends:
            self.check(backend, status=1)
            self.check(backend, directory="nonexistent", status=1)
            self.check(backend, binaries="nonexistent", status=1)
        self.case()
        newline = self.case("has\nnewline.smt2")
        for backend in self.backends:
            self.check(backend, [newline], status=1)
            self.check(backend, status=1)

    def test_marker_write_failure_cannot_print_pass(self):
        self.case()
        for backend in self.backends:
            output = self.check(backend, status=1, counts=(0, 0), HARNESS_MARKER_FAILURE="1")
            self.assertIn("cannot record result", output)
            self.assertNotIn("PASS [", output)

    def test_direct_worker_setup_failures_record_errors_and_clean_temps(self):
        no_gold = self.case("no-gold.smt2", gold=None)
        bad_options = self.case("bad-options.smt2")
        Path(str(bad_options) + ".options").mkdir()
        good = self.case()
        for index, (test, settings) in enumerate((
            (no_gold, {}), (bad_options, {}),
            (good, {"TMPDIR": str(self.root / "absent-tmp")}),
        )):
            output_dir = self.root / ("worker-output-%d" % index)
            output_dir.mkdir()
            code, output = self.run_command([self.scripts / "run_test.sh", test, self.binaries, output_dir], "serial", settings)
            self.assertNotEqual(code, 0, output)
            self.assertEqual(len(list(output_dir.glob("*.error"))), 1, output)
            self.assertEqual(list(output_dir.glob("*.pass")), [], output)
            self.assertEqual(list(self.tmp.iterdir()), [], output)

    def test_direct_worker_leading_dash_paths_and_sidecars(self):
        os.chdir(self.cases)
        names = ("-leading.smt2", "-leading.smt", "-leading.ys",
                 "both/-leading.smt2", "-directory/both/-leading.smt2")
        for number, name in enumerate(names):
            both = "/both/" in "/" + name
            source = self.case(name, content="; require-option\n" + ("; mode-specific\n" if both else ""))
            Path(str(source) + ".options").write_text("--fixture-option\n")
            if both:
                Path(str(source) + ".mcsat.gold").write_text("unsat\n")
                Path(str(source) + ".dpllt.gold").write_text("sat\n")
            for spelling, test in enumerate((name, "./" + name, str(source))):
                with self.subTest(test=test):
                    output_dir = self.root / ("leading-output-%d-%d" % (number, spelling))
                    output_dir.mkdir()
                    code, output = self.run_command(
                        [self.scripts / "run_test.sh", "--", test, self.binaries, output_dir], "serial", {})
                    self.assertEqual(code, 0, output)
                    markers = list(output_dir.glob("*.pass"))
                    self.assertEqual(len(markers), 1, output)
                    self.assertEqual(markers[0].read_text().splitlines()[0], test)
                    self.assertEqual(list(output_dir.glob("*.error")), [], output)
                    self.assertEqual(list(self.tmp.iterdir()), [], output)

    def signal_command(self, args, number, *, require_record=True):
        """Use real bash dispatch; a Python worker wrapper changes SIGINT semantics."""
        tools = self.root / "signal-tools"
        if not tools.exists():
            tools.mkdir()
            for tool in self.tools["serial"].iterdir():
                (tools / tool.name).symlink_to(BASH if tool.name == "bash" else tool)
        if self.events.exists():
            self.events.unlink()
        # A forced batch termination may remove the result directory before
        # a worker records its failure. Keep each probe's temporary files
        # separate so that cleanup races cannot contaminate the next probe.
        signal_tmp = self.root / ("signal-tmp-%d" % self.invocations["serial"])
        signal_tmp.mkdir()
        env = dict(self.env, PATH=str(tools), TMPDIR=str(signal_tmp), HARNESS_TRACE_MARKERS="1")

        def reset_signals():
            # A backgrounded invoking shell may have inherited SIG_IGN.
            # Model an interactive user's ordinary foreground process group.
            for caught in (signal.SIGINT, signal.SIGQUIT, signal.SIGTERM, signal.SIGHUP):
                signal.signal(caught, signal.SIG_DFL)

        def events():
            if not self.events.exists():
                return []
            # Ignore an incomplete final line while another process appends.
            return [json.loads(line) for line in self.events.read_text().splitlines(keepends=True)
                    if line.endswith("\n")]

        self.invocations["serial"] += 1
        proc = subprocess.Popen(list(map(str, args)), env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, universal_newlines=True,
                                start_new_session=True, preexec_fn=reset_signals)
        try:
            deadline = time.monotonic() + 10
            while (not any(item["kind"] == "solver-wait" for item in events()) and
                   proc.poll() is None and time.monotonic() < deadline):
                time.sleep(0.02)
            self.assertIsNone(proc.poll(), "probe stopped before its solver was ready")
            self.assertTrue(any(item["kind"] == "solver-wait" for item in events()),
                            "probe never reached its solver")
            os.killpg(proc.pid, number)
            try:
                output = proc.communicate(timeout=5)[0]
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                output = proc.communicate(timeout=5)[0]
                self.fail("signal did not promptly stop the run:\n" + output)
        finally:
            # Only the process group created above; never signal an existing job.
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait(timeout=5)
        seen = events()
        self.assertNotEqual(proc.returncode, 0, output)
        self.assertNotIn("PASS [", output)
        self.assertEqual(sum(item["kind"] == "solver-wait" for item in seen), 1,
                         "an interrupted batch dispatched another test:\n" + output)
        markers = [item for item in seen if item["kind"] == "marker"]
        self.assertLessEqual(len(markers), 1, output)
        for marker in markers:
            self.assertEqual(marker["suffix"], ".error", output)
        if require_record:
            self.assertEqual(len(markers), 1, output)
            self.assertEqual(list(signal_tmp.iterdir()), [], output)
        return proc.returncode, output, markers

    def test_signals_stop_serial_batches_directly_and_under_make(self):
        make = shutil.which("make")
        self.assertIsNotNone(make, "make is required for the interrupt integration probe")
        tests = [self.case("wait%d.smt2" % n, content="; wait-for-signal\n") for n in range(4)]
        command = [BASH, self.scripts / "check.sh", self.cases, self.binaries, *tests]
        makefile = self.root / "interrupt.mk"
        makefile.write_text(".PHONY: check\ncheck:\n\t" +
                            " ".join(shlex.quote(str(arg)) for arg in command) + "\n")
        for number in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            for launcher in (command, [make, "-s", "-f", makefile, "check"]):
                with self.subTest(signal=number, launcher=launcher[0]):
                    # Unlike bash's cooperative SIGINT wait, TERM/HUP can
                    # start the parent's cleanup before its worker exits.
                    # They must stop promptly, without claiming a PASS; a
                    # temporary marker need not survive that cleanup race.
                    _, _, markers = self.signal_command(
                        launcher, number, require_record=(number == signal.SIGINT))
                    for marker in markers:
                        self.assertEqual(marker["test"], str(tests[0]))

    def test_signalled_worker_records_error_then_terminates_by_signal(self):
        test = self.case(content="; wait-for-signal\n")
        for number in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            with self.subTest(signal=number):
                output_dir = self.root / ("signal-output-%d" % number)
                output_dir.mkdir()
                code, output, markers = self.signal_command(
                    [BASH, self.scripts / "run_test.sh", test, self.binaries, output_dir], number)
                self.assertEqual(code, -number, output)
                self.assertEqual(markers[0]["test"], str(test))
                self.assertEqual(len(list(output_dir.glob("*.error"))), 1, output)
                self.assertEqual(list(output_dir.glob("*.pass")), [], output)


if __name__ == "__main__":
    if sys.argv[1:2] == ["--fixture"]:
        sys.exit(fixture(sys.argv[2], sys.argv[3:]))
    program = unittest.main(verbosity=2, exit=False)
    print("Harness/worker invocations by dispatch fixture: " + json.dumps(HarnessTests.invocations, sort_keys=True))
    sys.exit(not program.result.wasSuccessful())
