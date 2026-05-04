#!/usr/bin/env python3

#
# This file is part of the Yices SMT Solver.
# Copyright (C) 2025 SRI International.
#
# Yices is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# Yices is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with Yices.  If not, see <http://www.gnu.org/licenses/>.
#

import subprocess
import threading
import sys
import os
import signal
import shutil
import time
import argparse
import random
from typing import List

_active_solver = None

def _global_signal_handler(signum, frame):
    if signum == signal.SIGINT:
        print("\nReceived Ctrl+C, shutting down gracefully...", file=sys.stderr)
    else:
        print(f"\nReceived signal {signum}, shutting down gracefully...", file=sys.stderr)
    if _active_solver is not None:
        _active_solver.cleanup_threads()
    sys.exit(0)


def generate_configs(num_configs: int, seed: int = None, use_l2o: bool = False) -> List[List[str]]:
    if seed is not None:
        random.seed(seed)

    configs = [[], ["--mcsat", "--mcsat-na-bound"]]
    if use_l2o:
        configs.append(["--mcsat", "--mcsat-l2o"])

    n_fixed = len(configs)
    for _ in range(num_configs - n_fixed):
        options = ["--mcsat"]
        if random.random() < 0.9:
            options.append(f"--mcsat-rand-dec-seed={random.randint(1, 1000000)}")
        if random.random() < 0.9:
            options.append(f"--mcsat-rand-dec-freq={random.uniform(0, 1):.2f}")
        if random.random() < 0.5:
            options.append("--mcsat-na-nlsat")
        if random.random() < 0.5:
            options.append("--mcsat-na-mgcd")
        if random.random() < 0.5:
            options.append("--mcsat-na-bound")
        if random.random() < 0.5:
            options.append("--mcsat-partial-restart")
        if use_l2o and random.random() < 0.5:
            options.append("--mcsat-l2o")

        if len(options) == 1:
            options.append(random.choice([
                f"--mcsat-rand-dec-freq={random.uniform(0, 1):.2f}",
                f"--mcsat-rand-dec-seed={random.randint(1, 1000000)}"
            ]))

        configs.append(options)

    return configs


class PortfolioSolver:
    def __init__(self, yices_path, smt2_file, num_threads, verbose=False, seed=None, use_l2o=False):
        self.yices_path = yices_path
        self.smt2_file = smt2_file
        self.num_threads = num_threads
        self.verbose = verbose
        self.seed = seed
        self.use_l2o = use_l2o
        self.threads = []
        self.stop_event = threading.Event()
        self.start_time = None
        self.processes = []
        self._lock = threading.Lock()
        self._solution = None

    def log(self, message):
        if self.verbose:
            print(f"[{time.time() - self.start_time:.2f}s] {message}", file=sys.stderr)

    def cleanup_threads(self):
        self.stop_event.set()
        with self._lock:
            processes, self.processes = self.processes, []
        for process in processes:
            try:
                if process and process.poll() is None:
                    process.kill()
            except (ProcessLookupError, OSError):
                pass

    def try_set_solution(self, value):
        with self._lock:
            if self.stop_event.is_set():
                return
            self._solution = value
            self.stop_event.set()
        self.cleanup_threads()

    def run_yices(self, thread_id, params):
        try:
            cmd = [self.yices_path] + params + [self.smt2_file]
            self.log(f"Thread {thread_id} starting with params: {' '.join(params)}")

            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )
            with self._lock:
                self.processes.append(process)

            stdout, stderr = process.communicate()

            if not self.stop_event.is_set():
                lines = {line.strip().lower() for line in stdout.splitlines()}
                if "unsat" in lines:
                    self.log(f"Thread {thread_id} found UNSAT solution")
                    self.try_set_solution(("unsat", stdout, thread_id, params))
                elif "sat" in lines:
                    self.log(f"Thread {thread_id} found SAT solution")
                    self.try_set_solution(("sat", stdout, thread_id, params))
                else:
                    self.log(f"Thread {thread_id} finished without finding solution")

        except Exception as e:
            if not self.stop_event.is_set():
                self.log(f"Error in thread {thread_id}: {e}")

    def solve(self):
        try:
            param_sets = generate_configs(self.num_threads, self.seed, self.use_l2o)

            self.start_time = time.time()
            self.log(f"Starting portfolio solver with {self.num_threads} threads")
            self.log(f"Using yices_smt2 from: {self.yices_path}")
            self.log(f"Solving file: {self.smt2_file}")
            if self.seed is not None:
                self.log(f"Using random seed: {self.seed}")
            self.log("Generated configurations:")
            for i, params in enumerate(param_sets):
                self.log(f"  Config {i}: {' '.join(params) if params else '(default)'}")

            for i in range(min(self.num_threads, len(param_sets))):
                thread = threading.Thread(target=self.run_yices, args=(i, param_sets[i]))
                thread.daemon = True
                self.threads.append(thread)
                thread.start()
                self.log(f"Started thread {i}")

            for thread in self.threads:
                thread.join()

            if self._solution is not None:
                result, output, thread_id, params = self._solution
                self.log(f"Solution found by thread {thread_id} with params: {' '.join(params) if params else '(default)'}")
                return result, output
            return "unknown", "No solution found"

        finally:
            self.cleanup_threads()


def main():
    global _active_solver

    signal.signal(signal.SIGINT, _global_signal_handler)
    signal.signal(signal.SIGTERM, _global_signal_handler)
    signal.signal(signal.SIGQUIT, _global_signal_handler)

    parser = argparse.ArgumentParser(description='Portfolio solver using yices_smt2')
    parser.add_argument('--yices', default='yices_smt2', help='Path to yices_smt2 executable (default: yices_smt2)')
    parser.add_argument('-n', '--num-threads', type=int, default=4, help='Number of threads to use (default: 4)')
    parser.add_argument('-v', '--verbose', action='store_true', help='Enable verbose output')
    parser.add_argument('--seed', type=int, help='Random seed for configuration generation')
    parser.add_argument('--mcsat-l2o', action='store_true', help='Use MCSAT L2O option as one of the configuration')
    parser.add_argument('smt2_file', help='Path to SMT2 benchmark file')

    args = parser.parse_args()

    if not os.path.isabs(args.yices):
        on_path = shutil.which(args.yices)
        if on_path:
            args.yices = on_path
        else:
            script_dir = os.path.dirname(os.path.abspath(__file__))
            args.yices = os.path.join(script_dir, args.yices)

    if not os.path.exists(args.yices):
        print(f"Error: yices_smt2 executable not found at {args.yices}", file=sys.stderr)
        sys.exit(1)

    if not os.path.exists(args.smt2_file):
        print(f"Error: SMT2 file not found at {args.smt2_file}", file=sys.stderr)
        sys.exit(1)

    try:
        _active_solver = PortfolioSolver(args.yices, args.smt2_file, args.num_threads, args.verbose, args.seed, args.mcsat_l2o)
        result, output = _active_solver.solve()
        print(result)
    except KeyboardInterrupt:
        print("\nInterrupted by user", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()
