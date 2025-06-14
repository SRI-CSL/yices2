#!/usr/bin/env python3

import subprocess
import threading
import sys
import os
import signal
import time
import argparse
import random
from typing import List

def _global_signal_handler(signum, frame):
    """Global signal handler for the main process"""
    if signum == signal.SIGINT:
        print("\nReceived Ctrl+C, shutting down gracefully...", file=sys.stderr)
    else:
        print(f"\nReceived signal {signum}, shutting down gracefully...", file=sys.stderr)
    
    # Clean up any running threads
    if hasattr(_global_signal_handler, 'solver'):
        _global_signal_handler.solver.cleanup_threads()
    
    sys.exit(0)

class ConfigGenerator:
    def __init__(self, num_configs: int, seed: int = None):
        self.num_configs = num_configs
        if seed is not None:
            random.seed(seed)
        
    def generate_configs(self) -> List[List[str]]:
        configs = [[], ["--mcsat-nra-bound"]]  # Always include empty config and nra bound
        
        for _ in range(self.num_configs - 2):
            options = []
            if random.random() < 0.9:
                options.append(f"--mcsat-rand-dec-freq={random.uniform(0, 1):.2f}")
            if random.random() < 0.6:
                options.append(f"--mcsat-rand-dec-seed={random.randint(1, 1000000)}")
            if random.random() < 0.3:
                options.append("--mcsat-nra-bound")
                
            if not options:
                options.append(random.choice([
                    f"--mcsat-rand-dec-freq={random.uniform(0, 1):.2f}",
                    f"--mcsat-rand-dec-seed={random.randint(1, 1000000)}"
                ]))
                
            configs.append(options)
            
        return configs

class PortfolioSolver:
    def __init__(self, yices_path, smt2_file, num_threads, verbose=False, seed=None):
        self.yices_path = yices_path
        self.smt2_file = smt2_file
        self.num_threads = num_threads
        self.verbose = verbose
        self.seed = seed
        self.threads = []
        self.stop_event = threading.Event()
        self.start_time = None
        self.processes = []
        self._solution = None
        _global_signal_handler.solver = self

    @property
    def solution(self):
        return self._solution

    @solution.setter
    def solution(self, value):
        if not self.stop_event.is_set():
            self._solution = value
            self.stop_event.set()
            self.cleanup_threads()

    def log(self, message):
        if self.verbose:
            print(f"[{time.time() - self.start_time:.2f}s] {message}", file=sys.stderr)

    def cleanup_threads(self):
        self.stop_event.set()
        for process in self.processes:
            try:
                if process and process.poll() is None:
                    process.kill()
            except (ProcessLookupError, OSError):
                pass
        self.threads.clear()
        self.processes.clear()

    def run_yices(self, thread_id, params):
        process = None
        try:
            cmd = [self.yices_path, "--mcsat"] + params + [self.smt2_file]
            self.log(f"Thread {thread_id} starting with params: {' '.join(params)}")
            
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )
            self.processes.append(process)
            
            stdout, stderr = process.communicate()
            
            if not self.stop_event.is_set():
                if "unsat" in stdout.lower():
                    self.log(f"Thread {thread_id} found UNSAT solution")
                    self.solution = ("unsat", stdout, thread_id, params)
                elif "sat" in stdout.lower():
                    self.log(f"Thread {thread_id} found SAT solution")
                    self.solution = ("sat", stdout, thread_id, params)
                else:
                    self.log(f"Thread {thread_id} finished without finding solution")
                
        except Exception as e:
            if not self.stop_event.is_set():
                self.log(f"Error in thread {thread_id}: {e}")
        finally:
            if process and process.poll() is None:
                try:
                    process.kill()
                except (ProcessLookupError, OSError):
                    pass

    def solve(self):
        try:
            config_generator = ConfigGenerator(self.num_threads, self.seed)
            param_sets = config_generator.generate_configs()
            
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

            if self.solution is not None:
                result, output, thread_id, params = self.solution
                self.log(f"Solution found by thread {thread_id} with params: {' '.join(params) if params else '(default)'}")
                return result, output
            return "unknown", "No solution found"

        finally:
            self.cleanup_threads()

def main():
    signal.signal(signal.SIGINT, _global_signal_handler)
    signal.signal(signal.SIGTERM, _global_signal_handler)
    signal.signal(signal.SIGQUIT, _global_signal_handler)
    
    parser = argparse.ArgumentParser(description='Portfolio solver using yices_smt2')
    parser.add_argument('--yices', default='yices_smt2', help='Path to yices_smt2 executable (default: yices_smt2)')
    parser.add_argument('-n', '--num-threads', type=int, default=4, help='Number of threads to use (default: 4)')
    parser.add_argument('-v', '--verbose', action='store_true', help='Enable verbose output')
    parser.add_argument('--seed', type=int, help='Random seed for configuration generation')
    parser.add_argument('smt2_file', help='Path to SMT2 benchmark file')
    
    args = parser.parse_args()

    # Get the directory of this script
    script_dir = os.path.dirname(os.path.abspath(__file__))
    
    # If yices path is not absolute, make it relative to script directory
    if not os.path.isabs(args.yices):
        args.yices = os.path.join(script_dir, args.yices)

    if not os.path.exists(args.yices):
        print(f"Error: yices_smt2 executable not found at {args.yices}", file=sys.stderr)
        sys.exit(1)

    if not os.path.exists(args.smt2_file):
        print(f"Error: SMT2 file not found at {args.smt2_file}", file=sys.stderr)
        sys.exit(1)

    try:
        solver = PortfolioSolver(args.yices, args.smt2_file, args.num_threads, args.verbose, args.seed)
        result, output = solver.solve()
        print(result)
    except KeyboardInterrupt:
        print("\nInterrupted by user", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main() 
