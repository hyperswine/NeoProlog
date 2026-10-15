"""Regression tests for the engine benchmark runner, without needing an engine.

Run with ``python3 -m unittest discover -s test -p bench_harness_test.py``.
The executable doubles exercise process failures and output validation; they do
not make timing assertions or replace the real-engine workload checks.
"""

import json
import math
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "bench" / "run.py"

STUB = r'''import json
import os
from pathlib import Path
import sys
import time

case = os.environ["INFERA_BENCH_CASE"]
mode = os.environ.get("BENCH_TEST_MODE", "success")
stdin = sys.stdin.read()
sources = {}
for arg in sys.argv[1:]:
    path = Path(arg)
    if path.suffix in (".nprolog", ".pl") and path.is_file():
        sources[str(path)] = path.read_text()
with open(os.environ["BENCH_TEST_LOG"], "a") as log:
    log.write(json.dumps({"case": case, "engine": os.environ["INFERA_BENCH_ENGINE"],
                          "cwd": os.getcwd(), "argv": sys.argv[1:],
                          "stdin": stdin, "sources": sources}) + "\n")
if mode == "late_exit":
    with open(os.environ["BENCH_TEST_LOG"]) as log:
        if len(log.readlines()) > 1:
            sys.exit(42)
marker = "INFERA_BENCH_OK:" + case
answers = {"nrev": list(range(30, 0, -1)), "loop": 90000,
           "fib": 75025, "queens": [1, 5, 8, 6, 3, 7, 2, 4]}
answer = json.dumps(answers[case])
if mode == "exit":
    print(marker)
    sys.exit(42)
if mode == "silent":
    sys.exit(0)
if mode == "echo":
    print('> print "' + marker + '"?')
    sys.exit(0)
if mode == "timeout":
    time.sleep(5)
if mode == "wrong_case":
    print("INFERA_BENCH_OK:wrong")
    sys.exit(0)
if mode == "error":
    print("Error: synthetic benchmark failure")
if mode == "stderr_error":
    print("Error: synthetic benchmark failure", file=sys.stderr)
if mode == "false":
    print("false.")
if mode == "exhaustion":
    print("Search depth limit exceeded")
if mode == "duplicate":
    print(marker)
print(marker)
if mode == "marker_only":
    sys.exit(0)
if mode == "wrong_result":
    answer = json.dumps({"nrev": list(range(1, 31)), "loop": 89999,
                         "fib": 75024, "queens": [1, 2, 3, 4, 5, 6, 7, 8]}[case])
if mode == "malformed_result":
    answer = "[1, broken"
if mode == "duplicate_result":
    print("INFERA_BENCH_RESULT:" + answer)
print("INFERA_BENCH_RESULT:" + answer)
print("true.")
'''


class BenchmarkHarnessTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="infera-bench-test-")
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        # Shell metacharacters are intentional: the runner must execute argv
        # directly, even when a user supplies an unusual binary path.
        self.binary = self.directory / "fake engine $(touch injected)"
        self.binary.write_text("#!" + sys.executable + "\n" + STUB)
        self.binary.chmod(0o755)
        self.log = self.directory / "invocations.jsonl"

    def invoke(self, *extra, mode="success", path=None, base=True):
        env = os.environ.copy()
        env["BENCH_TEST_MODE"] = mode
        env["BENCH_TEST_LOG"] = str(self.log)
        if path is not None:
            env["PATH"] = path
        args = [sys.executable, str(RUNNER), "--json"]
        if base:
            args += ["--binary", str(self.binary), "--engine", "infera",
                     "--case", "loop", "--runs", "1", "--warmup", "0"]
        result = subprocess.run(args + list(extra), cwd=self.directory,
                                env=env, capture_output=True, text=True,
                                timeout=15)
        return result

    def rows(self, result):
        return [json.loads(line) for line in result.stdout.splitlines() if line.strip()]

    def invocations(self):
        if not self.log.exists():
            return []
        return [json.loads(line) for line in self.log.read_text().splitlines()]

    def assert_failed(self, result):
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        for row in self.rows(result):
            self.assertNotEqual(row.get("status"), "ok", row)
            self.assertFalse(row.get("samples_seconds"), row)
            self.assertIsNone(row.get("median_seconds"), row)

    def test_success_has_validated_samples_and_excludes_warmups(self):
        result = self.invoke("--runs", "3", "--warmup", "2")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        rows = self.rows(result)
        self.assertEqual(len(rows), 1, rows)
        row = rows[0]
        self.assertEqual((row["engine"], row["case"], row["status"]),
                         ("infera", "loop", "ok"))
        self.assertEqual(len(row["samples_seconds"]), 3)
        self.assertTrue(all(math.isfinite(value) and value > 0
                            for value in row["samples_seconds"]))
        self.assertTrue(math.isfinite(row["median_seconds"]))
        self.assertEqual(len(self.invocations()), 5)

    def test_every_case_runs_in_an_isolated_directory(self):
        before = {p.name for p in (ROOT / "bench").iterdir()}
        result = self.invoke("--binary", str(self.binary), "--engine", "infera",
                             "--runs", "1", "--warmup", "0", base=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        rows = self.rows(result)
        self.assertEqual({row["case"] for row in rows}, {"nrev", "loop", "fib", "queens"})
        calls = self.invocations()
        self.assertEqual(len(calls), 4)
        for call in calls:
            workdir = Path(call["cwd"])
            self.assertNotEqual(workdir, ROOT / "bench")
            self.assertNotEqual(workdir, self.directory)
            self.assertFalse(workdir.exists(), "temporary engine directory was not removed")
            self.assertTrue(call["sources"], call)
            self.assertEqual(call["engine"], "infera")
        self.assertEqual({p.name for p in (ROOT / "bench").iterdir()}, before)
        self.assertFalse((self.directory / "injected").exists())
        self.assertFalse((ROOT / "bench" / "injected").exists())

    def test_nonzero_exit_is_not_a_timing_success_even_with_marker(self):
        self.assert_failed(self.invoke(mode="exit"))

    def test_false_executable_regression(self):
        self.assert_failed(self.invoke("--binary", "/usr/bin/false"))

    def test_zero_exit_without_result_is_not_success(self):
        self.assert_failed(self.invoke(mode="silent"))

    def test_echoed_query_does_not_count_as_completion(self):
        self.assert_failed(self.invoke(mode="echo"))

    def test_wrong_workload_marker_is_not_success(self):
        self.assert_failed(self.invoke(mode="wrong_case"))

    def test_duplicate_completion_is_not_success(self):
        self.assert_failed(self.invoke(mode="duplicate"))

    def test_completion_without_semantic_answer_is_not_success(self):
        self.assert_failed(self.invoke(mode="marker_only"))

    def test_wrong_answer_for_each_workload_is_not_success(self):
        for case in ("nrev", "loop", "fib", "queens"):
            with self.subTest(case=case):
                self.assert_failed(self.invoke("--binary", str(self.binary), "--engine", "infera",
                                               "--case", case, "--runs", "1", "--warmup", "0",
                                               mode="wrong_result", base=False))

    def test_malformed_or_duplicate_semantic_answer_is_not_success(self):
        for mode in ("malformed_result", "duplicate_result"):
            with self.subTest(mode=mode):
                self.assert_failed(self.invoke(mode=mode))

    def test_error_failure_and_exhaustion_override_completion(self):
        for mode in ("error", "stderr_error", "false", "exhaustion"):
            with self.subTest(mode=mode):
                self.assert_failed(self.invoke(mode=mode))

    def test_timeout_is_failure_without_samples(self):
        self.assert_failed(self.invoke("--timeout", "0.1", mode="timeout"))

    def test_failed_warmup_aborts_before_measurement(self):
        self.assert_failed(self.invoke("--runs", "3", "--warmup", "2", mode="exit"))
        self.assertEqual(len(self.invocations()), 1)

    def test_partial_measurement_failure_has_no_success_summary(self):
        self.assert_failed(self.invoke("--runs", "3", mode="late_exit"))
        self.assertEqual(len(self.invocations()), 2)

    def test_invalid_numeric_flags_fail_before_execution(self):
        invalid = {
            "--runs": ("0", "-1", "1.5", "nan"),
            "--warmup": ("-1", "0.5", "nan"),
            "--timeout": ("0", "-1", "nan", "inf", "-inf", "invalid"),
        }
        for flag, values in invalid.items():
            for value in values:
                with self.subTest(flag=flag, value=value):
                    result = self.invoke(flag, value)
                    self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.invocations())

    def test_unknown_case_or_engine_is_rejected(self):
        for args in (("--case", "unknown"), ("--engine", "unknown")):
            with self.subTest(args=args):
                self.assertNotEqual(self.invoke(*args).returncode, 0)
        self.assertFalse(self.invocations())

    def test_explicit_missing_optional_engine_is_failure(self):
        for engine in ("swipl", "scryer"):
            with self.subTest(engine=engine):
                result = self.invoke("--binary", str(self.binary), "--engine", engine,
                                     "--case", "loop", "--runs", "1", "--warmup", "0",
                                     path="", base=False)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertFalse(self.invocations())

    def test_binary_environment_override(self):
        env = os.environ.copy()
        env.update(INFERA_BIN=str(self.binary), BENCH_TEST_MODE="success",
                   BENCH_TEST_LOG=str(self.log))
        result = subprocess.run([sys.executable, str(RUNNER), "--json", "--engine", "infera",
                                 "--case", "loop", "--runs", "1", "--warmup", "0"],
                                cwd=self.directory, env=env, capture_output=True,
                                text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(len(self.invocations()), 1)

    def test_comparison_engine_overrides_use_the_same_validation(self):
        env = os.environ.copy()
        env.update(SWIPL_BIN=str(self.binary), SCRYER_BIN=str(self.binary),
                   BENCH_TEST_MODE="success", BENCH_TEST_LOG=str(self.log))
        result = subprocess.run([sys.executable, str(RUNNER), "--json",
                                 "--engine", "swipl", "--engine", "scryer", "--case", "fib",
                                 "--runs", "1", "--warmup", "0"],
                                cwd=self.directory, env=env, capture_output=True,
                                text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual({row["engine"] for row in self.rows(result)}, {"swipl", "scryer"})
        calls = self.invocations()
        self.assertEqual(len(calls), 2)
        for call in calls:
            self.assertEqual(call["stdin"], "")
            self.assertTrue(any(path.endswith(".pl") for path in call["sources"]))
            self.assertFalse(Path(call["cwd"]).exists())


if __name__ == "__main__":
    unittest.main()
