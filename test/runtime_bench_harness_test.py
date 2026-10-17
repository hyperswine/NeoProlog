"""Loaded benchmark validation tests, without requiring a Prolog engine.

Run with ``python3 -m unittest discover -s test -p '*bench_harness_test.py'``.
The real-engine checks remain separate; executable doubles test failure paths
and explicit backend/timer selection, never performance thresholds.
"""

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "bench" / "runtime-compare.py"
SPEC = importlib.util.spec_from_file_location("runtime_compare", RUNNER)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

STUB = r'''import json
import os
from pathlib import Path
import re
import sys
import time

mode = os.environ.get("RUNTIME_TEST_MODE", "success")
args = sys.argv[1:]
if "--case" in args:
    case = args[args.index("--case") + 1]
    engine = args[args.index("--engine") + 1]
    batch = int(args[args.index("--batch") + 1])
else:
    goal = args[args.index("-g") + 1]
    case = re.search(r"runtime_checked\('([^']+)'", goal).group(1)
    engine = "scryer" if "use_module(library(time))" in goal else "swipl"
    batch = int(re.search(r"runtime_batch\(([0-9]+)", goal).group(1))
with open(os.environ["RUNTIME_TEST_LOG"], "a") as output:
    output.write(json.dumps({"argv": args, "cwd": os.getcwd(), "case": case,
                             "engine": engine, "batch": batch}) + "\n")
if mode == "timeout":
    time.sleep(5)
if mode == "exit":
    sys.exit(42)
if mode == "silent":
    sys.exit(0)
if mode == "stderr_error":
    print("error(existence_error(procedure,statistics/2),statistics/2).", file=sys.stderr)
cpu = 0.0 if mode == "zero" else 0.001 if mode == "coarse" else 0.125
if engine in ("bytecode", "interpreted"):
    row = {"status": "ok", "engine": engine, "case": case, "phase": "warm",
           "batch_queries": batch, "verified_answers": 1, "fully_drained": True,
           "oracle_checked": True, "independent_checked": True, "fresh_query_state": True,
           "cpu_seconds": cpu, "wall_seconds": 0.25}
    if mode == "wrong_backend":
        row["engine"] = "reference"
    if mode == "unchecked":
        row["independent_checked"] = False
    print(json.dumps(row))
else:
    print(("   " if engine == "scryer" else "") + "INFERA_RUNTIME_RESULT:" + ("[45149]" if mode == "wrong_result" else "[45150]"))
    if engine == "scryer":
        print("%% CPU time: %.3fs, 7_910 inferences" % cpu)
    else:
        print("INFERA_RUNTIME_CPU_SECONDS:" + str(cpu))
        print("INFERA_RUNTIME_WALL_SECONDS:0.25")
    if mode == "duplicate":
        print("INFERA_RUNTIME_OK:" + case)
    print("INFERA_RUNTIME_OK:" + case)
'''


def swi_output(case="controls", result="[45150]", cpu="0.125", wall="0.25"):
    return ("INFERA_RUNTIME_RESULT:" + result + "\n"
            "INFERA_RUNTIME_CPU_SECONDS:" + cpu + "\n"
            "INFERA_RUNTIME_WALL_SECONDS:" + wall + "\n"
            "INFERA_RUNTIME_OK:" + case + "\n")


class RuntimeModelsTest(unittest.TestCase):
    def test_integer_reverse_and_queens_models_accept_checked_answers(self):
        for case in MODULE.CASES:
            value = {"core-nrev": list(range(30, 0, -1)), "core-loop": 90000,
                     "core-fib": 75025, "core-queens": [1, 5, 8, 6, 3, 7, 2, 4]}.get(case, 45150)
            with self.subTest(case=case):
                MODULE.validate_result(case, [value])

    def test_wrong_values_extra_answers_booleans_and_unsafe_queens_fail(self):
        invalid = [("controls", [45149]), ("controls", [True]),
                   ("controls", [45150, 45150]), ("controls", []),
                   ("core-nrev", [list(range(1, 31))]),
                   ("core-queens", [[1, 2, 3, 4, 5, 6, 7, 8]]),
                   ("core-queens", [[1, 5, 8, 6, 3, 7, 2, 2]])]
        for case, value in invalid:
            with self.subTest(case=case, value=value):
                with self.assertRaises(MODULE.RuntimeErrorChecked):
                    MODULE.validate_result(case, value)

    def test_swi_cpu_and_wall_are_loaded_batch_totals(self):
        row = MODULE.read_prolog("controls", swi_output(), "swipl")
        self.assertEqual((row["cpu_seconds"], row["wall_seconds"]), (0.125, 0.25))

    def test_scryer_cpu_only_does_not_invent_loaded_wall_time(self):
        text = "   INFERA_RUNTIME_RESULT:[45150]\n% CPU time: 0.125s, 7_910 inferences\nINFERA_RUNTIME_OK:controls\n"
        row = MODULE.read_prolog("controls", text, "scryer")
        self.assertEqual(row["cpu_seconds"], 0.125)
        self.assertIsNone(row["wall_seconds"])

    def test_missing_duplicate_or_wrong_markers_and_malformed_results_fail(self):
        invalid = [swi_output().replace("INFERA_RUNTIME_OK:controls\n", ""),
                   swi_output() + "INFERA_RUNTIME_OK:controls\n",
                   swi_output(case="core-loop"), swi_output(result="[broken"),
                   swi_output() + "INFERA_RUNTIME_RESULT:[45150]\n"]
        for text in invalid:
            with self.subTest(text=text):
                with self.assertRaises(MODULE.RuntimeErrorChecked):
                    MODULE.read_prolog("controls", text, "swipl")

    def test_missing_duplicate_zero_and_nonfinite_timers_fail(self):
        invalid = [swi_output(cpu="0"), swi_output(cpu="nan"), swi_output(wall="inf"),
                   swi_output().replace("INFERA_RUNTIME_CPU_SECONDS:0.125\n", ""),
                   swi_output() + "INFERA_RUNTIME_CPU_SECONDS:0.125\n"]
        for text in invalid:
            with self.subTest(text=text):
                with self.assertRaises(MODULE.RuntimeErrorChecked):
                    MODULE.read_prolog("controls", text, "swipl")

    def test_scryer_requires_exactly_one_positive_cpu_line(self):
        base = "INFERA_RUNTIME_RESULT:[45150]\nINFERA_RUNTIME_OK:controls\n"
        invalid = [base, base + "% CPU time: 0.000s, 7_910 inferences\n",
                   base + "% CPU time: 0.125s, 7_910 inferences\n" * 2]
        for text in invalid:
            with self.subTest(text=text):
                with self.assertRaises(MODULE.RuntimeErrorChecked):
                    MODULE.read_prolog("controls", text, "scryer")


class RuntimeProcessTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="infera-runtime-test-")
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.binary = self.directory / "fake engine $(touch injected)"
        self.binary.write_text("#!" + sys.executable + "\n" + STUB)
        self.binary.chmod(0o755)
        self.log = self.directory / "calls.jsonl"

    def invoke(self, engine="swipl", mode="success", *extra):
        environment = os.environ.copy()
        environment.update(RUNTIME_TEST_MODE=mode, RUNTIME_TEST_LOG=str(self.log))
        flag = "--infera-runner" if engine.startswith("infera-") else "--" + engine
        result = subprocess.run([sys.executable, str(RUNNER), "--engine", engine,
                                 flag, str(self.binary), "--case", "controls", "--runs", "1",
                                 *extra], cwd=self.directory, env=environment,
                                capture_output=True, text=True, timeout=15)
        return result, [json.loads(line) for line in result.stdout.splitlines() if line.strip()]

    def assert_failed(self, result, rows):
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(len(rows), 1, rows)
        self.assertEqual(rows[0]["status"], "error", rows)
        self.assertFalse(rows[0]["samples"], rows)
        self.assertNotIn("median_per_query_cpu_seconds", rows[0])

    def test_explicit_bytecode_uses_loaded_runner_and_checks_its_gates(self):
        result, rows = self.invoke("infera-bytecode")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(rows[0]["engine"], "infera-bytecode")
        call = json.loads(self.log.read_text().splitlines()[0])
        self.assertEqual((call["engine"], call["batch"], call["cwd"]), ("bytecode", 100, str(ROOT)))
        self.assertFalse((self.directory / "injected").exists())

    def test_scryer_cpu_rows_keep_wall_unavailable(self):
        result, rows = self.invoke("scryer")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        row = rows[0]
        self.assertEqual(row["median_per_query_cpu_seconds"], 0.00125)
        self.assertIsNone(row["median_per_query_wall_seconds"])
        self.assertIsNone(row["wall_clock"])

    def test_nonzero_exit_silent_zero_or_semantically_invalid_output_fails(self):
        for mode in ("exit", "silent", "zero", "wrong_result", "duplicate", "stderr_error"):
            with self.subTest(mode=mode):
                self.assert_failed(*self.invoke("swipl", mode))

    def test_unchecked_or_wrong_backend_infera_rows_fail(self):
        for mode in ("unchecked", "wrong_backend"):
            with self.subTest(mode=mode):
                self.assert_failed(*self.invoke("infera-bytecode", mode))

    def test_positive_coarse_samples_cannot_establish_default_gate(self):
        for engine in ("infera-bytecode", "swipl", "scryer"):
            with self.subTest(engine=engine):
                result, rows = self.invoke(engine, "coarse")
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(rows[0]["status"], "ok")
                self.assertTrue(rows[0]["samples"])
                self.assertFalse(rows[0]["comparison_timing_sufficient"])
                self.assertEqual(rows[0]["minimum_gate_batch_cpu_seconds"], 0.05)

    def test_timeout_is_failure_without_success_samples(self):
        self.assert_failed(*self.invoke("swipl", "timeout", "--timeout", "0.05"))

    def test_rounds_alternate_and_temporary_prolog_directories_are_removed(self):
        result, rows = self.invoke("swipl", "success", "--runs", "3",
                                   "--engine", "infera-bytecode", "--infera-runner", str(self.binary))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(len(rows[0]["samples"]), 3)
        calls = [json.loads(line) for line in self.log.read_text().splitlines()]
        self.assertEqual([call["engine"] for call in calls],
                         ["swipl", "bytecode", "bytecode", "swipl", "swipl", "bytecode"])
        for call in calls:
            if call["engine"] == "swipl":
                self.assertNotEqual(call["cwd"], str(ROOT))
                self.assertFalse(Path(call["cwd"]).exists())


if __name__ == "__main__":
    unittest.main()
