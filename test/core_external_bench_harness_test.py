"""Check Core's external comparison harness without requiring either engine.

Run with ``python3 -m unittest discover -s test -p '*bench_harness_test.py'``.
These tests validate the measurement/answer contract, not engine performance.
"""

import importlib.util
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "core_external", ROOT / "bench" / "core_external.py")
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

RESULTS = {
    "core-nrev": list(range(30, 0, -1)),
    "core-loop": 90000,
    "core-fib": 75025,
    "core-queens": [1, 5, 8, 6, 3, 7, 2, 4],
}


def output(case="core-loop", answers=None, cpu="0.125", wall="0.25"):
    if answers is None:
        answers = repr([RESULTS[case]])
    return ("INFERA_CORE_RESULT:" + answers + "\n"
            "INFERA_CORE_CPU_SECONDS:" + cpu + "\n"
            "INFERA_CORE_WALL_SECONDS:" + wall + "\n"
            "INFERA_CORE_OK:" + case + "\n")


def scryer_output(case="core-loop", cpu="0.125", inferences="7_910"):
    return ("   INFERA_CORE_RESULT:" + repr([RESULTS[case]]) + "\n"
            "% CPU time: " + cpu + "s, " + inferences + " inferences\n"
            "   INFERA_CORE_OK:" + case + "\n")


class CoreExternalModelTest(unittest.TestCase):
    def test_independent_models_accept_all_four_workloads(self):
        self.assertEqual(set(MODULE.CASES), set(RESULTS))
        for case in MODULE.CASES:
            with self.subTest(case=case):
                row = MODULE.parse_sample("swipl", case, 25, output(case))
                self.assertEqual(row["result"], [RESULTS[case]])
                self.assertTrue(row["fully_drained"])
                self.assertTrue(row["independent_checked"])

    def test_missing_extra_and_uncollected_answers_fail(self):
        for answers in ("[]", "[90000,90000]", "90000", "(90000,)",
                        "{'Result':90000}"):
            with self.subTest(answers=answers), self.assertRaises(ValueError):
                MODULE.parse_sample("swipl", "core-loop", 1, output(answers=answers))

    def test_wrong_scalar_and_boolean_answers_fail(self):
        for case, answers in (("core-loop", "[89999]"),
                              ("core-loop", "[True]"),
                              ("core-fib", "[75024]"),
                              ("core-fib", "[75025.0]")):
            with self.subTest(case=case, answers=answers), self.assertRaises(ValueError):
                MODULE.parse_sample("swipl", case, 1, output(case, answers))

    def test_reverse_checks_contents_order_and_integer_types(self):
        invalid = [list(range(1, 31)), list(range(29, 0, -1)),
                   list(range(30, 0, -1)) + [0],
                   [float(x) for x in range(30, 0, -1)]]
        for value in invalid:
            with self.subTest(value=value), self.assertRaises(ValueError):
                MODULE.parse_sample("swipl", "core-nrev", 1,
                                    output("core-nrev", repr([value])))

    def test_queens_checks_range_uniqueness_length_and_diagonals(self):
        invalid = [[1, 2, 3, 4, 5, 6, 7, 8], [1, 5, 8, 6, 3, 7, 2, 2],
                   [0, 5, 8, 6, 3, 7, 2, 4], [1, 5, 8, 6, 3, 7, 2, 9],
                   [1, 5, 8, 6, 3, 7, 2], [True, 5, 8, 6, 3, 7, 2, 4]]
        for value in invalid:
            with self.subTest(value=value), self.assertRaises(ValueError):
                MODULE.parse_sample("swipl", "core-queens", 1,
                                    output("core-queens", repr([value])))

    def test_queens_accepts_another_valid_solution(self):
        value = [8, 4, 1, 3, 6, 2, 7, 5]
        row = MODULE.parse_sample("swipl", "core-queens", 1,
                                  output("core-queens", repr([value])))
        self.assertEqual(row["result"], [value])

    def test_malformed_results_are_reported_as_validation_errors(self):
        for answers in ("[broken", "[unknown]", "[90000] trailing", ""):
            with self.subTest(answers=answers), self.assertRaises(ValueError):
                MODULE.parse_sample("swipl", "core-loop", 1, output(answers=answers))


class CoreExternalTimingTest(unittest.TestCase):
    def test_swi_reports_batch_and_per_query_loaded_cpu_and_wall(self):
        row = MODULE.parse_sample("swipl", "core-loop", 25, output())
        self.assertEqual((row["cpu_seconds"], row["wall_seconds"]), (0.125, 0.25))
        self.assertEqual(row["per_query_cpu_seconds"], 0.005)
        self.assertEqual(row["per_query_wall_seconds"], 0.01)
        self.assertEqual(row["batch_queries"], 25)
        self.assertEqual(row["warmup_queries"], 1)
        self.assertFalse(row["startup_included"])
        self.assertFalse(row["output_included"])

    def test_gate_is_50ms_of_batch_cpu_inclusive(self):
        for cpu, sufficient in (("0.001", False), ("0.049999", False),
                                ("0.050", True), ("0.125", True)):
            with self.subTest(cpu=cpu):
                row = MODULE.parse_sample("swipl", "core-loop", 1000,
                                          output(cpu=cpu))
                self.assertEqual(row["comparison_timing_sufficient"], sufficient)
                self.assertEqual(row["minimum_gate_batch_cpu_seconds"], 0.05)

    def test_zero_negative_nonfinite_and_malformed_cpu_or_wall_fail(self):
        for field in ("cpu", "wall"):
            for value in ("0", "-0.125", "nan", "inf", "-inf", "bad", ""):
                with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                    MODULE.parse_sample("swipl", "core-loop", 1,
                                        output(**{field: value}))

    def test_swi_requires_exactly_one_of_each_marker(self):
        sample = output()
        for line in sample.splitlines(keepends=True):
            for invalid in (sample.replace(line, ""), sample + line):
                with self.subTest(line=line, invalid=invalid), self.assertRaises(ValueError):
                    MODULE.parse_sample("swipl", "core-loop", 1, invalid)

    def test_wrong_completion_marker_fails(self):
        with self.assertRaises(ValueError):
            MODULE.parse_sample("swipl", "core-loop", 1,
                                output().replace("INFERA_CORE_OK:core-loop", "INFERA_CORE_OK:core-fib"))

    def test_reported_errors_and_search_exhaustion_fail_on_either_stream(self):
        errors = ["ERROR: Unknown procedure statistics/2", "error(type_error(integer,x),ctx).",
                  "Exception: search failed", "search depth limit reached"]
        for error in errors:
            for in_stderr in (False, True):
                with self.subTest(error=error, in_stderr=in_stderr), self.assertRaises(ValueError):
                    MODULE.parse_sample("swipl", "core-loop", 1,
                                        output() if in_stderr else output() + error,
                                        error if in_stderr else "")

    def test_scryer_cpu_line_keeps_wall_unavailable(self):
        row = MODULE.parse_sample("scryer", "core-loop", 25, scryer_output())
        self.assertEqual(row["cpu_seconds"], 0.125)
        self.assertEqual(row["per_query_cpu_seconds"], 0.005)
        self.assertIsNone(row["wall_seconds"])
        self.assertIsNone(row["per_query_wall_seconds"])

    def test_scryer_coarse_positive_timer_is_valid_but_insufficient(self):
        row = MODULE.parse_sample("scryer", "core-loop", 25,
                                  scryer_output(cpu="0.001", inferences="7910"))
        self.assertEqual(row["cpu_seconds"], 0.001)
        self.assertFalse(row["comparison_timing_sufficient"])

    def test_scryer_requires_one_positive_cpu_line(self):
        line = "% CPU time: 0.125s, 7_910 inferences\n"
        sample = scryer_output()
        invalid = [sample.replace(line, ""), sample + line,
                   scryer_output(cpu="0.000"), scryer_output(cpu="nan"),
                   scryer_output(cpu="-0.125"),
                   sample.replace("7_910 inferences", "unknown inferences")]
        for value in invalid:
            with self.subTest(value=value), self.assertRaises(ValueError):
                MODULE.parse_sample("scryer", "core-loop", 1, value)


class CoreExternalRequestTest(unittest.TestCase):
    def test_invalid_requests_fail_for_commands_and_parser(self):
        invalid = [("unknown", "core-loop", 1), ("swipl", "loop", 1),
                   ("swipl", "core-loop", 0), ("swipl", "core-loop", -1),
                   ("swipl", "core-loop", True), ("swipl", "core-loop", 1.0),
                   ("swipl", "core-loop", "1"), ("swipl", "core-loop", 1000001),
                   ("swipl", "core-loop');halt;('", 1)]
        for engine, case, batch in invalid:
            with self.subTest(engine=engine, case=case, batch=batch):
                with self.assertRaises(ValueError):
                    MODULE.command(engine, "/path/to/engine", case, batch)
                with self.assertRaises(ValueError):
                    MODULE.parse_sample(engine, case, batch, output())

    def test_swi_command_is_an_argument_vector_with_exact_driver_and_goal(self):
        binary = Path("/engine with spaces/$(touch injected)")
        args = MODULE.command("swipl", binary, "core-loop", 25)
        self.assertEqual(args, [str(binary), "-q", "-g",
                               "external_bench_swipl('core-loop',25),halt",
                               "-t", "halt", str(ROOT / "bench" / "core-external.pl")])

    def test_scryer_explicitly_loads_cpu_timer_without_history(self):
        args = MODULE.command("scryer", "/path/to/scryer", "core-nrev", 100)
        self.assertEqual(args, ["/path/to/scryer", "-f", "--no-add-history", "-g",
                               "use_module(library(time)),external_bench_scryer('core-nrev',100),halt",
                               str(ROOT / "bench" / "core-external.pl")])


class CoreExternalSourceTest(unittest.TestCase):
    def test_original_algorithms_are_a_byte_identical_prefix(self):
        original = (ROOT / "bench" / "bench.pl").read_bytes()
        driver = (ROOT / "bench" / "core-external.pl").read_bytes()
        self.assertTrue(driver.startswith(original))
        self.assertGreater(len(driver), len(original))

    def test_reverse_and_loop_inputs_match_core_major_exactly(self):
        driver = (ROOT / "bench" / "core-external.pl").read_text()
        native = (ROOT / "bench" / "core-major.hs").read_text()
        self.assertIn("once((bench_nrev(100), range(1, 30, L), nrev(L, Result)))", driver)
        self.assertIn('once (bench_nrev 100, range 1 30 L, nrev L Result)?', native)
        self.assertIn("once((loop(90000), Result = 90000))", driver)
        self.assertIn('once (loop 90000, Result = 90000)?', native)
        self.assertNotIn("bench_nrev(3000)", driver)

    def test_timed_batch_is_drained_and_checked_outside_warmup_and_output(self):
        driver = (ROOT / "bench" / "core-external.pl").read_text()
        self.assertIn("findall(Result, external_case(Case, Result), Results)", driver)
        self.assertIn("ground(Results), external_valid(Case, Results)", driver)
        self.assertIn("external_checked(Case, _), Next is N - 1", driver)
        swi = driver.split("external_bench_swipl(Case, N) :-", 1)[1].split("external_bench_scryer", 1)[0]
        self.assertLess(swi.index("external_checked(Case, _)"), swi.index("statistics(process_cputime, C0)"))
        self.assertLess(swi.index("external_batch(N, Case)"), swi.index("statistics(process_cputime, C1)"))
        self.assertLess(swi.index("statistics(process_cputime, C1)"), swi.index("external_checked(Case, Results)"))
        self.assertLess(swi.index("external_checked(Case, Results)"), swi.index("external_output(Case, Results)"))


if __name__ == "__main__":
    unittest.main()
