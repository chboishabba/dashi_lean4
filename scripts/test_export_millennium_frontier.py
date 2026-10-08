#!/usr/bin/env python3
import json
import pathlib
import subprocess
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "export_millennium_frontier.py"
FRONTIER = ROOT / "MillenniumExternal" / "ExternalTargetFrontier.lean"
EXACT = ROOT / "MillenniumExternal" / "ExactTargetSurface.lean"


class FrontierExportTests(unittest.TestCase):
    def _data(self):
        out = subprocess.check_output(
            [sys.executable, str(SCRIPT), str(FRONTIER), str(EXACT)], text=True
        )
        return json.loads(out)

    def _rows(self):
        return {row["problem"]: row for row in self._data()["problems"]}

    def test_export_has_seven_unique_problem_rows(self):
        data = self._data()
        self.assertEqual(data["schema_version"], 2)
        self.assertEqual(len(data["problems"]), 7)
        self.assertEqual(len({row["problem"] for row in data["problems"]}), 7)

    def test_pnp_rh_bsd_are_resolution_only_not_red_math(self):
        rows = self._rows()
        for problem in ("pVersusNP", "riemann", "birchSwinnertonDyer"):
            row = rows[problem]
            self.assertEqual(row["frontier"], "PROOF-RESOLUTION")
            self.assertEqual(row["closure_state"], "proofResolutionPending")
        self.assertTrue(rows["riemann"]["exact_statement_weld"])
        self.assertIn("SAT", rows["pVersusNP"]["first_unpaid"])
        self.assertIn("RiemannHypothesis", rows["riemann"]["first_unpaid"])
        self.assertIn("Rank.Existence", rows["birchSwinnertonDyer"]["first_unpaid"])

    def test_ns_source_exact_kernel_gate_is_only_remaining_acceptance_step(self):
        ns = self._rows()["navierStokes"]
        self.assertEqual(ns["frontier"], "PROVED")
        self.assertEqual(ns["closure_state"], "sourceExactKernelPending")
        self.assertIn("dashiExactFeffermanC", ns["first_unpaid"])
        self.assertIn("dashiExactFeffermanD", ns["first_unpaid"])
        self.assertIn("kernel", ns["first_unpaid"].lower())

    def test_incomplete_upstream_targets_fail_closed(self):
        rows = self._rows()
        self.assertEqual(rows["hodge"]["frontier"], "UPSTREAM-DEFECT")
        self.assertEqual(rows["yangMills"]["frontier"], "UPSTREAM-DEFECT")
        self.assertEqual(rows["hodge"]["closure_state"], "upstreamIncomplete")
        self.assertEqual(rows["yangMills"]["closure_state"], "upstreamIncomplete")

    def test_poincare_remains_solved_unformalized(self):
        p = self._rows()["poincare"]
        self.assertEqual(p["frontier"], "SOLVED-UNFORMALIZED")
        self.assertEqual(p["closure_state"], "upstreamSolvedUnformalized")


if __name__ == "__main__":
    unittest.main()
