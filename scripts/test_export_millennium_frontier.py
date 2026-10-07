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
    def _rows(self):
        out = subprocess.check_output(
            [sys.executable, str(SCRIPT), str(FRONTIER), str(EXACT)], text=True
        )
        return {row["problem"]: row for row in json.loads(out)["problems"]}

    def test_export_has_seven_unique_problem_rows(self):
        out = subprocess.check_output(
            [sys.executable, str(SCRIPT), str(FRONTIER), str(EXACT)], text=True
        )
        data = json.loads(out)
        self.assertEqual(len(data["problems"]), 7)
        self.assertEqual(len({row["problem"] for row in data["problems"]}), 7)

    def test_rh_statement_weld_is_paid_but_math_is_open(self):
        rh = self._rows()["riemann"]
        self.assertEqual(rh["frontier"], "ANALYTIC")
        self.assertTrue(rh["exact_statement_weld"])
        self.assertEqual(rh["closure_state"], "redMath")
        self.assertIn("RiemannHypothesis", rh["first_unpaid"])

    def test_pnp_frontier_names_literal_agda_collision(self):
        pnp = self._rows()["pVersusNP"]
        self.assertEqual(pnp["frontier"], "ANALYTIC")
        self.assertIn(
            "UniversalAnchoredPolynomialSATDecisionCollision", pnp["first_unpaid"]
        )

    def test_incomplete_upstream_targets_fail_closed(self):
        rows = self._rows()
        self.assertEqual(rows["hodge"]["frontier"], "UPSTREAM-DEFECT")
        self.assertEqual(rows["yangMills"]["frontier"], "UPSTREAM-DEFECT")
        self.assertFalse(rows["hodge"]["exact_statement_weld"])
        self.assertFalse(rows["yangMills"]["exact_statement_weld"])


if __name__ == "__main__":
    unittest.main()
