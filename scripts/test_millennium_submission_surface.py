#!/usr/bin/env python3
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
BRIDGE = ROOT / "ExternalClayNS" / "LeanDojoCComparatorBridge.lean"
GEOMETRY = ROOT / "ExternalClayNS" / "LeanDojoCarrierGeometry.lean"
EXACT = ROOT / "MillenniumExternal" / "ExactTargetSurface.lean"
FRONTIER = ROOT / "MillenniumExternal" / "ExternalTargetFrontier.lean"


class MillenniumSubmissionSurfaceTests(unittest.TestCase):
    def test_ns_c_bridge_reuses_paid_clayspec_and_carrier_welds(self):
        self.assertTrue(BRIDGE.exists(), "direct ClaySpec-to-LeanDojo C bridge is missing")
        self.assertTrue(GEOMETRY.exists(), "LeanDojo carrier geometry is missing")
        text = BRIDGE.read_text(encoding="utf-8")
        geometry = GEOMETRY.read_text(encoding="utf-8")
        for name in (
            "ClayInitialDecayToLeanDojo",
            "ClayForceToLeanDojo",
            "LeanDojoSolutionToClaySpec",
            "LeanDojoCTransportFrontier",
            "leanDojoFeffermanC_of_transport",
        ):
            self.assertIn(name, text)
        for paid in (
            "pairFieldToLeanDojo_spacetime_point",
            "leanDojoFieldToPair_pairFieldToLeanDojo",
            "spacetime_point_mem_global_iff",
            "clayInitialDivergenceFree_to_leanDojo",
        ):
            self.assertIn(paid, geometry)
        self.assertIn("SemanticGap.admissibleDataR3_of_comparator", text)
        self.assertIn("SemanticGap.claySolutionR3_to_comparator", text)
        self.assertIn("clayInitialDivergenceFree_to_leanDojo", text)
        self.assertNotIn("ClayInitialToLeanDojo", text)
        self.assertNotIn("ComparatorInitialToLeanDojo", text)
        self.assertNotIn("ComparatorForceToLeanDojo", text)
        self.assertNotIn("LeanDojoSolutionToComparator", text)
        self.assertNotIn("LeanDojoCDStatementWeld", text)
        self.assertNotIn("sorry", text + geometry)
        self.assertNotIn("axiom ", text + geometry)

    def test_exact_p_negative_branch_needs_only_one_language_outside_p(self):
        text = EXACT.read_text(encoding="utf-8")
        self.assertIn("theorem clayPNotEqualsNP_of_language_outside_p", text)
        self.assertIn("Millennium.InNondeterministicPolynomialTime", text)
        self.assertIn("Millennium.InPolynomialTime", text)
        self.assertIn("Millennium.ClayPVersusNP.Formulations.NegativeBranch", text)
        self.assertIn("#print axioms clayPNotEqualsNP_of_language_outside_p", text)

    def test_exact_targets_can_only_be_green_from_unconditional_theorems(self):
        frontier = FRONTIER.read_text(encoding="utf-8")
        ns_start = frontier.index("problem := .navierStokes")
        ns_end = frontier.index("problem := .hodge", ns_start)
        ns = frontier[ns_start:ns_end]
        bridge = BRIDGE.read_text(encoding="utf-8")
        if "state := .greenExact" in ns:
            self.assertIn(
                "theorem leanDojoFeffermanC :\n    MillenniumNavierStokes.FeffermanC :=",
                bridge,
            )
            self.assertIn("#print axioms leanDojoFeffermanC", bridge)

        p_start = frontier.index("problem := .pVersusNP")
        p_end = frontier.index("problem := .riemann", p_start)
        p = frontier[p_start:p_end]
        if "state := .greenExact" in p:
            exact = EXACT.read_text(encoding="utf-8")
            self.assertIn("theorem clayPNotEqualsNP", exact)
            self.assertNotIn("_of_language_outside_p", exact)


if __name__ == "__main__":
    unittest.main()
