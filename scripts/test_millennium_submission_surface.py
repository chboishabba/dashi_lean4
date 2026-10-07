#!/usr/bin/env python3
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
BRIDGE = ROOT / "ExternalClayNS" / "LeanDojoCComparatorBridge.lean"
SAME = ROOT / "ExternalClayNS" / "LeanDojoSameObject.lean"
CORE = ROOT / "ExternalClayNS" / "LeanDojoSameObjectCore.lean"
LINEAR = ROOT / "ExternalClayNS" / "LeanDojoCoordinateLinearEquiv.lean"
BOUNDARY = ROOT / "ExternalClayNS" / "LeanDojoBoundaryExtension.lean"
EXACT = ROOT / "MillenniumExternal" / "ExactTargetSurface.lean"
FRONTIER = ROOT / "MillenniumExternal" / "ExternalTargetFrontier.lean"


class MillenniumSubmissionSurfaceTests(unittest.TestCase):
    def test_ns_c_bridge_has_exact_four_leaf_transport_frontier(self):
        for path in (BRIDGE, SAME, CORE, LINEAR, BOUNDARY):
            self.assertTrue(path.exists(), f"missing canonical NS transport owner: {path.name}")

        bridge = BRIDGE.read_text(encoding="utf-8")
        same = SAME.read_text(encoding="utf-8")
        core = CORE.read_text(encoding="utf-8")
        linear = LINEAR.read_text(encoding="utf-8")
        boundary = BOUNDARY.read_text(encoding="utf-8")

        for residual in (
            "ComparatorForceDecayToLeanDojo",
            "LeanDojoMomentumToClay",
            "LeanDojoIncompressibleToClay",
            "LeanDojoEnergyToClay",
        ):
            self.assertIn(residual, bridge)

        for compiler in (
            "LeanDojoSolutionTransportFrontier",
            "leanDojoInitialCondition_to_clay",
            "leanDojoSolutionToClaySpec_of_transport",
            "LeanDojoCTransportFrontier",
            "leanDojoFeffermanC_of_transport",
        ):
            self.assertIn(compiler, bridge)

        self.assertIn("comparatorInitialDecay_to_leanDojo", same)
        self.assertIn("comparatorInitialDecayData_to_leanDojo", same)
        self.assertIn("leanDojo_spatialDerivativeVector_eq_clay", same)
        self.assertIn("pairLeanSpacetimeEquiv", core)
        self.assertIn("comparatorForceToLean", core)
        self.assertIn("contDiffOn_leanFieldToComparator", linear)
        self.assertIn("eqOn_Ici_zero_of_eqOn_Ioi_zero", boundary)

        self.assertIn("comparatorInitialDecayData_to_leanDojo", bridge)
        self.assertIn("SemanticGap.claySolutionR3_to_comparator", bridge)
        self.assertIn("NavierStokesOnR3.Breakdown.iff_no_finite_energy_solution", bridge)

        for reopened in (
            "ClayInitialDecayToLeanDojo",
            "ClayInitialToLeanDojo",
            "ComparatorInitialToLeanDojo",
            "LeanDojoSolutionToComparator",
            "LeanDojoVelocitySmoothToClay",
            "LeanDojoPressureSmoothToClay",
            "LeanDojoCDStatementWeld",
        ):
            self.assertNotIn(reopened, bridge)

        self.assertNotIn("sorry", bridge)
        self.assertNotIn("axiom ", bridge)

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
