#!/usr/bin/env python3
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
RESOLUTION = ROOT / "MillenniumExternal" / "ProofResolutionMaxCut.lean"
FRONTIER = ROOT / "MillenniumExternal" / "ExternalTargetFrontier.lean"
CENSUS = ROOT / "MillenniumExternal" / "TerminalCensus.lean"


class MillenniumPNPVirtualFrontierTests(unittest.TestCase):
    def test_resolution_retires_literal_materialisation_and_tracks_virtual_route(self):
        text = RESOLUTION.read_text(encoding="utf-8")
        for donor in (
            "PNotEqualsNPCodedLiteralSelfQuotationPositiveBudgetNoGoExact.literalStructuralSelfQuotationPositiveBudgetImpossible",
            "PNotEqualsNPVirtualQuotationFrontierExact.literalAnchoredRouteClosed",
            "PNotEqualsNPVirtualQuotationFrontierExact.VirtualSelfQuotationCompilation",
            "PNotEqualsNPFixedDescriptionVirtualGeneratorExact.FixedDescriptionGuardedCookBitGenerator",
            "PNotEqualsNPFaithfulVirtualSimulationExact.FaithfulVirtualSelfQuotationCompilation",
            "GuardedCookFixedDescriptionStreamingCostExact.fixedDescriptionLinearBudget",
        ):
            self.assertIn(donor, text)
        self.assertIn("pnp_resolution_uses_virtual_streaming_maxcut", text)

        start = text.index("def pVersusNPResolution")
        end = text.index("def rhResolution", start)
        lane = text[start:end]
        self.assertIn("resolvedSourceTerm := none", lane)
        self.assertIn("newMathematicsPermitted := false", lane)

    def test_frontier_names_finite_generator_simulation_and_same_budget(self):
        text = FRONTIER.read_text(encoding="utf-8")
        start = text.index("problem := .pVersusNP")
        end = text.index("problem := .riemann", start)
        lane = text[start:end]
        for marker in (
            "fixed-description",
            "streamed",
            "finite coded standard",
            "faithful same-target virtual simulation",
            "same Cook budget",
            "literal materialisation",
        ):
            self.assertIn(marker, lane)
        self.assertIn("state := .proofResolutionPending", lane)
        self.assertNotIn("state := .greenExact", lane)

    def test_census_points_to_current_virtual_streaming_owner(self):
        text = CENSUS.read_text(encoding="utf-8")
        start = text.index("def pVersusNPLane")
        end = text.index("def riemannLane", start)
        lane = text[start:end]
        for marker in (
            "PNotEqualsNPCodedLiteralSelfQuotationPositiveBudgetNoGoExact",
            "PNotEqualsNPFixedDescriptionVirtualGeneratorExact",
            "PNotEqualsNPFaithfulVirtualSimulationExact",
            "virtual/streaming",
        ):
            self.assertIn(marker, lane)


if __name__ == "__main__":
    unittest.main()
