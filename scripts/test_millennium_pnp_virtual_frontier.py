#!/usr/bin/env python3
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
RESOLUTION = ROOT / "MillenniumExternal" / "ProofResolutionMaxCut.lean"
FRONTIER = ROOT / "MillenniumExternal" / "ExternalTargetFrontier.lean"
CENSUS = ROOT / "MillenniumExternal" / "TerminalCensus.lean"


class MillenniumPNPVirtualFrontierTests(unittest.TestCase):
    def test_resolution_tracks_live_compiler_and_return_boundary(self):
        text = RESOLUTION.read_text(encoding="utf-8")
        for donor in (
            "PNotEqualsNPCodedLiteralSelfQuotationPositiveBudgetNoGoExact.literalStructuralSelfQuotationPositiveBudgetImpossible",
            "ConcreteTapeGlobalCookLevinStreamingBitCostedExact.streamedCookBitCostedResultExact",
            "GuardedCookFixedDescriptionIndexABIExact.indexABIWorkBound",
            "ConcreteTapeFixedLocalKernelTablesExact.transitionKernelFrozenSeekExact",
            "CodedFiniteStandardLinkedStructuralSimulationExact.linkedStructuralSimulation",
            "CodedFiniteStandardLinkedRunSimulationExact.simulateCodedCandidateExecution",
            "CodedFiniteStandardLinkedRunSimulationExact.appendLinkedCandidatePhase",
            "CodedFiniteStandardReturnLinkFreshnessExact.residentCandidateRuleBlocksReturnLink",
            "ConcreteTapeStandardClockExact.concreteStandardClockReceipt",
        ):
            self.assertIn(donor, text)
        self.assertIn("pnp_resolution_uses_virtual_streaming_maxcut", text)

        start = text.index("def pVersusNPResolution")
        end = text.index("def rhResolution", start)
        lane = text[start:end]
        self.assertIn("resolvedSourceTerm := none", lane)
        self.assertIn("newMathematicsPermitted := false", lane)

    def test_frontier_names_generator_and_quiescent_return_as_first_unpaid(self):
        text = FRONTIER.read_text(encoding="utf-8")
        start = text.index("problem := .pVersusNP")
        end = text.index("problem := .riemann", start)
        lane = text[start:end]
        for marker in (
            "index-only ABI",
            "finite local kernel tables",
            "exact linked candidate middle run",
            "fresh dispatch key",
            "clock/phase wrapper",
            "quiescent",
            "same Cook budget",
        ):
            self.assertIn(marker, lane)
        self.assertIn("state := .proofResolutionPending", lane)
        self.assertNotIn("state := .greenExact", lane)

    def test_census_points_to_current_compiler_owners(self):
        text = CENSUS.read_text(encoding="utf-8")
        start = text.index("def pVersusNPLane")
        end = text.index("def riemannLane", start)
        lane = text[start:end]
        for marker in (
            "GuardedCookFixedDescriptionIndexABIExact",
            "ConcreteTapeFixedLocalKernelTablesExact",
            "CodedFiniteStandardLinkedStructuralSimulationExact",
            "CodedFiniteStandardLinkedRunSimulationExact",
            "CodedFiniteStandardReturnLinkFreshnessExact",
            "ConcreteTapeStandardClockExact",
        ):
            self.assertIn(marker, lane)


if __name__ == "__main__":
    unittest.main()
