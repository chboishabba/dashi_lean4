#!/usr/bin/env python3
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
RESOLUTION = ROOT / "MillenniumExternal" / "ProofResolutionMaxCut.lean"
FRONTIER = ROOT / "MillenniumExternal" / "ExternalTargetFrontier.lean"
CENSUS = ROOT / "MillenniumExternal" / "TerminalCensus.lean"


class MillenniumPNPVirtualFrontierTests(unittest.TestCase):
    def test_resolution_tracks_live_behavioral_self_fix_frontier(self):
        text = RESOLUTION.read_text(encoding="utf-8")
        for donor in (
            "PNotEqualsNPCodedLiteralResourceCompilerAnchoredNoGoExact.anchoredLiteralStructuralResourceImpossible",
            "PNotEqualsNPLiteralSelfCodeGrowthNoGoExact.strictCodeGrowthKillsLiteralFixedPoint",
            "PNotEqualsNPKleeneSpecializationFixedPointExact.fixedPointProgramCorrect",
            "PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact.q2PrimitiveExecutionErasesQuotedProgram",
            "PNotEqualsNPCodedCandidateExactPhaseBoundaryExact.candidatePhaseEndpointTransitionNothing",
            "CodedFiniteStandardExactPhaseSizeExact.phaseLiftRuleCountExact",
            "CodedFiniteUnaryCursorExact.cursorStopKeyFresh",
            "CodedFiniteBitStreamLookupExact.lookupCode",
            "GuardedCookFiniteBitTableGeneratorExact.cookBitAtQueryAnswerExact",
            "ConcreteTapeCookLevinStateWidthLowerExact.stateWidthBelowGuardedCookBitCode",
            "PNotEqualsNPXORCountdownMicrocodeExact.sameXorOutputDifferentBorrow",
        ):
            self.assertIn(donor, text)
        self.assertIn("pnp_resolution_uses_behavioral_self_fix_maxcut", text)

        start = text.index("def pVersusNPResolution")
        end = text.index("def rhResolution", start)
        lane = text[start:end]
        self.assertIn("resolvedSourceTerm := none", lane)
        self.assertIn("newMathematicsPermitted := false", lane)

    def test_frontier_names_behavioral_fixed_point_and_resource_closure(self):
        text = FRONTIER.read_text(encoding="utf-8")
        start = text.index("problem := .pVersusNP")
        end = text.index("problem := .riemann", start)
        lane = text[start:end]
        for marker in (
            "behavioural Kleene self-specialization",
            "CodedFiniteStandardTM",
            "raw-code growth",
            "one-hot state-width",
            "quoted program",
            "resource fixed point T*",
            "IIT phi is not complexity hardness evidence",
        ):
            self.assertIn(marker, lane)
        self.assertIn("state := .proofResolutionPending", lane)
        self.assertNotIn("state := .greenExact", lane)

    def test_census_points_to_current_producer_owners(self):
        text = CENSUS.read_text(encoding="utf-8")
        start = text.index("def pVersusNPLane")
        end = text.index("def riemannLane", start)
        lane = text[start:end]
        for marker in (
            "PNotEqualsNPCodedCandidateExactPhaseBoundaryExact",
            "CodedFiniteStandardExactPhaseSizeExact",
            "CodedFiniteUnaryCursorExact",
            "CodedFiniteBitStreamLookupExact",
            "GuardedCookFiniteBitTableGeneratorExact",
            "ConcreteTapeCookLevinStateWidthLowerExact",
            "CandidateActualSelfInstantiationBoundaryExact",
            "PNotEqualsNPXORCountdownMicrocodeExact",
            "behavioural fixed points",
            "budget T*",
        ):
            self.assertIn(marker, lane)


if __name__ == "__main__":
    unittest.main()
