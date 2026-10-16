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
            "CodedStandardCanonicalInputExact.canonicalStandardStart",
            "CodedStandardHaltingPolynomialDeciderExact.GuardedExecutionReceipt",
            "PNotEqualsNPHaltingCodedCandidateBridgeExact.haltingWitnessToPolynomiallyClockedCandidate",
            "GuardedCookFiniteBitTableSelfCodeNoGoExact.tableBakedGeneratorCannotBeDescriptionCode",
            "PNotEqualsNPCodedLiteralResourceCompilerAnchoredNoGoExact.anchoredLiteralStructuralResourceImpossible",
            "PNotEqualsNPKleeneSpecializationFixedPointExact.fixedPointProgramCorrect",
            "PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact.q2PrimitiveExecutionErasesQuotedProgram",
            "CodedFiniteStandardSelfDelimitingCodeExact.selfDelimitingRoundTrip",
            "CodedFiniteStandardRawInterpreterExact.runActualCodeReducesToRawView",
            "PNotEqualsNPCodedCandidateExactPhaseBoundaryExact.candidatePhaseEndpointTransitionNothing",
            "CodedFiniteStandardExactPhaseSizeExact.phaseLiftRuleCountExact",
            "PNotEqualsNPBinaryCountdownCostExact.countdownWorkBound",
            "PNotEqualsNPBinaryCountdownExactRunExact.countdownExactRun",
            "PNotEqualsNPPhaseCounterParetoExact.compactCounterSingleDecrementBound",
            "PNotEqualsNPPhaseCounterParetoExact.phaseExpandedRuleCountExact",
            "PNotEqualsNPXORCountdownMicrocodeExact.sameXorOutputDifferentBorrow",
        ):
            self.assertIn(donor, text)
        self.assertIn("pnp_resolution_uses_behavioral_self_fix_maxcut", text)

        start = text.index("def pVersusNPResolution")
        end = text.index("def rhResolution", start)
        lane = text[start:end]
        self.assertIn("resolvedSourceTerm := none", lane)
        self.assertIn("newMathematicsPermitted := false", lane)

    def test_frontier_names_self_delimiting_behavioral_fixed_point(self):
        text = FRONTIER.read_text(encoding="utf-8")
        start = text.index("problem := .pVersusNP")
        end = text.index("problem := .riemann", start)
        lane = text[start:end]
        for marker in (
            "actual-halting CodedFiniteStandardTM",
            "self-delimiting",
            "raw interpreter",
            "behavioural specializer",
            "phase-expanded",
            "compact XOR/ripple counter",
            "resource fixed point",
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
            "CodedStandardCanonicalInputExact",
            "CodedFiniteStandardSelfDelimitingCodeExact",
            "CodedFiniteStandardRawInterpreterExact",
            "PNotEqualsNPKleeneSpecializationFixedPointExact",
            "PNotEqualsNPBinaryCountdownExactRunExact",
            "PNotEqualsNPPhaseCounterParetoExact",
            "behavioural",
        ):
            self.assertIn(marker, lane)


if __name__ == "__main__":
    unittest.main()
