#!/usr/bin/env python3
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
EXACT_NS = ROOT / "ExternalClayNS" / "LeanDojoExactTerminal.lean"
FORCE = ROOT / "ExternalClayNS" / "LeanDojoForceDecayQuantitative.lean"
MOMENTUM = ROOT / "ExternalClayNS" / "LeanDojoMomentumTransport.lean"
DIVERGENCE = ROOT / "ExternalClayNS" / "LeanDojoDivergenceTransport.lean"
ENERGY = ROOT / "ExternalClayNS" / "LeanDojoEnergyTransport.lean"
REGRESSION = ROOT / "ExternalClayNS" / "LeanDojoSameObjectRegression.lean"
OBSOLETE_NS = ROOT / "ExternalClayNS" / "LeanDojoCComparatorBridge.lean"
EXACT = ROOT / "MillenniumExternal" / "ExactTargetSurface.lean"
FRONTIER = ROOT / "MillenniumExternal" / "ExternalTargetFrontier.lean"
SAME_OBJECT_CUT = ROOT / "MillenniumExternal" / "SameObjectMaxCut.lean"
RESOLUTION = ROOT / "MillenniumExternal" / "ProofResolutionMaxCut.lean"


class MillenniumSubmissionSurfaceTests(unittest.TestCase):
    def test_ns_exact_terminal_supersedes_transport_frontier(self):
        for path in (EXACT_NS, FORCE, MOMENTUM, DIVERGENCE, ENERGY, REGRESSION):
            self.assertTrue(path.exists(), f"missing paid NS owner: {path.name}")
        self.assertFalse(OBSOLETE_NS.exists(), "obsolete conditional NS frontier must stay removed")

        terminal = EXACT_NS.read_text(encoding="utf-8")
        force = FORCE.read_text(encoding="utf-8")
        regression = REGRESSION.read_text(encoding="utf-8")

        for theorem in (
            "theorem leanDojoR3Solution_to_comparator",
            "theorem leanDojoPeriodicSolution_to_comparator",
            "theorem dashiExactFeffermanC : MillenniumNavierStokes.FeffermanC",
            "theorem dashiExactFeffermanD : MillenniumNavierStokes.FeffermanD",
            "#print axioms dashiExactFeffermanC",
            "#print axioms dashiExactFeffermanD",
        ):
            self.assertIn(theorem, terminal)

        for paid in (
            "comparatorForceDecay_to_leanDojo",
            "comparatorPeriodicForceDecay_to_leanDojo",
            "spacetimeDerivativeVector_eq_fullJet_apply",
            "norm_targetJet_le_sourceJet",
        ):
            self.assertIn(paid, force)

        self.assertIn("#check dashiExactFeffermanC", regression)
        self.assertIn("#check dashiExactFeffermanD", regression)
        self.assertNotIn("sorry", terminal)
        self.assertNotIn("axiom ", terminal)

    def test_exact_p_negative_branch_needs_only_one_language_outside_p(self):
        text = EXACT.read_text(encoding="utf-8")
        self.assertIn("theorem clayPNotEqualsNP_of_language_outside_p", text)
        self.assertIn("Millennium.InNondeterministicPolynomialTime", text)
        self.assertIn("Millennium.InPolynomialTime", text)
        self.assertIn("Millennium.ClayPVersusNP.Formulations.NegativeBranch", text)
        self.assertIn("#print axioms clayPNotEqualsNP_of_language_outside_p", text)

    def test_bsd_finite_rank_is_derived_not_an_adapter_field(self):
        text = EXACT.read_text(encoding="utf-8")
        self.assertIn("theorem leanDojoRank_finite_of_projective_fg", text)
        self.assertIn("theorem leanDojoBSDFiniteRank_of_dashi", text)
        self.assertIn("Module.Finite.base_change", text)
        self.assertIn("Cardinal.toENat_ne_top", text)
        self.assertIn("projective_fg E", text)

        start = text.index("structure BSDLeanDojoSameObjectWeld")
        end = text.index("theorem clayBirchSwinnertonDyer_of_dashi", start)
        weld = text[start:end]
        self.assertIn("rankExistence_of_dashi", weld)
        self.assertNotIn("finiteRank :", weld)

        compiler = text[text.index("theorem clayBirchSwinnertonDyer_of_dashi"):]
        self.assertIn("leanDojoBSDFiniteRank_of_dashi bg.algebraic", compiler)

    def test_completion_pass_forbids_reopening_math_on_faithful_live_lanes(self):
        same = SAME_OBJECT_CUT.read_text(encoding="utf-8")
        resolution = RESOLUTION.read_text(encoding="utf-8")

        for lane in (
            "pVersusNPSameObjectCut",
            "riemannSameObjectCut",
            "navierStokesSameObjectCut",
            "bsdSameObjectCut",
        ):
            start = same.index(f"def {lane}")
            next_def = same.find("\ndef ", start + 5)
            block = same[start:] if next_def == -1 else same[start:next_def]
            self.assertIn("remaining := .transportOnly", block)
            self.assertNotIn("remaining := .mathematics", block)

        for lane in (
            "pVersusNPResolution",
            "rhResolution",
            "navierStokesResolution",
            "bsdResolution",
        ):
            start = resolution.index(f"def {lane}")
            next_def = resolution.find("\ndef ", start + 5)
            block = resolution[start:] if next_def == -1 else resolution[start:next_def]
            self.assertIn("newMathematicsPermitted := false", block)

        self.assertIn("navierStokes_source_term_is_resolved", resolution)
        self.assertIn('some "DASHILiteralClayNS.dashiExactFeffermanC|D"', resolution)
        self.assertIn("pnp_rh_bsd_still_require_donor_resolution", resolution)

    def test_fail_closed_frontier_uses_resolution_not_red_math(self):
        frontier = FRONTIER.read_text(encoding="utf-8")

        ns_start = frontier.index("problem := .navierStokes")
        ns_end = frontier.index("problem := .hodge", ns_start)
        ns = frontier[ns_start:ns_end]
        self.assertIn("frontier := .proved", ns)
        self.assertIn("state := .sourceExactKernelPending", ns)
        self.assertIn("dashiExactFeffermanC", ns)
        self.assertIn("dashiExactFeffermanD", ns)
        self.assertNotIn("state := .greenExact", ns)

        for problem, next_problem in (
            (".pVersusNP", ".riemann"),
            (".riemann", ".navierStokes"),
            (".birchSwinnertonDyer", ".yangMills"),
        ):
            start = frontier.index(f"problem := {problem}")
            end = frontier.index(f"problem := {next_problem}", start)
            block = frontier[start:end]
            self.assertIn("state := .proofResolutionPending", block)
            self.assertIn("frontier := .proofResolution", block)
            self.assertNotIn("state := .redMath", block)
            self.assertNotIn("state := .greenExact", block)

        bsd_start = frontier.index("problem := .birchSwinnertonDyer")
        bsd_end = frontier.index("problem := .yangMills", bsd_start)
        self.assertIn("Rank.Existence", frontier[bsd_start:bsd_end])
        self.assertIn("faithful_active_lanes_not_red_math", frontier)


if __name__ == "__main__":
    unittest.main()
