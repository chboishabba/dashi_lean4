import Adapter
import LeanDojoCarrierGeometry
import Problems.NavierStokes.Millennium

/-!
# Direct ClaySpec -> exact LeanDojo Fefferman C max-cut

The released comparator theorem is already welded to the independently frozen
`ClaySpec` representation by `Gap.lean`:

* comparator data -> `ClaySpec.AdmissibleDataR3`;
* `ClaySpec.ClaySolutionR3` -> the exact comparator solution structure.

`LeanDojoCarrierGeometry` additionally pays the literal spatial carrier,
pair-spacetime packing round-trip, domain membership, and initial-divergence
identity.  The external acceptance seam therefore does not reopen any of those
facts.

The residual obligations are now only:

1. ClaySpec condition-(4) derivative-decay notation -> LeanDojo condition (4);
2. ClaySpec condition-(5) pair-spacetime notation -> LeanDojo time-first `Fin 4` condition (5);
3. LeanDojo global smooth finite-energy solution -> literal ClaySpec solution.

No fluid estimate is introduced here.
-/

noncomputable section

namespace DASHILiteralClayNS

open ClaySpec
open NavierStokes

/-- Condition-(4) derivative-packaging transport only. Smoothness is already a
literal common predicate and divergence is paid separately by
`clayInitialDivergenceFree_to_leanDojo`. -/
def ClayInitialDecayToLeanDojo : Prop :=
  ∀ u₀ : R3 → R3,
    ContDiff ℝ ∞ u₀ →
    ClaySpec.InitialRapidDecay u₀ →
      NavierStokesOnR3.SmoothRapidDecayInitial u₀

/-- Condition-(5) representation transport only, after `Gap.lean` has already
proved the ClaySpec force smoothness and derivative-decay clauses. -/
def ClayForceToLeanDojo : Prop :=
  ∀ f : R3 → ℝ → R3,
    ClaySpec.TrustBoundarySmoothOn (SemanticGap.uncurryField f) →
    ClaySpec.ForceRapidDecayR3 (SemanticGap.uncurryField f) →
      NavierStokesOnR3.SmoothRapidDecayForce (pairFieldToLeanDojo f)

/-- Solution-carrier transport only.

The output is a literal `ClaySpec.ClaySolutionR3`; the already-proved
`SemanticGap.claySolutionR3_to_comparator` then supplies the released
comparator solution required for the contradiction. -/
def LeanDojoSolutionToClaySpec : Prop :=
  ∀ (ν : ℝ) (ν_pos : ν > 0)
    (u₀ : NavierStokesOnR3.InitialVelocity)
    (f : R3 → ℝ → R3)
    (hdiv : NavierStokesOnR3.DivergenceFreeInitial u₀)
    (sol : GlobalSmoothSolution
      (NavierStokesOnR3.equations ν ν_pos u₀ hdiv
        (pairFieldToLeanDojo f))),
      NavierStokesOnR3.FiniteEnergy sol.velocity →
        ClaySpec.ClaySolutionR3 ν u₀ (SemanticGap.uncurryField f)
          (leanDojoFieldToPair sol.velocity)
          (leanDojoFieldToPair sol.pressure)

/-- Exact post-archaeology representation frontier. Every field is now a
strictly residual notation/carrier transport; comparator semantics, spatial
carrier identity, domain round-trip and initial divergence are already paid. -/
structure LeanDojoCTransportFrontier : Prop where
  initialDecay : ClayInitialDecayToLeanDojo
  force : ClayForceToLeanDojo
  solution : LeanDojoSolutionToClaySpec

/-- The released comparator C theorem, already-paid same-object welds, and only
the three residual transports above compose to the exact pinned Fefferman C
target. -/
theorem leanDojoFeffermanC_of_transport
    (w : LeanDojoCTransportFrontier) :
    MillenniumNavierStokes.FeffermanC := by
  intro ν ν_pos
  obtain ⟨u₀, f, hu₀, hf, hno⟩ :=
    SemanticGapAdapter.openAIComparatorOptionC ν ν_pos
  have hClayData := SemanticGap.admissibleDataR3_of_comparator hu₀ hf
  rcases hClayData with ⟨huSmooth, huDiv, huRapid, hfSmooth, hfRapid⟩
  have hinit := w.initialDecay u₀ huSmooth huRapid
  have hdiv := clayInitialDivergenceFree_to_leanDojo u₀ huDiv
  have hforce := w.force f hfSmooth hfRapid
  refine ⟨u₀, pairFieldToLeanDojo f, hinit, hdiv, hforce, ?_⟩
  intro hdiv' hExists
  apply hno
  rcases hExists with ⟨sol, _hsmooth, henergy⟩
  have hClay := w.solution ν ν_pos u₀ f hdiv' sol henergy
  have hComparator := SemanticGap.claySolutionR3_to_comparator hClay
  rw [SemanticGap.curryField_uncurryField] at hComparator
  exact ⟨_, _, hComparator⟩

#print axioms leanDojoFeffermanC_of_transport

end DASHILiteralClayNS
