import Adapter
import Problems.NavierStokes.Millennium

/-!
# Direct ClaySpec -> exact LeanDojo Fefferman C max-cut

The released comparator theorem is already welded to the independently frozen
`ClaySpec` representation by `Gap.lean`:

* comparator data -> `ClaySpec.AdmissibleDataR3`;
* `ClaySpec.ClaySolutionR3` -> the exact comparator solution structure.

Therefore the external acceptance seam must not reopen comparator PDE semantics.
The remaining obligations are purely representation transport between:

* `ClaySpec` pair spacetime `R3 × ℝ`, and
* LeanDojo's time-first ambient `EuclideanSpace ℝ (Fin 4)` spacetime.

The spatial carrier itself is already literally `EuclideanSpace ℝ (Fin 3)`.
No fluid estimate is introduced here.
-/

noncomputable section

namespace DASHILiteralClayNS

open ClaySpec
open NavierStokes

/-- Pack a curried `(x,t)` force into LeanDojo's time-first ambient spacetime. -/
noncomputable def comparatorForceToLeanDojo
    (f : R3 → ℝ → R3) : ForceField 3 :=
  fun z => f (NavierStokes.space z) (NavierStokes.time z)

/-- Read a LeanDojo velocity field on ClaySpec's pair-spacetime carrier. -/
noncomputable def leanDojoVelocityToClay
    (u : VelocityField 3) : ClaySpec.Velocity :=
  fun z => u (NavierStokes.spacetime_point z.2 z.1)

/-- Read a LeanDojo pressure field on ClaySpec's pair-spacetime carrier. -/
noncomputable def leanDojoPressureToClay
    (p : PressureField 3) : ClaySpec.Pressure :=
  fun z => p (NavierStokes.spacetime_point z.2 z.1)

/-- Condition-(4) and initial-divergence notation transport only.

`Gap.lean` has already proved these ClaySpec clauses from the released
comparator hypotheses.  This interface therefore contains no comparator object
and no fluid estimate. -/
def ClayInitialToLeanDojo : Prop :=
  ∀ u₀ : R3 → R3,
    ContDiff ℝ ∞ u₀ →
    ClaySpec.InitialDivergenceFree u₀ →
    ClaySpec.InitialRapidDecay u₀ →
      NavierStokesOnR3.SmoothRapidDecayInitial u₀ ∧
      NavierStokesOnR3.DivergenceFreeInitial u₀

/-- Condition-(5) representation transport only, after `Gap.lean` has already
proved the ClaySpec force smoothness and derivative-decay clauses. -/
def ClayForceToLeanDojo : Prop :=
  ∀ f : R3 → ℝ → R3,
    ClaySpec.TrustBoundarySmoothOn (SemanticGap.uncurryField f) →
    ClaySpec.ForceRapidDecayR3 (SemanticGap.uncurryField f) →
      NavierStokesOnR3.SmoothRapidDecayForce (comparatorForceToLeanDojo f)

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
        (comparatorForceToLeanDojo f))),
      NavierStokesOnR3.FiniteEnergy sol.velocity →
        ClaySpec.ClaySolutionR3 ν u₀ (SemanticGap.uncurryField f)
          (leanDojoVelocityToClay sol.velocity)
          (leanDojoPressureToClay sol.pressure)

/-- Exact post-archaeology representation frontier.  Every field is now a
ClaySpec <-> LeanDojo carrier/notation transport; comparator semantics are
already paid by `Gap.lean`. -/
structure LeanDojoCTransportFrontier : Prop where
  initial : ClayInitialToLeanDojo
  force : ClayForceToLeanDojo
  solution : LeanDojoSolutionToClaySpec

/-- The released comparator C theorem, the already-paid comparator -> ClaySpec
same-object weld, and only the three ClaySpec <-> LeanDojo transports above
compose to the exact pinned Fefferman C target. -/
theorem leanDojoFeffermanC_of_transport
    (w : LeanDojoCTransportFrontier) :
    MillenniumNavierStokes.FeffermanC := by
  intro ν ν_pos
  obtain ⟨u₀, f, hu₀, hf, hno⟩ :=
    SemanticGapAdapter.openAIComparatorOptionC ν ν_pos
  have hClayData := SemanticGap.admissibleDataR3_of_comparator hu₀ hf
  rcases hClayData with ⟨huSmooth, huDiv, huRapid, hfSmooth, hfRapid⟩
  have hinit := w.initial u₀ huSmooth huDiv huRapid
  have hforce := w.force f hfSmooth hfRapid
  refine ⟨u₀, comparatorForceToLeanDojo f,
    hinit.1, hinit.2, hforce, ?_⟩
  intro hdiv hExists
  apply hno
  rcases hExists with ⟨sol, _hsmooth, henergy⟩
  have hClay := w.solution ν ν_pos u₀ f hdiv sol henergy
  have hComparator := SemanticGap.claySolutionR3_to_comparator hClay
  rw [SemanticGap.curryField_uncurryField] at hComparator
  exact ⟨_, _, hComparator⟩

#print axioms leanDojoFeffermanC_of_transport

end DASHILiteralClayNS
