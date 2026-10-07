import Gap
import Problems.NavierStokes.Millennium

/-!
# Exact carrier geometry for the LeanDojo Navier--Stokes acceptance bridge

These lemmas pay representation facts only. They contain no Navier--Stokes
estimate and no breakdown/existence argument.
-/

noncomputable section

namespace DASHILiteralClayNS

open ClaySpec
open NavierStokes

/-- Pack a curried pair-spacetime field into LeanDojo's time-first ambient
spacetime by using its canonical `space` and `time` projections. -/
noncomputable def pairFieldToLeanDojo {E : Type*}
    (f : R3 → ℝ → E) : Spacetime3 → E :=
  fun z => f (NavierStokes.space z) (NavierStokes.time z)

/-- Read an ambient LeanDojo field on the ordinary pair-spacetime carrier. -/
noncomputable def leanDojoFieldToPair {E : Type*}
    (f : Spacetime3 → E) : R3 × ℝ → E :=
  fun z => f (NavierStokes.spacetime_point z.2 z.1)

/-- LeanDojo's time projection recovers the time used by `spacetime_point`. -/
@[simp] theorem leanDojo_time_spacetime_point
    (t : ℝ) (x : Space3) :
    NavierStokes.time (NavierStokes.spacetime_point t x) = t := by
  simp [NavierStokes.time, NavierStokes.spacetime_point]

/-- LeanDojo's spatial projection recovers the spatial point used by
`spacetime_point`. -/
@[simp] theorem leanDojo_space_spacetime_point
    (t : ℝ) (x : Space3) :
    NavierStokes.space (NavierStokes.spacetime_point t x) = x := by
  ext i
  simp [NavierStokes.space, NavierStokes.spacetime_point]

/-- Packing then evaluating at the canonical pair point recovers the curried
field exactly. -/
@[simp] theorem pairFieldToLeanDojo_spacetime_point {E : Type*}
    (f : R3 → ℝ → E) (x : R3) (t : ℝ) :
    pairFieldToLeanDojo f (NavierStokes.spacetime_point t x) = f x t := by
  simp [pairFieldToLeanDojo]

/-- Reading a packed field back on pair spacetime is definitionally the ordinary
uncurried field. -/
@[simp] theorem leanDojoFieldToPair_pairFieldToLeanDojo {E : Type*}
    (f : R3 → ℝ → E) :
    leanDojoFieldToPair (pairFieldToLeanDojo f) = SemanticGap.uncurryField f := by
  funext z
  simp [leanDojoFieldToPair, pairFieldToLeanDojo, SemanticGap.uncurryField]

/-- The canonical pair point lies in LeanDojo's closed spacetime domain exactly
when its time coordinate is nonnegative. -/
@[simp] theorem spacetime_point_mem_global_iff
    (t : ℝ) (x : Space3) :
    NavierStokes.spacetime_point t x ∈ NavierStokes.global_spacetime_domain 3 ↔
      0 ≤ t := by
  simp [NavierStokes.global_spacetime_domain, NavierStokes.spacetime_point]

/-- The fixed pair-to-ambient coordinate embedding is smooth. -/
theorem leanDojoPairEmbedding_contDiff :
    ContDiff ℝ ∞ (fun z : R3 × ℝ =>
      NavierStokes.spacetime_point z.2 z.1) := by
  unfold NavierStokes.spacetime_point
  fun_prop

/-- Pull any ambient smooth field back to ClaySpec's pair-spacetime carrier.
This is a generic coordinate theorem, not a fluid theorem. -/
theorem leanDojoSmooth_to_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Spacetime3 → E}
    (hg : ContDiffOn ℝ ∞ g (NavierStokes.global_spacetime_domain 3)) :
    ClaySpec.TrustBoundarySmoothOn (leanDojoFieldToPair g) := by
  unfold ClaySpec.TrustBoundarySmoothOn leanDojoFieldToPair
  exact hg.comp leanDojoPairEmbedding_contDiff.contDiffOn (by
    intro z hz
    exact (spacetime_point_mem_global_iff z.2 z.1).2 hz)

/-- ClaySpec and LeanDojo use the same literal `R3` standard basis in their
initial divergence sums. -/
theorem clayInitialDivergenceFree_to_leanDojo
    (u₀ : R3 → R3)
    (h : ClaySpec.InitialDivergenceFree u₀) :
    NavierStokesOnR3.DivergenceFreeInitial u₀ := by
  intro x
  simpa [ClaySpec.InitialDivergenceFree, ClaySpec.initialDivergence,
    NavierStokesOnR3.DivergenceFreeInitial, partial_deriv,
    ClaySpec.spatialBasis, standard_basis] using h x

end DASHILiteralClayNS
