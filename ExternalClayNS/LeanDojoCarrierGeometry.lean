import Gap
import Problems.NavierStokes.Millennium

/-!
# Exact carrier geometry for the LeanDojo Navier--Stokes acceptance bridge

These lemmas pay representation facts only.  They contain no Navier--Stokes
estimate and no breakdown/existence argument.
-/

noncomputable section

namespace DASHILiteralClayNS

open ClaySpec
open NavierStokes

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

/-- The pair-to-ambient map is a left inverse for the two projections. -/
@[simp] theorem comparatorForceToLeanDojo_spacetime_point
    (f : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    (fun z : ForceField 3 => z)
      (fun z => f (NavierStokes.space z) (NavierStokes.time z))
      (NavierStokes.spacetime_point t x) = f x t := by
  simp

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
