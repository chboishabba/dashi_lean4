import LeanDojoSameObjectCore
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Linear/calculus form of the exact spacetime identity

The product `(space,time)` and LeanDojo's time-first `Fin 4` coordinate space
are related by a coordinate permutation.  Recording that permutation as a
continuous linear equivalence lets the standard Mathlib chain rule transport
all higher derivatives and smoothness facts.
-/

noncomputable section

open ClaySpec
open NavierStokes

namespace DASHILiteralClayNS

/-- The exact carrier equivalence is linear: it only permutes the four real
coordinates. -/
def pairLeanSpacetimeLinearEquiv : SpaceTime ≃ₗ[ℝ] Spacetime3 where
  toFun := pairToLeanSpacetime
  invFun := leanSpacetimeToPair
  left_inv := leanSpacetimeToPair_leftInverse_apply
  right_inv := pairToLeanSpacetime_rightInverse_apply
  map_add' x y := by
    ext i
    fin_cases i <;>
      simp [pairToLeanSpacetime, spacetime_point]
  map_smul' c x := by
    ext i
    fin_cases i <;>
      simp [pairToLeanSpacetime, spacetime_point]

/-- Finite-dimensional real linear equivalences are automatically continuous.
This is the calculus-level same-object identifier used below. -/
def pairLeanSpacetimeContinuousLinearEquiv : SpaceTime ≃L[ℝ] Spacetime3 :=
  pairLeanSpacetimeLinearEquiv.toContinuousLinearEquiv

@[simp] theorem pairLeanSpacetimeContinuousLinearEquiv_apply (z : SpaceTime) :
    pairLeanSpacetimeContinuousLinearEquiv z = pairToLeanSpacetime z := rfl

@[simp] theorem pairLeanSpacetimeContinuousLinearEquiv_symm_apply (z : Spacetime3) :
    pairLeanSpacetimeContinuousLinearEquiv.symm z = leanSpacetimeToPair z := rfl

/-- Field transport is literally right-composition with the inverse continuous
linear equivalence. -/
theorem comparatorFieldToLean_eq_comp_symm
    {E : Type*} (f : R3 → ℝ → E) :
    comparatorFieldToLean f =
      Function.uncurry f ∘ pairLeanSpacetimeContinuousLinearEquiv.symm := by
  funext z
  rfl

/-- Pullback to the comparator carrier is right-composition with the forward
continuous linear equivalence. -/
theorem leanFieldToComparator_uncurry_eq_comp
    {E : Type*} (f : Spacetime3 → E) :
    Function.uncurry (leanFieldToComparator f) =
      f ∘ pairLeanSpacetimeContinuousLinearEquiv := by
  funext z
  rfl

/-- Smoothness transports from the frozen product-coordinate field to the
LeanDojo field on the corresponding closed half-space. -/
theorem contDiffOn_comparatorFieldToLean
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : R3 → ℝ → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) nonnegativeTime) :
    ContDiffOn ℝ ∞ (comparatorFieldToLean f)
      (global_spacetime_domain 3) := by
  rw [comparatorFieldToLean_eq_comp_symm]
  apply hf.comp
    pairLeanSpacetimeContinuousLinearEquiv.symm.contDiff.contDiffOn
  intro z hz
  exact (leanSpacetimeToPair_nonnegative_iff z).2 hz

/-- Conversely, LeanDojo closed-half-space smoothness pulls back to the frozen
product-coordinate field. -/
theorem contDiffOn_leanFieldToComparator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Spacetime3 → E}
    (hf : ContDiffOn ℝ ∞ f (global_spacetime_domain 3)) :
    ContDiffOn ℝ ∞ (Function.uncurry (leanFieldToComparator f))
      nonnegativeTime := by
  rw [leanFieldToComparator_uncurry_eq_comp]
  apply hf.comp
    pairLeanSpacetimeContinuousLinearEquiv.contDiff.contDiffOn
  intro z hz
  exact (pairToLeanSpacetime_nonnegative_iff z).2 hz

/-! ## Derivative directions -/

/-- Clay's positive-time direction is literally LeanDojo coordinate zero. -/
@[simp] theorem pairToLeanSpacetime_timeDirection :
    pairToLeanSpacetime ClaySpec.timeDirection =
      standard_basis (n := 4) (0 : Fin 4) := by
  ext i
  fin_cases i <;>
    simp [pairToLeanSpacetime, ClaySpec.timeDirection, spacetime_point,
      standard_basis]

/-- Clay spatial direction `i` is literally LeanDojo coordinate `i+1`. -/
@[simp] theorem pairToLeanSpacetime_spatialDirection (i : Fin 3) :
    pairToLeanSpacetime (ClaySpec.spatialDirection i) =
      standard_basis (n := 4) i.succ := by
  ext j
  fin_cases j <;>
    simp [pairToLeanSpacetime, ClaySpec.spatialDirection,
      ClaySpec.spatialBasis, spacetime_point, standard_basis]

/-- The inverse coordinate map sends LeanDojo's time basis back to the exact
Clay time direction. -/
@[simp] theorem leanSpacetimeToPair_timeBasis :
    leanSpacetimeToPair (standard_basis (n := 4) (0 : Fin 4)) =
      ClaySpec.timeDirection := by
  apply pairToLeanSpacetime_leftInverse.injective
  simp

/-- The inverse coordinate map sends each LeanDojo spatial basis vector back to
Clay's corresponding product-space direction. -/
@[simp] theorem leanSpacetimeToPair_spatialBasis (i : Fin 3) :
    leanSpacetimeToPair (standard_basis (n := 4) i.succ) =
      ClaySpec.spatialDirection i := by
  apply pairToLeanSpacetime_leftInverse.injective
  simp

/-! ## Spatial translations -/

/-- A LeanDojo spatial standard-basis translation leaves the time coordinate
unchanged. -/
@[simp] theorem time_add_int_spatialBasis
    (z : Spacetime3) (i : Fin 3) (n : ℤ) :
    time (z + n • standard_basis (n := 4) i.succ) = time z := by
  simp [time, standard_basis]

/-- Under `space`, the same four-dimensional translation is exactly the
corresponding three-dimensional integer basis translation. -/
@[simp] theorem space_add_int_spatialBasis
    (z : Spacetime3) (i : Fin 3) (n : ℤ) :
    space (z + n • standard_basis (n := 4) i.succ) =
      space z + n • standard_basis (n := 3) i := by
  ext j
  simp [space, standard_basis]

end DASHILiteralClayNS
