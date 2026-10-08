import LeanDojoSameObjectCore
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

open ClaySpec
open NavierStokes

namespace DASHILiteralClayNS

def pairLeanSpacetimeLinearEquiv : SpaceTime ≃ₗ[ℝ] Spacetime3 where
  toFun := pairToLeanSpacetime
  invFun := leanSpacetimeToPair
  left_inv := leanSpacetimeToPair_leftInverse_apply
  right_inv := pairToLeanSpacetime_rightInverse_apply
  map_add' x y := by
    ext i
    fin_cases i <;> simp [pairToLeanSpacetime, spacetime_point]
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [pairToLeanSpacetime, spacetime_point]

def pairLeanSpacetimeContinuousLinearEquiv : SpaceTime ≃L[ℝ] Spacetime3 :=
  pairLeanSpacetimeLinearEquiv.toContinuousLinearEquiv

@[simp] theorem pairLeanSpacetimeContinuousLinearEquiv_apply (z : SpaceTime) :
    pairLeanSpacetimeContinuousLinearEquiv z = pairToLeanSpacetime z := rfl

@[simp] theorem pairLeanSpacetimeContinuousLinearEquiv_symm_apply (z : Spacetime3) :
    pairLeanSpacetimeContinuousLinearEquiv.symm z = leanSpacetimeToPair z := rfl

theorem comparatorFieldToLean_eq_comp_symm
    {E : Type*} (f : R3 → ℝ → E) :
    comparatorFieldToLean f =
      Function.uncurry f ∘ pairLeanSpacetimeContinuousLinearEquiv.symm := by
  funext z
  rfl

theorem leanFieldToComparator_uncurry_eq_comp
    {E : Type*} (f : Spacetime3 → E) :
    Function.uncurry (leanFieldToComparator f) =
      f ∘ pairLeanSpacetimeContinuousLinearEquiv := by
  funext z
  rfl

theorem contDiffOn_comparatorFieldToLean
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : R3 → ℝ → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) nonnegativeTime) :
    ContDiffOn ℝ ∞ (comparatorFieldToLean f)
      (global_spacetime_domain 3) := by
  rw [comparatorFieldToLean_eq_comp_symm]
  apply hf.comp pairLeanSpacetimeContinuousLinearEquiv.symm.contDiff.contDiffOn
  intro z hz
  exact (leanSpacetimeToPair_nonnegative_iff z).2 hz

theorem contDiffOn_leanFieldToComparator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Spacetime3 → E}
    (hf : ContDiffOn ℝ ∞ f (global_spacetime_domain 3)) :
    ContDiffOn ℝ ∞ (Function.uncurry (leanFieldToComparator f))
      nonnegativeTime := by
  rw [leanFieldToComparator_uncurry_eq_comp]
  apply hf.comp pairLeanSpacetimeContinuousLinearEquiv.contDiff.contDiffOn
  intro z hz
  exact (pairToLeanSpacetime_nonnegative_iff z).2 hz

@[simp] theorem pairToLeanSpacetime_timeDirection :
    pairToLeanSpacetime ClaySpec.timeDirection =
      standard_basis (n := 4) (0 : Fin 4) := by
  ext i
  fin_cases i <;> simp [pairToLeanSpacetime, ClaySpec.timeDirection, spacetime_point,
    standard_basis]

@[simp] theorem pairToLeanSpacetime_spatialDirection (i : Fin 3) :
    pairToLeanSpacetime (ClaySpec.spatialDirection i) =
      standard_basis (n := 4) i.succ := by
  ext j
  fin_cases j <;> simp [pairToLeanSpacetime, ClaySpec.spatialDirection,
    ClaySpec.spatialBasis, spacetime_point, standard_basis]

@[simp] theorem leanSpacetimeToPair_timeBasis :
    leanSpacetimeToPair (standard_basis (n := 4) (0 : Fin 4)) =
      ClaySpec.timeDirection := by
  apply pairToLeanSpacetime_leftInverse.injective
  simp

@[simp] theorem leanSpacetimeToPair_spatialBasis (i : Fin 3) :
    leanSpacetimeToPair (standard_basis (n := 4) i.succ) =
      ClaySpec.spatialDirection i := by
  apply pairToLeanSpacetime_leftInverse.injective
  simp

@[simp] theorem time_add_int_spatialBasis
    (z : Spacetime3) (i : Fin 3) (n : ℤ) :
    time (z + n • standard_basis (n := 4) i.succ) = time z := by
  simp [time, standard_basis]

@[simp] theorem space_add_int_spatialBasis
    (z : Spacetime3) (i : Fin 3) (n : ℤ) :
    space (z + n • standard_basis (n := 4) i.succ) =
      space z + n • standard_basis (n := 3) i := by
  ext j
  simp [space, standard_basis]

end DASHILiteralClayNS
