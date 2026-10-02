import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic
import NSBControl.Rational345RealRadius4
import NSBControl.Rational345QuadraticODE

/-!
# R830 quadratic packaging of the literal radius-four field

The literal radius-four field is linear plus the diagonal of a bilinear map.
We package the viscous term as a complex linear map and the projected
nonlinearity as a complex bilinear map.  Since the carrier is finite
dimensional, both are automatically continuous.  Restricting scalars from C
to R gives exactly the real quadratic field consumed by the existing Picard
owner.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345RealRadius4Quadratic

open Rational345RealRadius4

theorem viscous_add (u v : State) :
    viscousLinear (u + v) = viscousLinear u + viscousLinear v := by
  funext k j
  simp only [viscousLinear]
  split_ifs <;> simp
  ring

theorem viscous_smul (c : ℂ) (u : State) :
    viscousLinear (c • u) = c • viscousLinear u := by
  funext k j
  simp only [viscousLinear]
  split_ifs <;> simp
  ring

def viscousLinearMap : State →ₗ[ℂ] State where
  toFun := viscousLinear
  map_add' := viscous_add
  map_smul' := viscous_smul

------------------------------------------------------------------------
-- Bilinearity of the literal projected convolution.
------------------------------------------------------------------------

theorem projectedBilinear_add_left (u v w : State) :
    projectedBilinear (u + v) w =
      projectedBilinear u w + projectedBilinear v w := by
  funext k j
  simp only [projectedBilinear]
  split_ifs
  · simp
  · simp only [projectedOrderedBilinear, leray, bilinearDot,
      Finset.sum_add_distrib]
    simp
    ring

theorem projectedBilinear_smul_left (c : ℂ) (u v : State) :
    projectedBilinear (c • u) v = c • projectedBilinear u v := by
  funext k j
  simp only [projectedBilinear]
  split_ifs
  · simp
  · simp only [projectedOrderedBilinear, leray, bilinearDot]
    simp
    ring

theorem projectedBilinear_add_right (u v w : State) :
    projectedBilinear u (v + w) =
      projectedBilinear u v + projectedBilinear u w := by
  funext k j
  simp only [projectedBilinear]
  split_ifs
  · simp
  · simp only [projectedOrderedBilinear, leray, bilinearDot,
      Finset.sum_add_distrib]
    simp
    ring

theorem projectedBilinear_smul_right (c : ℂ) (u v : State) :
    projectedBilinear u (c • v) = c • projectedBilinear u v := by
  funext k j
  simp only [projectedBilinear]
  split_ifs
  · simp
  · simp only [projectedOrderedBilinear, leray, bilinearDot]
    simp
    ring

theorem projectedBilinear_isBilinear :
    IsBilinearMap ℂ projectedBilinear where
  add_left := projectedBilinear_add_left
  smul_left := projectedBilinear_smul_left
  add_right := projectedBilinear_add_right
  smul_right := projectedBilinear_smul_right

/-- Finite dimensionality upgrades the algebraic bilinear convolution to a
continuous bilinear map without any new NS estimate. -/
noncomputable def projectedBilinearCLM :
    State →L[ℂ] State →L[ℂ] State :=
  projectedBilinear_isBilinear.toContinuousBilinearMap

noncomputable def viscousCLM : State →L[ℂ] State :=
  ⟨viscousLinearMap, LinearMap.continuous_of_finiteDimensional viscousLinearMap⟩

theorem projectedBilinearCLM_apply (u v : State) :
    projectedBilinearCLM u v = projectedBilinear u v := rfl

theorem viscousCLM_apply (u : State) :
    viscousCLM u = viscousLinear u := rfl

/-- The continuous quadratic package is still the literal repository field. -/
theorem galerkinField_eq_continuous_quadratic (u : State) :
    galerkinField u = viscousCLM u + projectedBilinearCLM u u := by
  rw [viscousCLM_apply, projectedBilinearCLM_apply]
  exact galerkinField_eq_linear_add_bilinear u

/-- As a real-time vector field, the literal Galerkin field is C1. -/
theorem galerkinField_contDiff_real :
    ContDiff ℝ 1 galerkinField := by
  rw [show galerkinField =
      fun u : State => (viscousCLM.restrictScalars ℝ) u +
        ((projectedBilinearCLM.bilinearRestrictScalars ℝ) u) u by
    funext u
    simpa using galerkinField_eq_continuous_quadratic u]
  exact
    (viscousCLM.restrictScalars ℝ).contDiff.add
      ((projectedBilinearCLM.bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp
        (contDiff_id.prodMk contDiff_id))

/-- O1 analytic endpoint: the actual real radius-four field has a local
integral curve through every state, in particular the 3-4-5 snapshot. -/
theorem exists_local_solution (u₀ : State) :
    ∃ (u : ℝ → State),
      u 0 = u₀ ∧
      ∃ ε > 0,
        ∀ t ∈ Set.Ioo (-ε) ε,
          HasDerivAt u (galerkinField (u t)) t := by
  exact
    Rational345LocalODE.exists_local_solution
      (galerkinField_contDiff_real.contDiffAt)

end Rational345RealRadius4Quadratic
end NSBControl
