import Integration.MoonshineEta24CuspPinned
import Integration.MoonshineLevelOneWeightZeroPinned

/-!
# Specialized one-dimensionality of level-one weight-12 cusp forms

At the pinned Mathlib v4.28.0 dependency the later dimension-formula package is
absent.  For the Delta identity we only need one specialization:

  every f : CuspForm SL(2,Z) 12 is a scalar multiple of eta^24.

The proof divides by the nonvanishing eta^24 cusp form, obtains a bounded
holomorphic weight-zero modular form, applies the locally ported weight-zero
constancy theorem, and multiplies back.

No general dimension formula is reconstructed.
-/

namespace Integration.MoonshineWeight12Eta24ScalarPinned

open Function Complex Filter Asymptotics
open UpperHalfPlane ModularGroup SlashInvariantForm ModularForm
open scoped MatrixGroups Topology Real

noncomputable section

namespace Eta
open Integration.MoonshineEta24CuspPinned
end Eta

namespace WeightZero
open Integration.MoonshineLevelOneWeightZeroPinned
end WeightZero

/-- Division by eta^24 is slash-invariant of weight zero. -/
theorem divByEta24_slash_eq
    (f : CuspForm 𝒮ℒ 12)
    (γ : SL(2, ℤ)) :
    (fun z : ℍ => f z / Eta.eta24CuspForm z) ∣[(0 : ℤ)] γ =
      (fun z : ℍ => f z / Eta.eta24CuspForm z) := by
  have hγ : ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  change (⇑f / ⇑Eta.eta24CuspForm) ∣[(12 : ℤ) - 12] γ =
    ⇑f / ⇑Eta.eta24CuspForm
  simp_rw [div_slash_SL2, SL_slash,
    slash_action_eqn _ _ hγ]
  norm_num

/-- Quotient of a weight-12 cusp form by eta^24 as a genuine weight-zero
level-one modular form. -/
def divByEta24
    (f : CuspForm 𝒮ℒ 12) :
    ModularForm 𝒮ℒ 0 where
  toFun z := f z / Eta.eta24CuspForm z
  slash_action_eq' := fun _ ⟨γ, hγ⟩ =>
    hγ ▸ divByEta24_slash_eq f γ
  holo' :=
    f.holo'.div
      Eta.eta24CuspForm.holo'
      (fun z =>
        pow_ne_zero 24
          (ModularForm.eta_ne_zero z.2))
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [divByEta24_slash_eq f γ,
      OnePoint.IsBoundedAtImInfty,
      Filter.BoundedAtFilter]
    exact
      (div_isBoundedUnder_of_isBigO
        (Eta.cusp_isBigO_eta24 f)).isBigO_one ℝ

@[simp]
theorem divByEta24_apply
    (f : CuspForm 𝒮ℒ 12)
    (z : ℍ) :
    divByEta24 f z =
      f z / Eta.eta24CuspForm z := rfl

/-- Every level-one weight-12 cusp form is a scalar multiple of eta^24. -/
theorem exists_smul_eta24
    (f : CuspForm 𝒮ℒ 12) :
    ∃ c : ℂ, c • Eta.eta24CuspForm = f := by
  obtain ⟨c, hc⟩ :=
    WeightZero.levelOne_weight_zero_const (divByEta24 f)
  refine ⟨c, ?_⟩
  ext z
  have hz := congrFun hc z
  change f z / Eta.eta24CuspForm z = c at hz
  have heta :
      Eta.eta24CuspForm z ≠ 0 := by
    exact pow_ne_zero 24 (ModularForm.eta_ne_zero z.2)
  apply (eq_div_iff heta).mp
  simpa [mul_comm] using hz.symm

/-- Pointwise form of the same scalar-multiple theorem. -/
theorem exists_pointwise_scalar_eta24
    (f : CuspForm 𝒮ℒ 12) :
    ∃ c : ℂ, ∀ z : ℍ,
      f z = c * Eta.eta24CuspForm z := by
  obtain ⟨c, hc⟩ := exists_smul_eta24 f
  refine ⟨c, fun z => ?_⟩
  have hz := congrArg (fun g : CuspForm 𝒮ℒ 12 => g z) hc
  simpa using hz.symm

structure Boundary where
  eta24NonvanishingUsed : Bool
  cuspDominationUsed : Bool
  quotientWeightZeroModularFormOwned : Bool
  pinnedWeightZeroConstancyUsed : Bool
  weight12ScalarMultipleTheoremOwned : Bool
  generalDimensionFormulaPorted : Bool
  dependencyBumpUsed : Bool

def boundary : Boundary where
  eta24NonvanishingUsed := true
  cuspDominationUsed := true
  quotientWeightZeroModularFormOwned := true
  pinnedWeightZeroConstancyUsed := true
  weight12ScalarMultipleTheoremOwned := true
  generalDimensionFormulaPorted := false
  dependencyBumpUsed := false

end

end Integration.MoonshineWeight12Eta24ScalarPinned
