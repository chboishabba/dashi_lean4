import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.NumberTheory.ModularForms.SlashActions
import Integration.MoonshineEta24CuspPinned
import Integration.MoonshineLevelOneWeightZeroPinned

/-!
# Weight-12 level-one cusp forms are scalar multiples of eta^24 at Mathlib v4.28.0

The later Mathlib dimension-formula stack proves this via its packaged
discriminant equivalence.  That stack is not available at this repository's
pin, so this module reconstructs only the weight-12 specialization needed by
the Moonshine Delta same-object seam.

For a weight-12 cusp form f, divide by eta^24.  Nonvanishing of eta, equal
weights, and the cusp-growth comparison show that f / eta^24 is a bounded
holomorphic level-one modular form of weight zero.  The pin-local weight-zero
constancy theorem then makes it constant.
-/

namespace Integration.MoonshineWeight12CuspPinned

open Function Complex Filter UpperHalfPlane ModularGroup ModularForm
  SlashInvariantForm Asymptotics

open scoped MatrixGroups Topology

noncomputable section

local notation "η24" => Integration.MoonshineEta24Pinned.eta24
local notation "Δη" => Integration.MoonshineEta24CuspPinned.eta24CuspForm

/-- eta^24 has no zero on the upper half-plane. -/
theorem eta24_ne_zero (z : ℍ) :
    η24 z ≠ 0 :=
  pow_ne_zero 24 (ModularForm.eta_ne_zero z.2)

/-- Division by eta^24 cancels weight 12 exactly. -/
theorem divByEta24_slash_eq
    (f : CuspForm 𝒮ℒ 12)
    (γ : SL(2, ℤ)) :
    (fun z : ℍ => f z / η24 z) ∣[(0 : ℤ)] γ =
      fun z : ℍ => f z / η24 z := by
  have hγ : ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ 𝒮ℒ :=
    ⟨γ, rfl⟩
  change
    (⇑f / ⇑Δη) ∣[(12 : ℤ) - 12] γ =
      ⇑f / ⇑Δη
  simp_rw [div_slash_SL2, SL_slash,
    slash_action_eqn _ _ hγ]

/-- Divide a weight-12 cusp form by eta^24 to obtain a weight-zero modular
form at the pinned dependency. -/
def divByEta24
    (f : CuspForm 𝒮ℒ 12) :
    ModularForm 𝒮ℒ 0 where
  toFun z := f z / η24 z

  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact divByEta24_slash_eq f γ

  holo' :=
    f.holo'.div
      Integration.MoonshineEta24CuspPinned.eta24_mdifferentiable
      eta24_ne_zero

  bdd_at_cusps' hc γ hγ := by
    rw [divByEta24_slash_eq f γ,
      IsBoundedAtImInfty,
      Filter.BoundedAtFilter]
    exact
      (div_isBoundedUnder_of_isBigO
        (Integration.MoonshineEta24CuspPinned.cusp_isBigO_eta24 f))
      |>.isBigO_one ℝ

@[simp]
theorem divByEta24_apply
    (f : CuspForm 𝒮ℒ 12)
    (z : ℍ) :
    divByEta24 f z = f z / η24 z :=
  rfl

/-- Every level-one weight-12 cusp form is a scalar multiple of eta^24.

This is the sole dimension-one fact needed for the final Delta identity. -/
theorem exists_smul_eta24_of_weight12
    (f : CuspForm 𝒮ℒ 12) :
    ∃ c : ℂ, c • Δη = f := by
  obtain ⟨c, hc⟩ :=
    Integration.MoonshineLevelOneWeightZeroPinned.levelOne_weight_zero_const
      (divByEta24 f)
  refine ⟨c, ?_⟩
  apply CuspForm.ext
  intro z
  have hz := congrFun hc z
  change c * η24 z = f z
  change f z / η24 z = c at hz
  rw [← hz]
  exact (div_mul_cancel₀ (f z) (eta24_ne_zero z)).symm

/-- Functional version of the scalar-multiple theorem. -/
theorem exists_scalar_eta24_function_of_weight12
    (f : CuspForm 𝒮ℒ 12) :
    ∃ c : ℂ, ∀ z : ℍ, f z = c * η24 z := by
  obtain ⟨c, hc⟩ := exists_smul_eta24_of_weight12 f
  refine ⟨c, fun z => ?_⟩
  have := congrArg (fun g : CuspForm 𝒮ℒ 12 => g z) hc
  simpa using this.symm

structure Weight12CuspPinnedBoundary where
  eta24NonvanishingOwned : Bool
  divisionToWeightZeroOwned : Bool
  quotientHolomorphicOwned : Bool
  quotientBoundedAtCuspsOwned : Bool
  weightZeroConstancyReused : Bool
  weight12ScalarMultipleEta24Owned : Bool
  generalDimensionFormulaPorted : Bool
  dependencyBumpUsed : Bool

def weight12CuspPinnedBoundary : Weight12CuspPinnedBoundary where
  eta24NonvanishingOwned := true
  divisionToWeightZeroOwned := true
  quotientHolomorphicOwned := true
  quotientBoundedAtCuspsOwned := true
  weightZeroConstancyReused := true
  weight12ScalarMultipleEta24Owned := true
  generalDimensionFormulaPorted := false
  dependencyBumpUsed := false

end

end Integration.MoonshineWeight12CuspPinned
