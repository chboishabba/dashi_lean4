import Integration.MoonshineEisensteinAgdaTarget
import Integration.MoonshineEta24CuspPinned
import Integration.MoonshineWeight12Eta24ScalarPinned
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Final eta^24 = normalized E4/E6 Delta identity at Mathlib v4.28.0

This closes the last classical same-object seam without a Mathlib dependency
bump.

Proof shape:
1. compute the q-expansion of the existing normalized E4/E6 weight-12 modular
   form using the v4.28 q-expansion ring laws;
2. show its constant coefficient is zero and its first coefficient is one;
3. build the corresponding weight-12 cusp form directly using the pin-native
   cusp-function continuity argument;
4. use the local theorem that every level-one weight-12 cusp form is a scalar
   multiple of eta^24;
5. compare first q coefficients to force that scalar to one.

Thus, pointwise on the upper half-plane,

  eta(tau)^24 = (E4(tau)^3 - E6(tau)^2) / 1728.
-/

namespace Integration.MoonshineDeltaIdentityPinned

open Function Complex Filter
open UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass
open EisensteinSeries
open scoped MatrixGroups Topology Real

noncomputable section

namespace Target
open Integration.MoonshineEisensteinAgdaTarget
end Target

namespace Analytic
open Integration.MoonshineEisensteinAnalytic
end Analytic

namespace Eta
open Integration.MoonshineEta24CuspPinned
end Eta

namespace Scalar
open Integration.MoonshineWeight12Eta24ScalarPinned
end Scalar

------------------------------------------------------------------------
-- q-expansion algebra for the packaged normalized E4/E6 target.
------------------------------------------------------------------------

theorem qExpansion_e4CubeWeight12 :
    qExpansion 1 Target.e4CubeWeight12 =
      qExpansion 1 Analytic.E4 *
        qExpansion 1 Analytic.E4 *
          qExpansion 1 Analytic.E4 := by
  unfold Target.e4CubeWeight12
  change
    qExpansion 1
        ((((Analytic.E4.mul Analytic.E4).mul Analytic.E4 :
          ModularForm 𝒮ℒ 12) : ℍ → ℂ)) =
      _
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL]
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL]

theorem qExpansion_e6SquareWeight12 :
    qExpansion 1 Target.e6SquareWeight12 =
      qExpansion 1 Analytic.E6 *
        qExpansion 1 Analytic.E6 := by
  unfold Target.e6SquareWeight12
  change
    qExpansion 1
        (((Analytic.E6.mul Analytic.E6 :
          ModularForm 𝒮ℒ 12) : ℍ → ℂ)) =
      _
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL]

theorem normalizedDeltaForm_qExpansion_eq :
    qExpansion 1 Target.normalizedDeltaForm =
      ((1728 : ℂ)⁻¹) •
        (qExpansion 1 Analytic.E4 *
            qExpansion 1 Analytic.E4 *
              qExpansion 1 Analytic.E4 -
          qExpansion 1 Analytic.E6 *
            qExpansion 1 Analytic.E6) := by
  unfold Target.normalizedDeltaForm
  rw [ModularForm.qExpansion_smul
      one_pos one_mem_strictPeriods_SL]
  rw [ModularForm.qExpansion_sub
      one_pos one_mem_strictPeriods_SL]
  rw [qExpansion_e4CubeWeight12, qExpansion_e6SquareWeight12]

private theorem E4_qExpansion_coeff_zero :
    (qExpansion 1 Analytic.E4).coeff 0 = 1 := by
  simpa [Analytic.E4] using
    (EisensteinSeries.E_qExpansion_coeff_zero
      (k := 4)
      (by norm_num : 3 ≤ 4)
      (by norm_num : Even 4))

private theorem E6_qExpansion_coeff_zero :
    (qExpansion 1 Analytic.E6).coeff 0 = 1 := by
  simpa [Analytic.E6] using
    (EisensteinSeries.E_qExpansion_coeff_zero
      (k := 6)
      (by norm_num : 3 ≤ 6)
      (by norm_num : Even 6))

private theorem E4_qExpansion_coeff_one :
    (qExpansion 1 Analytic.E4).coeff 1 = 240 := by
  rw [EisensteinSeries.E_qExpansion_coeff
    (k := 4)
    (by norm_num : 3 ≤ 4)
    (by norm_num : Even 4)
    (m := 1)]
  norm_num [show bernoulli 4 = -1 / 30 by decide +kernel]

private theorem E6_qExpansion_coeff_one :
    (qExpansion 1 Analytic.E6).coeff 1 = -504 := by
  rw [EisensteinSeries.E_qExpansion_coeff
    (k := 6)
    (by norm_num : 3 ≤ 6)
    (by norm_num : Even 6)
    (m := 1)]
  norm_num [show bernoulli 6 = 1 / 42 by decide +kernel]

theorem normalizedDeltaForm_qExpansion_coeff_zero :
    (qExpansion 1 Target.normalizedDeltaForm).coeff 0 = 0 := by
  rw [normalizedDeltaForm_qExpansion_eq]
  simp [PowerSeries.coeff_smul, PowerSeries.coeff_mul,
    E4_qExpansion_coeff_zero, E6_qExpansion_coeff_zero]

theorem normalizedDeltaForm_qExpansion_coeff_one :
    (qExpansion 1 Target.normalizedDeltaForm).coeff 1 = 1 := by
  rw [normalizedDeltaForm_qExpansion_eq]
  norm_num [PowerSeries.coeff_smul, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_succ,
    E4_qExpansion_coeff_zero, E6_qExpansion_coeff_zero,
    E4_qExpansion_coeff_one, E6_qExpansion_coeff_one]

------------------------------------------------------------------------
-- Pin-native conversion of a zero-constant modular form into a cusp form.
------------------------------------------------------------------------

theorem isZeroAtImInfty_of_coeffZero
    {k : ℤ}
    (f : ModularForm 𝒮ℒ k)
    (h0 : (qExpansion 1 f).coeff 0 = 0) :
    IsZeroAtImInfty f := by
  have hval : valueAtInfty f = 0 := by
    rw [← qExpansion_coeff_zero f one_pos one_mem_strictPeriods_SL]
    exact h0
  have hanal :=
    ModularFormClass.analyticAt_cuspFunction_zero
      f one_pos one_mem_strictPeriods_SL
  have hper :=
    SlashInvariantFormClass.periodic_comp_ofComplex
      f one_mem_strictPeriods_SL
  have ht :=
    hanal.continuousAt.tendsto.comp
      (UpperHalfPlane.qParam_tendsto_atImInfty
        (h := 1) one_pos)
  rw [cuspFunction_apply_zero f one_pos one_mem_strictPeriods_SL,
      hval] at ht
  rw [IsZeroAtImInfty, Filter.ZeroAtFilter]
  exact ht.congr
    (fun τ =>
      SlashInvariantFormClass.eq_cuspFunction
        f τ one_mem_strictPeriods_SL one_ne_zero)

theorem normalizedDeltaForm_isZeroAtImInfty :
    IsZeroAtImInfty Target.normalizedDeltaForm :=
  isZeroAtImInfty_of_coeffZero
    Target.normalizedDeltaForm
    normalizedDeltaForm_qExpansion_coeff_zero

def normalizedDeltaCuspForm :
    CuspForm 𝒮ℒ 12 where
  toFun := Target.normalizedDeltaForm
  slash_action_eq' :=
    Target.normalizedDeltaForm.slash_action_eq'
  holo' :=
    Target.normalizedDeltaForm.holo'
  zero_at_cusps' {c} hc γ hγ := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro δ _
    rw [show
      ((Target.normalizedDeltaForm : ℍ → ℂ) ∣[(12 : ℤ)] δ) =
        (Target.normalizedDeltaForm : ℍ → ℂ) from
      Target.normalizedDeltaForm.slash_action_eq' _ ⟨δ, rfl⟩]
    exact normalizedDeltaForm_isZeroAtImInfty

@[simp]
theorem normalizedDeltaCuspForm_apply (z : ℍ) :
    normalizedDeltaCuspForm z =
      Target.normalizedDeltaLimit z := by
  exact Target.normalizedDeltaForm_apply z

theorem normalizedDeltaCuspForm_qExpansion_coeff_one :
    (qExpansion 1 normalizedDeltaCuspForm).coeff 1 = 1 :=
  normalizedDeltaForm_qExpansion_coeff_one

------------------------------------------------------------------------
-- Compare the unique weight-12 cusp-form scalar.
------------------------------------------------------------------------

theorem normalizedDelta_scalar_eq_one :
    ∀ c : ℂ,
      c • Eta.eta24CuspForm = normalizedDeltaCuspForm →
      c = 1 := by
  intro c hc
  have hc_fun :
      (c • Eta.eta24CuspForm : ℍ → ℂ) =
        (normalizedDeltaCuspForm : ℍ → ℂ) :=
    congrArg DFunLike.coe hc
  have hq :=
    ModularForm.qExpansion_smul
      one_pos one_mem_strictPeriods_SL
      c Eta.eta24CuspForm
  rw [hc_fun] at hq
  have hcoeff :=
    congrArg (fun p : PowerSeries ℂ => p.coeff 1) hq
  have heta :
      (qExpansion 1 Eta.eta24CuspForm).coeff 1 = 1 :=
    Eta.eta24_qExpansion_coeff_one
  have htarget :
      (qExpansion 1 normalizedDeltaCuspForm).coeff 1 = 1 :=
    normalizedDeltaCuspForm_qExpansion_coeff_one
  simpa [PowerSeries.coeff_smul, heta, htarget] using hcoeff.symm

/-- The final pinned same-object identity. -/
theorem eta24_eq_normalizedDelta
    (τ : ℍ) :
    Integration.MoonshineEta24Pinned.eta24 τ =
      Target.normalizedDeltaLimit τ := by
  obtain ⟨c, hc⟩ :=
    Scalar.exists_smul_eta24 normalizedDeltaCuspForm
  have hc1 := normalizedDelta_scalar_eq_one c hc
  subst c
  have hz :=
    congrArg
      (fun f : CuspForm 𝒮ℒ 12 => f τ)
      hc
  simpa [normalizedDeltaCuspForm_apply] using hz

/-- Symmetric orientation. -/
theorem normalizedDelta_eq_eta24
    (τ : ℍ) :
    Target.normalizedDeltaLimit τ =
      Integration.MoonshineEta24Pinned.eta24 τ :=
  (eta24_eq_normalizedDelta τ).symm

structure Boundary where
  normalizedDeltaQExpansionOwned : Bool
  normalizedDeltaConstantCoefficientZero : Bool
  normalizedDeltaFirstCoefficientOne : Bool
  normalizedDeltaCuspFormOwned : Bool
  eta24Weight12ScalarTheoremUsed : Bool
  scalarForcedToOneByFirstCoefficient : Bool
  eta24NormalizedDeltaSameObjectProved : Bool
  generalDimensionFormulaPorted : Bool
  dependencyBumpUsed : Bool

def boundary : Boundary where
  normalizedDeltaQExpansionOwned := true
  normalizedDeltaConstantCoefficientZero := true
  normalizedDeltaFirstCoefficientOne := true
  normalizedDeltaCuspFormOwned := true
  eta24Weight12ScalarTheoremUsed := true
  scalarForcedToOneByFirstCoefficient := true
  eta24NormalizedDeltaSameObjectProved := true
  generalDimensionFormulaPorted := false
  dependencyBumpUsed := false

end

end Integration.MoonshineDeltaIdentityPinned
