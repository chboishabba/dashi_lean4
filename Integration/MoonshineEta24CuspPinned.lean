import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Cusps
import Integration.MoonshineEta24Pinned
import Integration.MoonshineLevelOneWeightZeroPinned

/-!
# eta^24 as a level-one cusp form at the pinned Mathlib v4.28.0 dependency

The later Mathlib Discriminant module packages eta^24 as the level-one
weight-12 discriminant, but that module does not exist at this repository's
v4.28.0 pin.

This file reconstructs only the needed cusp-form surface using APIs already
present at the pin and the S/T laws proved in MoonshineEta24Pinned.

The key q-product identity is

  eta(z)^24 = q(z) * (prod_n (1 - q(z)^(n+1)))^24.

The Euler product is shown to tend to 1 as q -> 0 by the pin-native uniform
infinite-product API on the closed radius-1/2 disc.  Consequently eta^24 tends
to zero at i-infinity and has first-order q asymptotic coefficient 1.
-/

namespace Integration.MoonshineEta24CuspPinned

open Function Complex Filter Set Metric SlashInvariantForm UpperHalfPlane
  ModularGroup ModularForm

open scoped MatrixGroups Real Topology BigOperators

noncomputable section

local notation "η24" => Integration.MoonshineEta24Pinned.eta24
local notation "𝕢" => Periodic.qParam

/-- Pin-local generator theorem for SL2Z. -/
theorem slash_action_generators_SL2Z
    {f : ℍ → ℂ} {k : ℤ}
    (hS : f ∣[k] ModularGroup.S = f)
    (hT : f ∣[k] ModularGroup.T = f) :
    ∀ γ : SL(2, ℤ), f ∣[k] γ = f := by
  intro γ
  have hSL :
      𝒮ℒ =
        Subgroup.closure
          ({((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ),
            ((ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ)} :
            Set (GL (Fin 2) ℝ)) := by
    rw [MonoidHom.range_eq_map,
      ← SpecialLinearGroup.SL2Z_generators,
      MonoidHom.map_closure,
      Set.image_pair]
    rfl
  exact
    (SlashInvariantForm.slash_action_generators hSL).mpr
      (fun g hg => by
        rcases hg with rfl | rfl
        · exact hS
        · exact hT)
      _
      (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)

/-- Pointwise slash S invariance of eta^24. -/
theorem eta24_slash_S :
    ((fun z : ℍ => η24 z) ∣[(12 : ℤ)] ModularGroup.S) =
      fun z : ℍ => η24 z := by
  funext z
  rw [SlashInvariantForm.SL_slash_apply]
  have h :=
    Integration.MoonshineEta24Pinned.eta24_S_pointwise z
  simp only [ModularGroup.denom_S] at *
  field_simp [z.ne_zero] at *
  simpa [UpperHalfPlane.modular_S_smul] using h

/-- Pointwise slash T invariance of eta^24. -/
theorem eta24_slash_T :
    ((fun z : ℍ => η24 z) ∣[(12 : ℤ)] ModularGroup.T) =
      fun z : ℍ => η24 z := by
  funext z
  rw [SlashInvariantForm.SL_slash_apply]
  have h :=
    Integration.MoonshineEta24Pinned.eta24_T_pointwise z
  simpa [ModularGroup.denom_T] using h

/-- eta^24 is invariant under every element of SL2Z. -/
theorem eta24_slash_all
    (γ : SL(2, ℤ)) :
    ((fun z : ℍ => η24 z) ∣[(12 : ℤ)] γ) =
      fun z : ℍ => η24 z :=
  slash_action_generators_SL2Z eta24_slash_S eta24_slash_T γ

/-- Euler product as a function of the q parameter. -/
def etaEulerProduct (q : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - q ^ (n + 1))

private theorem etaEulerProduct_uniform_on_halfDisc :
    HasProdUniformlyOn
      (fun n (q : ℂ) => 1 - q ^ (n + 1))
      etaEulerProduct
      (Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)) := by
  have hsum :
      Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
    simpa only [pow_succ'] using
      (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left (1 / 2)
  apply Summable.hasProdUniformlyOn_nat_one_add
    Metric.isCompact_closedBall
    hsum
  · filter_upwards with n q hq
    have hnorm : ‖q‖ ≤ (1 / 2 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hq
    simpa [norm_neg, norm_pow] using
      pow_le_pow_left₀ (norm_nonneg q) hnorm (n + 1)
  · intro n
    fun_prop

/-- The Euler product is continuous at q=0 within the half-disc. -/
theorem etaEulerProduct_continuousWithinAt_zero :
    ContinuousWithinAt
      etaEulerProduct
      (Metric.closedBall (0 : ℂ) (1 / 2 : ℝ))
      0 := by
  have hprod := etaEulerProduct_uniform_on_halfDisc
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at hprod
  have hcont :
      ContinuousOn etaEulerProduct
        (Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)) :=
    hprod.continuousOn
      (Frequently.of_forall fun s => by
        exact continuousOn_finsetProd _ fun i _ => by fun_prop)
  exact hcont 0 (by simp)

/-- The Euler product equals 1 at q=0. -/
@[simp]
theorem etaEulerProduct_zero :
    etaEulerProduct 0 = 1 := by
  unfold etaEulerProduct
  simp

/-- Therefore the Euler product tends to 1 as q tends to 0 through the
closed half-disc. -/
theorem etaEulerProduct_tendsto_one :
    Tendsto etaEulerProduct
      (𝓝[Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)] 0)
      (𝓝 1) := by
  simpa [etaEulerProduct_zero] using
    etaEulerProduct_continuousWithinAt_zero

/-- On the upper half-plane the eta Euler product is the q-parameter product. -/
theorem eta_tprod_eq_eulerProduct (z : ℍ) :
    (∏' n : ℕ, (1 - ModularForm.eta_q n z)) =
      etaEulerProduct (𝕢 1 z) := by
  apply tprod_congr
  intro n
  simp [etaEulerProduct, ModularForm.eta_q]

/-- Exact q-product formula for eta^24, using no square-root eta
transformation theorem. -/
theorem eta24_eq_q_mul_eulerProduct_pow (z : ℍ) :
    η24 z =
      𝕢 1 z * (etaEulerProduct (𝕢 1 z)) ^ 24 := by
  unfold Integration.MoonshineEta24Pinned.eta24 ModularForm.eta
  rw [mul_pow, eta_tprod_eq_eulerProduct]
  congr 1
  unfold Periodic.qParam
  rw [← Complex.exp_nsmul]
  congr 1
  ring

/-- Eventually the level-one q parameter lies in the closed half-disc. -/
private theorem eventually_qParam_mem_halfDisc :
    ∀ᶠ z : ℍ in atImInfty,
      𝕢 1 z ∈ Metric.closedBall (0 : ℂ) (1 / 2 : ℝ) := by
  have hq := UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) zero_lt_one
  exact
    hq.eventually
      (Metric.closedBall_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 2))

/-- The Euler product tends to 1 at i-infinity. -/
theorem etaEulerProduct_tendsto_atImInfty :
    Tendsto
      (fun z : ℍ => etaEulerProduct (𝕢 1 z))
      atImInfty
      (𝓝 1) := by
  apply etaEulerProduct_tendsto_one.comp
  exact
    Tendsto.inf
      (UpperHalfPlane.qParam_tendsto_atImInfty
        (h := 1) zero_lt_one)
      (tendsto_principal.2 eventually_qParam_mem_halfDisc)

/-- eta^24 vanishes at i-infinity. -/
theorem eta24_isZeroAtImInfty :
    IsZeroAtImInfty (fun z : ℍ => η24 z) := by
  apply Tendsto.congr
    (fun z => (eta24_eq_q_mul_eulerProduct_pow z).symm)
  rw [show (0 : ℂ) = 0 * 1 by ring]
  exact
    (UpperHalfPlane.qParam_tendsto_atImInfty
      (h := 1) zero_lt_one).mul
      (etaEulerProduct_tendsto_atImInfty.pow 24)

/-- Holomorphy of eta^24 on the upper half-plane. -/
theorem eta24_mdifferentiable :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : ℍ => η24 z) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  exact
    ((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow 24)
      |>.differentiableWithinAt

/-- eta^24 packaged as a genuine level-one cusp form of weight 12. -/
def eta24CuspForm : CuspForm 𝒮ℒ 12 where
  toFun := fun z => η24 z
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact eta24_slash_all γ
  holo' := eta24_mdifferentiable
  zero_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [eta24_slash_all γ]
    exact eta24_isZeroAtImInfty

@[simp]
theorem eta24CuspForm_apply (z : ℍ) :
    eta24CuspForm z = η24 z := rfl

/-- eta^24 is big enough at the cusp to dominate the standard exponential
decay scale. -/
theorem exp_isBigO_eta24 :
    (fun z : ℍ => Real.exp (-2 * Real.pi * z.im))
      =O[atImInfty]
    (fun z : ℍ => η24 z) := by
  refine .of_bound 2 ?_
  have hprod :=
    etaEulerProduct_tendsto_atImInfty.eventually
      (Metric.ball_mem_nhds 1
        (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hprod] with z hz
  rw [eta24_eq_q_mul_eulerProduct_pow, norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  have hq :
      ‖𝕢 1 z‖ =
        Real.exp (-2 * Real.pi * z.im) := by
    simp [Periodic.qParam, Complex.norm_exp]
  rw [← hq]
  have hp : 1 / 2 ≤ ‖etaEulerProduct (𝕢 1 z)‖ := by
    have hsub :
        ‖etaEulerProduct (𝕢 1 z) - 1‖ < 1 / 2 := by
      rwa [Complex.dist_eq] at hz
    have h1 :=
      norm_sub_norm_le 1 (etaEulerProduct (𝕢 1 z))
    grind [norm_one, norm_sub_rev]
  have hp24 : 1 / 2 ≤ ‖etaEulerProduct (𝕢 1 z) ^ 24‖ := by
    rw [norm_pow]
    have : (1 / 2 : ℝ) ^ 24 ≤ ‖etaEulerProduct (𝕢 1 z)‖ ^ 24 :=
      pow_le_pow_left₀ (by positivity) hp 24
    norm_num at this ⊢
    exact le_trans (by norm_num) this
  linarith [norm_nonneg (𝕢 1 z),
    mul_le_mul_of_nonneg_left hp24 (norm_nonneg (𝕢 1 z))]

/-- Any level-one cusp form is O(eta^24) at i-infinity. -/
theorem cusp_isBigO_eta24 {k : ℤ}
    (f : CuspForm 𝒮ℒ k) :
    f =O[atImInfty] (fun z : ℍ => η24 z) :=
  (CuspFormClass.exp_decay_atImInfty
      (h := 1) f
      CuspFormClass.zero_at_infty
      one_pos
      (by simp))
    |>.trans
      (by simpa using exp_isBigO_eta24)

structure Eta24CuspPinnedBoundary where
  qProductFormulaOwned : Bool
  eulerProductContinuityAtZeroOwned : Bool
  eta24ZeroAtImInftyOwned : Bool
  eta24CuspFormOwned : Bool
  eta24CuspDominationOwned : Bool
  dependencyBumpUsed : Bool

def eta24CuspPinnedBoundary : Eta24CuspPinnedBoundary where
  qProductFormulaOwned := true
  eulerProductContinuityAtZeroOwned := true
  eta24ZeroAtImInftyOwned := true
  eta24CuspFormOwned := true
  eta24CuspDominationOwned := true
  dependencyBumpUsed := false

end

end Integration.MoonshineEta24CuspPinned
