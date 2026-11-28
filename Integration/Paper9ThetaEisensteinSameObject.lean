import Integration.Paper9ThetaCuspNormalization
import Integration.Paper9E2CorrectedClosure
import Integration.MoonshineDeltaIdentityPinned

/-! SOURCE-WRITTEN, kernel pending. The signed theta observations are
identified with the ORIGINAL normalized Eisenstein forms by the existing
eta24 quotient / nonpositive-weight maximum-modulus route.
No general dimension formula or assumed Jacobi quartic identity.
Classical theta identities and modular-form uniqueness; DASHI attachment. -/
namespace Integration.Paper9ThetaEisensteinSameObject
open Complex Filter Function UpperHalfPlane ModularGroup ModularForm
open SlashInvariantForm SlashInvariantFormClass ModularFormClass
open scoped MatrixGroups Real Topology Manifold
open Integration.Paper9ThetaModularTransport
open Integration.Paper9ThetaCuspNormalization
noncomputable section

local notation "E₄" => Integration.MoonshineEisensteinAnalytic.E4
local notation "E₆" => Integration.MoonshineEisensteinAnalytic.E6
local notation "ηC" => Integration.MoonshineEta24CuspPinned.eta24CuspForm

-- Reuse the already implemented weight-four corrected cusp quotient,
-- generalized only in its weight. All boundedness is on the original cusp.
theorem quotientSlash {k : ℤ} (f : CuspForm 𝒮ℒ k) (γ : SL(2,ℤ)) :
    (fun τ : ℍ => f τ / ηC τ) ∣[(k-12)] γ =
      (fun τ : ℍ => f τ / ηC τ) := by
  have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ,rfl⟩
  change (⇑f / ⇑ηC) ∣[(k-12)] γ = ⇑f / ⇑ηC
  simp_rw [div_slash_SL2, SL_slash, slash_action_eqn _ _ hγ]

def quotient {k : ℤ} (f : CuspForm 𝒮ℒ k) : ModularForm 𝒮ℒ (k-12) where
  toFun τ := f τ / ηC τ
  slash_action_eq' := fun _ ⟨γ,hγ⟩ => hγ ▸ quotientSlash f γ
  holo' := f.holo'.div ηC.holo'
    (fun τ => pow_ne_zero 24 (ModularForm.eta_ne_zero τ.2))
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [quotientSlash f γ,OnePoint.IsBoundedAtImInfty,Filter.BoundedAtFilter]
    exact (div_isBoundedUnder_of_isBigO
      (Integration.MoonshineEta24CuspPinned.cusp_isBigO_eta24 f)).isBigO_one ℝ

theorem cuspZero {k : ℤ} (f : CuspForm 𝒮ℒ k)
    (hk : k-12 ≤ 0) (hn : (2:ℝ)^(k-12) ≠ 1) (τ : ℍ) : f τ = 0 := by
  have hc := Integration.MoonshineLevelOneWeightZeroPinned.levelOne_nonpos_wt_const
    hk (quotient f)
  let v : ℍ := ⟨2 * Complex.I, by simp⟩
  have hS := congrFun (quotientSlash f ModularGroup.S) v
  change ((quotient f : ℍ → ℂ) ∣[(k-12)] ModularGroup.S) v =
    quotient f v at hS
  have ht := (slash_action_eq'_iff (k-12) (quotient f) ModularGroup.S v).1 hS
  have he : quotient f (ModularGroup.S • v) = quotient f v :=
    (congrFun hc _).trans (congrFun hc _).symm
  rw [he] at ht
  have hnorm := congrArg norm ht
  have hj : ‖(ModularGroup.S 1 0 : ℂ)*(v : ℂ)+(ModularGroup.S 1 1 : ℂ)‖ = 2 := by
    simp [ModularGroup.S,v,norm_mul]
  rw [norm_mul,norm_zpow,hj] at hnorm
  have hz : quotient f v = 0 := by
    by_contra h
    have hp : ‖quotient f v‖ ≠ 0 := norm_ne_zero_iff.mpr h
    apply hn
    exact mul_right_cancel₀ hp (by simpa using hnorm.symm)
  have hτ : quotient f τ = 0 :=
    ((congrFun hc τ).trans (congrFun hc v).symm).trans hz
  change f τ / ηC τ = 0 at hτ
  have hη : ηC τ ≠ 0 := pow_ne_zero 24 (ModularForm.eta_ne_zero τ.2)
  exact (div_eq_zero_iff.mp hτ).resolve_right hη

-- Original modular form cusp value, via the original q-expansion API.
theorem normalizedLimit {k : ℤ} (f : ModularForm 𝒮ℒ k)
    (h0 : (qExpansion 1 f).coeff 0 = 1) :
    Tendsto (fun τ : ℍ => f τ) atImInfty (𝓝 1) := by
  have hval : valueAtInfty f = 1 := by
    rw [← qExpansion_coeff_zero f one_pos one_mem_strictPeriods_SL]
    exact h0
  have ht := (ModularFormClass.analyticAt_cuspFunction_zero f one_pos
    one_mem_strictPeriods_SL).continuousAt.tendsto.comp
      (UpperHalfPlane.qParam_tendsto_atImInfty (h:=1) one_pos)
  rw [cuspFunction_apply_zero f one_pos one_mem_strictPeriods_SL,hval] at ht
  exact ht.congr (fun τ => SlashInvariantFormClass.eq_cuspFunction
    f τ one_mem_strictPeriods_SL one_ne_zero)

theorem original4Limit : Tendsto (fun τ : ℍ => E₄ τ) atImInfty (𝓝 1) := by
  apply normalizedLimit
  exact EisensteinSeries.E_qExpansion_coeff_zero (k:=4)
    (by norm_num : 3 ≤ 4) (by norm_num : Even 4)

theorem original6Limit : Tendsto (fun τ : ℍ => E₆ τ) atImInfty (𝓝 1) := by
  apply normalizedLimit
  exact EisensteinSeries.E_qExpansion_coeff_zero (k:=6)
    (by norm_num : 3 ≤ 6) (by norm_num : Even 6)

theorem thetaHolo (f : ℂ → ℂ)
    (hf : ∀ τ : ℍ, DifferentiableAt ℂ f (τ:ℂ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => f τ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  apply ((hf ⟨z,hz⟩).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simp [Function.comp_def,ofComplex_apply_of_im_pos hw]

def difference4 (τ : ℍ) := at4 τ - E₄ τ
def difference6 (τ : ℍ) := at6 τ - E₆ τ

theorem difference4Slash (γ : SL(2,ℤ)) :
    difference4 ∣[(4:ℤ)] γ = difference4 := by
  funext τ
  apply (slash_action_eq'_iff 4 difference4 γ τ).2
  have ha := (slash_action_eq'_iff 4 at4 γ τ).1 (congrFun (slash4 γ) τ)
  have hg : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ,rfl⟩
  have hb := SlashInvariantForm.slash_action_eqn'' E₄ hg τ
  unfold difference4
  rw [ha,hb]
  ring

theorem difference6Slash (γ : SL(2,ℤ)) :
    difference6 ∣[(6:ℤ)] γ = difference6 := by
  funext τ
  apply (slash_action_eq'_iff 6 difference6 γ τ).2
  have ha := (slash_action_eq'_iff 6 at6 γ τ).1 (congrFun (slash6 γ) τ)
  have hg : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ,rfl⟩
  have hb := SlashInvariantForm.slash_action_eqn'' E₆ hg τ
  unfold difference6
  rw [ha,hb]
  ring

def cusp4 : CuspForm 𝒮ℒ 4 where
  toFun := difference4
  slash_action_eq' := fun _ ⟨γ,hγ⟩ => hγ ▸ difference4Slash γ
  holo' := (thetaHolo thetaE4 E4Differentiable).sub E₄.holo'
  zero_at_cusps' {c} hc γ hγ := by
    rw [difference4Slash γ]
    rw [IsZeroAtImInfty, Filter.ZeroAtFilter]
    simpa [difference4] using E4Limit.sub original4Limit

def cusp6 : CuspForm 𝒮ℒ 6 where
  toFun := difference6
  slash_action_eq' := fun _ ⟨γ,hγ⟩ => hγ ▸ difference6Slash γ
  holo' := (thetaHolo thetaE6 E6Differentiable).sub E₆.holo'
  zero_at_cusps' {c} hc γ hγ := by
    rw [difference6Slash γ]
    rw [IsZeroAtImInfty, Filter.ZeroAtFilter]
    simpa [difference6] using E6Limit.sub original6Limit

theorem thetaE4_eq_original (τ : ℍ) : thetaE4 τ = E₄ τ :=
  sub_eq_zero.mp (cuspZero cusp4 (by norm_num) (by norm_num) τ)

theorem thetaE6_eq_original (τ : ℍ) : thetaE6 τ = E₆ τ :=
  sub_eq_zero.mp (cuspZero cusp6 (by norm_num) (by norm_num) τ)

-- Exact original normalized discriminant numerator, not a new Δ.
theorem thetaDiscriminantNumerator (τ : ℍ) :
    thetaE4 τ^3-thetaE6 τ^2 = E₄ τ^3-E₆ τ^2 := by
  rw [thetaE4_eq_original,thetaE6_eq_original]

#print axioms thetaE4_eq_original
#print axioms thetaE6_eq_original
#print axioms thetaDiscriminantNumerator
end
end Integration.Paper9ThetaEisensteinSameObject
