import Integration.Paper9EulerMobiusTransport

/-!
Source-written, uncompiled. Use the actual normalized Delta and its
existing eta-product cusp unit to remove the logarithmic singularity.
No new E2 carrier or abstract derivative/cusp premises in the terminal
intended theorem. All dependencies still require exact-head replay.
-/
namespace Integration.Paper9E2CorrectedClosure

open Function Complex Filter Asymptotics UpperHalfPlane ModularGroup
open ModularForm ModularFormClass SlashInvariantForm SlashInvariantFormClass
open scoped MatrixGroups Topology Real Manifold

noncomputable section

open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9BracketCuspClosure
open Integration.Paper9EulerMobiusTransport

local notation "Δf" => Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm
local notation "E₄" => Integration.MoonshineEisensteinAnalytic.E4
local notation "η₂₄" => Integration.MoonshineEta24Pinned.eta24

def deltaQ : ℂ → ℂ := cuspFunction 1 Δf

def deltaUnit (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n+1)) ^ 24

theorem deltaUnitZero : deltaUnit 0 = 1 := by simp [deltaUnit]

theorem deltaUnitAnalytic (q : ℂ) (hq : ‖q‖ < 1) :
    AnalyticAt ℂ deltaUnit q :=
  DifferentiableOn.analyticAt
    (Integration.MoonshineEtaProductPinned.differentiableOn_tprod_one_sub_pow_pow 24)
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_zero_iff.mpr hq))

theorem deltaUnitSourceOnDisk :
    Set.EqOn deltaQ (fun q => q * deltaUnit q) (Metric.ball 0 1) := by
  have hf : (Δf : ℍ → ℂ) = fun τ => η₂₄ τ := by
    funext τ
    rw [Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm_apply]
    exact Integration.MoonshineDeltaIdentityPinned.normalizedDelta_eq_eta24 τ
  intro q hq
  unfold deltaQ
  rw [hf]
  exact Integration.MoonshineEta24CuspPinned.eta24_cuspFunction_eqOn hq

theorem deltaUnitSourceLocal (q : ℂ) (hq : ‖q‖ < 1) :
    deltaQ =ᶠ[𝓝 q] (fun z => z * deltaUnit z) := by
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_zero_iff.mpr hq)]
    with z hz
  exact deltaUnitSourceOnDisk hz

theorem deltaUnitNonzero (q : ℂ) (hq : ‖q‖ < 1) :
    deltaUnit q ≠ 0 := by
  rcases eq_or_ne q 0 with rfl | hn
  · simp [deltaUnitZero]
  · let τ : ℍ := ⟨Periodic.invQParam 1 q,
      Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq hn⟩
    have hr : Periodic.qParam 1 τ = q := Periodic.qParam_right_inv one_ne_zero hn
    have hv : deltaQ q = Δf τ := by
      rw [← hr]
      exact eq_cuspFunction Δf τ one_mem_strictPeriods_SL one_ne_zero
    have hs := deltaUnitSourceOnDisk (Metric.mem_ball_zero_iff.mpr hq)
    rw [hv] at hs
    intro hz
    rw [hz, mul_zero] at hs
    exact Integration.MoonshineDeltaFinalMinCut.normalizedDelta_ne_zero_canonical τ
      ((Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm_apply τ).symm.trans hs)

theorem deltaQDeriv (q : ℂ) (hq : ‖q‖ < 1) :
    deriv deltaQ q = deltaUnit q + q * deriv deltaUnit q := by
  rw [(deltaUnitSourceLocal q hq).deriv_eq]
  have h := (hasDerivAt_id q).mul (deltaUnitAnalytic q hq).differentiableAt.hasDerivAt
  simpa [add_comm, mul_comm] using h.deriv

-- A regular analytic representative of the SAME logarithmic derivative,
-- including its zero mode. Its equality with e2 is proved below.
def e2Q (q : ℂ) : ℂ := 1 + q * deriv deltaUnit q / deltaUnit q

theorem e2QZero : e2Q 0 = 1 := by simp [e2Q]

theorem e2QAnalytic (q : ℂ) (hq : ‖q‖ < 1) : AnalyticAt ℂ e2Q q := by
  have hu := deltaUnitAnalytic q hq
  unfold e2Q
  exact analyticAt_const.add
    ((analyticAt_id.mul hu.deriv).div hu (deltaUnitNonzero q hq))

theorem e2QAt (τ : ℍ) : e2Q (qExt τ) = e2 τ := by
  let q := qExt τ
  have hq : ‖q‖ < 1 := qNorm τ
  have hn : q ≠ 0 := Periodic.qParam_ne_zero 1 τ
  have hu := deltaUnitNonzero q hq
  have hv : deltaQ q = Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaLimit τ :=
    (eq_cuspFunction Δf τ one_mem_strictPeriods_SL one_ne_zero).trans
      (Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm_apply τ)
  have hs := deltaUnitSourceOnDisk (Metric.mem_ball_zero_iff.mpr hq)
  change deltaQ q = q * deltaUnit q at hs
  change e2Q q = q * deriv deltaQ q /
    Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaLimit τ
  rw [← hv, hs, deltaQDeriv q hq]
  unfold e2Q
  field_simp [hn,hu] <;> ring

def de2 (τ : ℍ) : ℂ := euler e2Q (qExt τ)
def e2Ext (z : ℂ) : ℂ := e2Q (qExt z)

theorem e2ExtDeriv (τ : ℍ) :
    HasDerivAt e2Ext (scaleD * de2 τ) (τ : ℂ) := by
  have h := (e2QAnalytic _ (qNorm τ)).differentiableAt.hasDerivAt.comp
    (τ : ℂ) (qExtDeriv τ)
  simpa [e2Ext,de2,euler,Function.comp_def,mul_assoc,mul_comm,mul_left_comm] using h

theorem e2TransformLocal (γ : SL(2, ℤ)) (τ : ℍ) :
    (e2Ext ∘ mobius γ) =ᶠ[𝓝 (τ : ℂ)]
      (fun z => (linear γ z)^2 * e2Ext z +
        12*((γ 1 0 : ℂ)/scaleD)*linear γ z) := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  let v : ℍ := ⟨z,hz⟩
  change e2Ext (mobius γ (v : ℂ)) =
    (linear γ v)^2 * e2Ext v + 12*((γ 1 0 : ℂ)/scaleD)*linear γ v
  rw [mobiusAt]
  simp only [e2Ext, e2QAt]
  exact originalE2Transform γ v

theorem de2Transform (γ : SL(2, ℤ)) (τ : ℍ) :
    de2 (γ • τ) = (linear γ τ)^4 * de2 τ +
      2*((γ 1 0 : ℂ)/scaleD)*(linear γ τ)^3*e2 τ +
      12*((γ 1 0 : ℂ)/scaleD)^2*(linear γ τ)^2 := by
  let j := linear γ τ
  let c := (γ 1 0 : ℂ)
  have hj := linear_ne_zero γ τ
  have hf : HasDerivAt e2Ext (scaleD*de2 (γ • τ)) (mobius γ τ) := by
    rw [mobiusAt]
    exact e2ExtDeriv (γ • τ)
  have hl := hf.comp (τ : ℂ) (mobiusDeriv γ τ)
  have hr := (((linearDeriv γ τ).pow 2).mul (e2ExtDeriv τ)).add
    ((linearDeriv γ τ).const_mul (12*(c/scaleD)))
  have he := (hl.congr_of_eventuallyEq (e2TransformLocal γ τ).symm).unique hr
  have he' : scaleD*de2 (γ • τ)/j^2 =
      2*j*c*e2 τ+j^2*(scaleD*de2 τ)+12*(c/scaleD)*c := by
    simpa [j,c,e2Ext,e2QAt,div_eq_mul_inv,mul_comm,mul_assoc,mul_left_comm]
      using he
  calc
    de2 (γ • τ) = (j^2/scaleD)*(scaleD*de2 (γ • τ)/j^2) := by
      field_simp [hj,scaleD_ne_zero] <;> ring
    _ = _ := by rw [he']; field_simp [scaleD_ne_zero] <;> ring

def correctedQ (q : ℂ) : ℂ := 12 * euler e2Q q - e2Q q^2 + x q
def correctedAt (τ : ℍ) : ℂ := correctedQ (qExt τ)

theorem correctedZero : correctedQ 0 = 0 := by
  simp [correctedQ,euler,e2QZero,xZero]

theorem correctedAnalytic (q : ℂ) (hq : ‖q‖ < 1) :
    AnalyticAt ℂ correctedQ q := by
  have he := e2QAnalytic q hq
  unfold correctedQ euler
  exact ((analyticAt_const.mul (analyticAt_id.mul he.deriv)).sub (he.pow 2)).add
    (xAnalyticDisk q hq)

theorem correctedSource (τ : ℍ) :
    correctedAt τ = 12*de2 τ - e2 τ^2 + E₄ τ := by
  simp [correctedAt,correctedQ,de2,e2QAt,qExt,xAtQ]

theorem correctedSlash (γ : SL(2, ℤ)) :
    correctedAt ∣[(4 : ℤ)] γ = correctedAt := by
  funext τ
  apply (slash_action_eq'_iff 4 correctedAt γ τ).2
  simp only [correctedSource]
  rw [de2Transform,originalE2Transform,formTransform 3 E₄ γ τ]
  simpa [linear,zpow_ofNat] using e2CorrectedCovarianceAlgebra
    (e2 τ) (de2 τ) (E₄ τ) (linear γ τ) ((γ 1 0 : ℂ)/scaleD)

theorem correctedHolo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) correctedAt := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  let τ : ℍ := ⟨z,hz⟩
  have hc := (correctedAnalytic _ (qNorm τ)).differentiableAt.comp z
    (qExtDeriv z).differentiableAt
  apply (hc.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simp [Function.comp_def,correctedAt,ofComplex_apply_of_im_pos hw]

theorem correctedCuspZero : IsZeroAtImInfty correctedAt := by
  have h := (correctedAnalytic 0 (by simp)).continuousAt.tendsto.comp
    (UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) one_pos)
  rw [correctedZero] at h
  exact h

def correctedCusp : CuspForm 𝒮ℒ 4 where
  toFun := correctedAt
  slash_action_eq' A hA := by
    obtain ⟨γ,rfl⟩ := hA
    exact correctedSlash γ
  holo' := correctedHolo
  zero_at_cusps' {c} hc γ hγ := by
    rw [correctedSlash γ]
    exact correctedCuspZero

-- Same existing cusp domination owner as the weight-12 proof, but
-- at weight 4. No assumption of a general dimension theorem.
local notation "ηC" => Integration.MoonshineEta24CuspPinned.eta24CuspForm

theorem correctedQuotientSlash (γ : SL(2, ℤ)) :
    (fun τ : ℍ => correctedCusp τ / ηC τ) ∣[(-8 : ℤ)] γ =
      (fun τ : ℍ => correctedCusp τ / ηC τ) := by
  have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ,rfl⟩
  change (⇑correctedCusp / ⇑ηC) ∣[(4 : ℤ)-12] γ = ⇑correctedCusp / ⇑ηC
  simp_rw [div_slash_SL2,SL_slash,slash_action_eqn _ _ hγ]
  norm_num

def correctedQuotient : ModularForm 𝒮ℒ (-8) where
  toFun τ := correctedCusp τ / ηC τ
  slash_action_eq' := fun _ ⟨γ,hγ⟩ => hγ ▸ correctedQuotientSlash γ
  holo' := correctedCusp.holo'.div ηC.holo'
    (fun τ => pow_ne_zero 24 (ModularForm.eta_ne_zero τ.2))
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [correctedQuotientSlash γ,OnePoint.IsBoundedAtImInfty,Filter.BoundedAtFilter]
    exact (div_isBoundedUnder_of_isBigO
      (Integration.MoonshineEta24CuspPinned.cusp_isBigO_eta24 correctedCusp)).isBigO_one ℝ

theorem correctedQuotientZero (τ : ℍ) : correctedQuotient τ = 0 := by
  have hc := Integration.MoonshineLevelOneWeightZeroPinned.levelOne_nonpos_wt_const
    (by norm_num : (-8 : ℤ) ≤ 0) correctedQuotient
  let v : ℍ := ⟨2 * Complex.I, by simp⟩
  have hS := congrFun (correctedQuotientSlash ModularGroup.S) v
  change ((correctedQuotient : ℍ → ℂ) ∣[(-8 : ℤ)] ModularGroup.S) v =
    correctedQuotient v at hS
  have ht := (slash_action_eq'_iff (-8) correctedQuotient ModularGroup.S v).1 hS
  have he : correctedQuotient (ModularGroup.S • v) = correctedQuotient v :=
    (congrFun hc _).trans (congrFun hc _).symm
  rw [he] at ht
  have hn := congrArg norm ht
  have hj : ‖(ModularGroup.S 1 0 : ℂ)*(v : ℂ)+(ModularGroup.S 1 1 : ℂ)‖ = 2 := by
    simp [ModularGroup.S,v,norm_mul]
  rw [norm_mul,norm_zpow,hj] at hn
  norm_num at hn
  have hz : correctedQuotient v = 0 := norm_eq_zero.mp (by linarith)
  exact ((congrFun hc τ).trans (congrFun hc v).symm).trans hz

theorem originalRamanujan2 (τ : ℍ) :
    12 * de2 τ = e2 τ^2 - E₄ τ := by
  have h := correctedQuotientZero τ
  change correctedAt τ / ηC τ = 0 at h
  have hn : ηC τ ≠ 0 := pow_ne_zero 24 (ModularForm.eta_ne_zero τ.2)
  have hz := (div_eq_zero_iff.mp h).resolve_right hn
  rw [correctedSource] at hz
  linear_combination hz

theorem originalRamanujanSystem (τ : ℍ) :
    12 * de2 τ = e2 τ^2 - E₄ τ ∧
    3 * dx τ = e2 τ * E₄ τ - Integration.MoonshineEisensteinAnalytic.E6 τ ∧
    2 * dy τ = e2 τ * Integration.MoonshineEisensteinAnalytic.E6 τ - E₄ τ^2 :=
  ⟨originalRamanujan2 τ,originalRamanujan46 τ⟩

end
end Integration.Paper9E2CorrectedClosure
