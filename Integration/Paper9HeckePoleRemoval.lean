import Integration.Paper9DiscriminantUnitReflection
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! SOURCE-WRITTEN, UNCOMPILED.
Consume the existing classical Hecke chart and pinned rigidity owners.
The actual coefficient replay must supply a zero-cusp residual; this
module does not assume a modular polynomial identity as a premise.
-/
namespace Integration.Paper9HeckePoleRemoval

open Complex Function Filter UpperHalfPlane ModularGroup ModularForm
open scoped MatrixGroups Topology Manifold BigOperators
open Integration.Paper9ActualJSourceJet
open Integration.Paper9Hecke41ChartGeometry
open Integration.Paper9EulerMobiusTransport
open Integration.Paper9BracketCuspClosure

noncomputable section

-- Actual pinned Euclidean reduction theorem, not a new group proof.
theorem invarianceFromST (f : ℍ → ℂ)
    (hs : ∀ τ : ℍ, f (ModularGroup.S • τ)=f τ)
    (ht : ∀ τ : ℍ, f (ModularGroup.T • τ)=f τ) :
    ∀ (g : SL(2, ℤ)) (τ : ℍ), f (g • τ)=f τ := by
  let stabilizer : Subgroup (SL(2, ℤ)) :=
    { carrier := {g | ∀ τ : ℍ, f (g • τ)=f τ}
      one_mem' := by intro τ; simp
      mul_mem' := by
        intro g h hg hh τ
        rw [mul_smul,hg,hh]
      inv_mem' := by
        intro g hg τ
        have he := hg (g⁻¹ • τ)
        simpa [smul_smul] using he.symm }
  have hgen : ({ModularGroup.S, ModularGroup.T} : Set (SL(2, ℤ))) ⊆ stabilizer := by
    intro g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hs
    · exact ht
  have hclosure := Subgroup.closure_le.mpr hgen
  rw [SpecialLinearGroup.SL2Z_generators] at hclosure
  intro g
  exact hclosure (show g ∈ (⊤ : Subgroup (SL(2, ℤ))) from trivial)

theorem productInvariant (g : SL(2, ℤ)) (τ : ℍ) (Y : ℂ) :
    actualProduct (g • τ) Y=actualProduct τ Y :=
  invarianceFromST (fun v => actualProduct v Y)
    (fun v => productSInvariant v Y) (fun v => productTInvariant v Y) g τ

local notation "j" => Integration.MoonshineEisensteinAgdaTarget.jTarget

-- Actual local analytic j extension, no inverse j and no nonzero E4
-- hypothesis (j may vanish at elliptic points).
theorem jExtAnalytic (τ : ℍ) : AnalyticAt ℂ jExt (τ : ℂ) := by
  have hn : qExt τ ≠ 0 := Periodic.qParam_ne_zero 1 τ
  have hq : ‖qExt τ‖ < 1 := qNorm τ
  have he : AnalyticAt ℂ qExt (τ : ℂ) := by
    unfold qExt Periodic.qParam
    fun_prop
  exact (jQAnalytic (qExt τ) hq hn).comp he

def chartAffine (i : Chart) (z : ℂ) : ℂ :=
  if i.val=41 then 41*z else (z+(i.val : ℂ))/41

theorem chartAffineAt (i : Chart) (τ : ℍ) :
    chartAffine i τ = (chartPoint i τ : ℂ) := by
  by_cases hi : i.val=41 <;> simp [chartAffine,chartPoint,hi]

theorem chartAffineAnalytic (i : Chart) (z : ℂ) :
    AnalyticAt ℂ (chartAffine i) z := by
  unfold chartAffine
  split <;> fun_prop

theorem jHolo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) j := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  let τ : ℍ := ⟨z,hz⟩
  apply ((jExtAnalytic τ).differentiableAt.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simpa [ofComplex_apply_of_im_pos hw] using (jExtAt (⟨w,hw⟩ : ℍ)).symm

theorem chartHolo (i : Chart) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (chartValue i) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  let τ : ℍ := ⟨z,hz⟩
  have ha : AnalyticAt ℂ jExt (chartAffine i z) := by
    rw [show chartAffine i z=chartAffine i (τ : ℂ) from rfl,chartAffineAt]
    exact jExtAnalytic (chartPoint i τ)
  have hd := (ha.comp (chartAffineAnalytic i z)).differentiableAt
  apply (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  let v : ℍ := ⟨w,hw⟩
  change chartValue i (ofComplex w)=jExt (chartAffine i w)
  rw [ofComplex_apply_of_im_pos hw]
  change j (chartPoint i v)=jExt (chartAffine i (v : ℂ))
  rw [chartAffineAt,jExtAt]

theorem productHolo (F : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => actualProduct τ (F τ)) := by
  unfold actualProduct
  exact .prod (fun i _ => hf.sub (chartHolo i))

theorem polynomialHolo (P : Polynomial ℂ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => P.eval (j τ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  let τ : ℍ := ⟨z,hz⟩
  have hd := P.differentiableAt.comp z (jExtAnalytic τ).differentiableAt
  apply (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simp [Function.comp_def,ofComplex_apply_of_im_pos hw,
    jExtAt (⟨w,hw⟩ : ℍ)]

-- Reuse the existing pinned weight-zero constancy proof. The cusp
-- form constructor gives boundedness at every cusp automatically.
theorem invariantZero (f : ℍ → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hi : ∀ (g : SL(2, ℤ)) (τ : ℍ), f (g • τ)=f τ)
    (hz : IsZeroAtImInfty f) : ∀ τ, f τ=0 := by
  have hs (g : SL(2, ℤ)) : f ∣[(0 : ℤ)] g=f := by
    funext τ
    apply (slash_action_eq'_iff 0 f g τ).2
    simpa using hi g τ
  let r : CuspForm 𝒮ℒ 0 :=
    { toFun := f
      slash_action_eq' := fun _ ⟨g,hg⟩ => hg ▸ (by simpa [SL_slash] using hs g)
      holo' := hf
      zero_at_cusps' := by
        intro c hc
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
        intro g _
        rw [hs]
        exact hz }
  obtain ⟨c,hc⟩ :=
    Integration.MoonshineLevelOneWeightZeroPinned.levelOne_weight_zero_const r
  have he : f = Function.const ℍ c := hc
  rw [IsZeroAtImInfty, Filter.ZeroAtFilter,he] at hz
  have hc0 : c=0 := tendsto_nhds_unique tendsto_const_nhds hz
  intro τ
  rw [he,hc0]
  rfl

-- A4 only needs the diagonal. Its own residual has zero cusp if the
-- original degree-82 coefficient packet is reflected. No symmetry
-- or full bivariate construction is needed for THIS theorem.
def diagonalResidual (P : Polynomial ℂ) (τ : ℍ) : ℂ :=
  actualProduct τ (j τ)-P.eval (j τ)

theorem diagonalIdentity (P : Polynomial ℂ)
    (hz : IsZeroAtImInfty (diagonalResidual P)) :
    ∀ τ, actualProduct τ (j τ)=P.eval (j τ) := by
  have hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (diagonalResidual P) :=
    (productHolo j jHolo).sub (polynomialHolo P)
  have hi (g : SL(2, ℤ)) (τ : ℍ) :
      diagonalResidual P (g • τ)=diagonalResidual P τ := by
    unfold diagonalResidual
    rw [jInvariant,productInvariant]
  intro τ
  exact sub_eq_zero.mp (invariantZero _ hf hi hz τ)

theorem actualCMDiagonalRoot (P : Polynomial ℂ)
    (hz : IsZeroAtImInfty (diagonalResidual P)) :
    P.eval (j Integration.Paper9ActualCMPoint.cmTau)=0 :=
  (diagonalIdentity P hz _).symm.trans cmProductZero

-- The fixed-target slice is similarly a single weight-zero residual.
def sliceResidual (K : ℂ) (P : Polynomial ℂ) (τ : ℍ) : ℂ :=
  actualProduct τ K-P.eval (j τ)

theorem sliceIdentity (K : ℂ) (P : Polynomial ℂ)
    (hz : IsZeroAtImInfty (sliceResidual K P)) :
    ∀ τ, actualProduct τ K=P.eval (j τ) := by
  have hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (sliceResidual K P) :=
    (productHolo (fun _ => K) mdifferentiable_const).sub (polynomialHolo P)
  have hi (g : SL(2, ℤ)) (τ : ℍ) :
      sliceResidual K P (g • τ)=sliceResidual K P τ := by
    unfold sliceResidual
    rw [jInvariant,productInvariant]
  intro τ
  exact sub_eq_zero.mp (invariantZero _ hf hi hz τ)

-- Keep the actual ramified parameter t = exp(2 pi i tau / 41).
-- Cancellation of t^d is legitimate away from the cusp. The residual
-- then extends with zero limit, without a separate inverse-j theorem.
def tParam (τ : ℍ) : ℂ := Periodic.qParam 41 (τ : ℂ)

theorem tNonzero (τ : ℍ) : tParam τ ≠ 0 :=
  Periodic.qParam_ne_zero 41 τ

theorem tPower (τ : ℍ) : tParam τ^41=qExt τ := by
  unfold tParam qExt Periodic.qParam
  rw [← Complex.exp_nat_mul]
  congr 1
  norm_num
  ring

theorem tTendsto : Tendsto tParam atImInfty (𝓝 0) :=
  UpperHalfPlane.qParam_tendsto_atImInfty (h := 41) (by norm_num)

theorem normalizedResidualZero (d : ℕ) (f : ℍ → ℂ) (G : ℂ → ℂ)
    (hG : ContinuousAt G 0)
    (he : ∀ᶠ τ in atImInfty,
      tParam τ^d*f τ=tParam τ^(d+1)*G (tParam τ)) :
    IsZeroAtImInfty f := by
  have hlocal : ∀ᶠ τ in atImInfty, f τ=tParam τ*G (tParam τ) :=
    he.mono fun τ h => by
      apply mul_left_cancel₀ (pow_ne_zero d (tNonzero τ))
      rw [h,pow_succ,mul_assoc]
  have ht := tTendsto.mul (hG.tendsto.comp tTendsto)
  rw [zero_mul] at ht
  rw [IsZeroAtImInfty,Filter.ZeroAtFilter]
  exact ht.congr' hlocal.symm

-- Actual normalized unit factors, retaining the sign and q/t powers.
theorem diagonalFiniteFactor (q t : ℂ) (hq : q≠0) (ht : t≠0)
    (hp : q=t^41) :
    q*(jQ q-jQ t)=jUnit q-t^40*jUnit t := by
  unfold jQ
  rw [hp]
  field_simp [ht] <;> ring

theorem diagonalInfinityFactor (q : ℂ) (hq : q≠0) :
    q^41*(jQ q-jQ (q^41))=q^40*jUnit q-jUnit (q^41) := by
  unfold jQ
  field_simp [hq] <;> ring

theorem fixedFiniteFactor (K t : ℂ) (ht : t≠0) :
    -t*(K-jQ t)=jUnit t-K*t := by
  unfold jQ
  field_simp [ht] <;> ring

theorem fixedInfinityFactor (K q : ℂ) (hq : q≠0) :
    -q^41*(K-jQ (q^41))=jUnit (q^41)-K*q^41 := by
  unfold jQ
  field_simp [hq] <;> ring

-- Direct residual consumers at the original finite truncation depths.
-- The unpaid producer is an analytic order factorization, not a new
-- modularity, symmetry or arbitrary real equality assumption.
theorem diagonalFromRamifiedReplay (P : Polynomial ℂ) (G : ℂ → ℂ)
    (hG : ContinuousAt G 0)
    (he : ∀ᶠ τ in atImInfty,
      tParam τ^3362*diagonalResidual P τ =
        tParam τ^3363*G (tParam τ)) :
    ∀ τ, actualProduct τ (j τ)=P.eval (j τ) :=
  diagonalIdentity P (normalizedResidualZero 3362 _ G hG he)

theorem sliceFromRamifiedReplay (K : ℂ) (P : Polynomial ℂ) (G : ℂ → ℂ)
    (hG : ContinuousAt G 0)
    (he : ∀ᶠ τ in atImInfty,
      tParam τ^1722*sliceResidual K P τ =
        tParam τ^1723*G (tParam τ)) :
    ∀ τ, actualProduct τ K=P.eval (j τ) :=
  sliceIdentity K P (normalizedResidualZero 1722 _ G hG he)


end
end Integration.Paper9HeckePoleRemoval
