import Synthesis.NavierStokesEuclideanSignedProductMajorantExact

/-!
Global SPATIAL integrability of the actual amplitude-convolution envelope
from weighted Fourier energy. Classical weighted Cauchy/Young and Fubini.
For W=R²+|η|², the remaining scalar integral is ∫W⁻²=π²/R.
The resulting E^(1/2)D^(3/2) scaling is NOT an energy-only spacetime
bound and does not pay arbitrary-data continuation.
-/
namespace DASHI.NavierStokes.EuclideanMidpoint
open MeasureTheory
noncomputable section

/-- Cauchy-Schwarz on the actual measure, via the integral of a square.
No assumption that the individual unsquared functions lie in L¹. -/
theorem integral_product_sq_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (g h : X → ℝ)
    (hg : Integrable (fun x => g x^2) μ)
    (hh : Integrable (fun x => h x^2) μ)
    (hgh : Integrable (fun x => g x*h x) μ) :
    (∫ x, g x*h x ∂μ)^2 ≤
      (∫ x, g x^2 ∂μ)*(∫ x, h x^2 ∂μ) := by
  let A := ∫ x, g x^2 ∂μ
  let B := ∫ x, h x^2 ∂μ
  let C := ∫ x, g x*h x ∂μ
  have hA : 0 ≤ A := integral_nonneg (fun _ => sq_nonneg _)
  have hq (r : ℝ) : 0 ≤ r^2*A-2*r*C+B := by
    have hn : 0 ≤ ∫ x, (r*g x-h x)^2 ∂μ :=
      integral_nonneg (fun _ => sq_nonneg _)
    have he : (fun x => (r*g x-h x)^2) =
        fun x => r^2*(g x^2)-(2*r)*(g x*h x)+h x^2 := by
      funext x
      ring
    rw [he,integral_add ((hg.const_mul (r^2)).sub (hgh.const_mul (2*r))) hh,
      integral_sub (hg.const_mul (r^2)) (hgh.const_mul (2*r)),
      integral_const_mul,integral_const_mul] at hn
    exact hn
  change C^2 ≤ A*B
  by_cases ha : A=0
  · by_cases hc : C=0
    · simp [ha,hc]
    · have hbad := hq ((B+1)/(2*C))
      rw [ha,mul_zero,zero_sub] at hbad
      have he : 2*((B+1)/(2*C))*C=B+1 := by
        field_simp [hc] <;> ring
      rw [he] at hbad
      linarith
  · have ha' : 0 < A := lt_of_le_of_ne hA (Ne.symm ha)
    have hn := mul_nonneg ha'.le (hq (C/A))
    have he : A*((C/A)^2*A-2*(C/A)*C+B)=A*B-C^2 := by
      field_simp [ha] <;> ring
    rw [he] at hn
    linarith

def selfConvolution (f : Vec3 → ℝ) (ξ : Vec3) : ℝ :=
  ∫ η, f η*f (ξ-η)

/-- Exact convolution mass on the original R³ Haar measure. Integrate
output first at fixed η, using translation, then Fubini back to the
same-output order. This also produces a.e. integrability of each fibre. -/
theorem nonnegative_convolution_mass (f : Vec3 → ℝ)
    (hm : Measurable f) (hf : Integrable f) (hn : ∀ x,0 ≤ f x) :
    (∀ᵐ ξ ∂volume, Integrable (fun η => f η*f (ξ-η))) ∧
    Integrable (selfConvolution f) ∧
    (∫ ξ,selfConvolution f ξ)=(∫ η,f η)^2 := by
  let μ : Measure Vec3 := volume
  let k : Vec3 × Vec3 → ℝ := fun z => f z.2*f (z.1-z.2)
  have hkm : Measurable k :=
    (hm.comp measurable_snd).mul
      (hm.comp (measurable_fst.sub measurable_snd))
  have hrow (η : Vec3) : Integrable (fun ξ => k (ξ,η)) μ := by
    have h := (hf.comp_add_right (-η)).const_mul (f η)
    simpa [k,sub_eq_add_neg] using h
  have hrowMass (η : Vec3) : (∫ ξ,k (ξ,η) ∂μ)=f η*(∫ ξ,f ξ ∂μ) := by
    change (∫ ξ,f η*f (ξ-η) ∂μ)=_
    rw [integral_const_mul]
    congr 1
    simpa [sub_eq_add_neg] using integral_add_right_eq_self f μ (-η)
  have hnorm : (fun η : Vec3 => ∫ ξ, ‖k (ξ,η)‖ ∂μ) =
      fun η => f η*(∫ ξ,f ξ ∂μ) := by
    funext η
    rw [← hrowMass η]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hn η) (hn (ξ-η)))]
  have hk : Integrable k (μ.prod μ) :=
    (integrable_prod_iff' hkm.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hrow, by rw [hnorm]; exact hf.mul_const _⟩
  have hmarg : Integrable (selfConvolution f) := hk.integral_prod_left
  refine ⟨hk.prod_right_ae,hmarg,?_⟩
  change (∫ ξ,∫ η,k (ξ,η) ∂μ ∂μ)=_
  rw [← integral_prod k hk,integral_prod_symm k hk]
  simp_rw [hrowMass]
  rw [integral_mul_const]
  ring

/-- Pointwise convolution bound for a nonnegative L² amplitude. It
also constructs the integrability of the translated product. -/
theorem selfConvolution_le_squareMass (f : Vec3 → ℝ)
    (hm : Measurable f) (hf : Integrable (fun x => f x^2))
    (hn : ∀ x,0 ≤ f x) (ξ : Vec3) :
    Integrable (fun η => f η*f (ξ-η)) ∧
    selfConvolution f ξ ≤ ∫ η,f η^2 := by
  have hs := hf.comp_sub_left ξ
  have hg : Integrable (fun η : Vec3 => (f η^2+f (ξ-η)^2)/2) :=
    (hf.add hs).div_const 2
  have hp (η : Vec3) : f η*f (ξ-η) ≤ (f η^2+f (ξ-η)^2)/2 := by
    nlinarith only [sq_nonneg (f η-f (ξ-η))]
  have hi : Integrable (fun η => f η*f (ξ-η)) :=
    hg.mono' (hm.mul (hm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hn η) (hn (ξ-η)))]
        exact hp η)
  refine ⟨hi,?_⟩
  unfold selfConvolution
  calc
    (∫ η,f η*f (ξ-η)) ≤ ∫ η,(f η^2+f (ξ-η)^2)/2 :=
      integral_mono hi hg hp
    _ = ∫ η,f η^2 := by
      rw [integral_div,integral_add hf hs,integral_sub_left_eq_self]
      ring

/-- Weighted convolution Cauchy on the actual fixed-output fibre.
A=w² W and b=W⁻¹ retain exact reciprocal weight, no generic estimate
for arbitrary signed coefficients. -/
theorem weighted_convolution_point
    (w W : Vec3 → ℝ) (hw : ∀ x,0 ≤ w x) (hW : ∀ x,0 < W x)
    (ξ : Vec3)
    (hA : Integrable (fun η => (w η^2*W η)*(w (ξ-η)^2*W (ξ-η))))
    (hB : Integrable (fun η => (W η)⁻¹*(W (ξ-η))⁻¹))
    (hC : Integrable (fun η => w η*w (ξ-η))) :
    (selfConvolution w ξ)^2 ≤
      selfConvolution (fun η => w η^2*W η) ξ *
      selfConvolution (fun η => (W η)⁻¹) ξ := by
  let G := fun η => w η*w (ξ-η)*Real.sqrt (W η*W (ξ-η))
  let H := fun η => (Real.sqrt (W η*W (ξ-η)))⁻¹
  have heG : (fun η => G η^2) =
      fun η => (w η^2*W η)*(w (ξ-η)^2*W (ξ-η)) := by
    funext η
    dsimp [G]
    rw [mul_pow,Real.sq_sqrt (mul_nonneg (hW η).le (hW (ξ-η)).le)]
    ring
  have heH : (fun η => H η^2) = fun η => (W η)⁻¹*(W (ξ-η))⁻¹ := by
    funext η
    dsimp [H]
    rw [inv_pow,Real.sq_sqrt (mul_nonneg (hW η).le (hW (ξ-η)).le)]
    rw [mul_inv_rev₀,mul_comm]
  have heC : (fun η => G η*H η) = fun η => w η*w (ξ-η) := by
    funext η
    dsimp [G,H]
    rw [mul_assoc,mul_inv_cancel₀ (ne_of_gt
      (Real.sqrt_pos.2 (mul_pos (hW η) (hW (ξ-η))))),mul_one]
  have h := integral_product_sq_le (volume : Measure Vec3) G H
    (heG.symm ▸ hA) (heH.symm ▸ hB) (heC.symm ▸ hC)
  rw [heG,heH,heC] at h
  exact h

/-- Global output L² integrability of the ACTUAL convolution envelope.
Weighted energy A∈L¹ and inverse weight b∈L² suffice. This pays the
fixed-time spatial tail, not a cutoff-uniform critical time estimate. -/
theorem weighted_convolution_global
    (w W : Vec3 → ℝ)
    (hw : ∀ x,0 ≤ w x) (hW : ∀ x,0 < W x)
    (hmw : Measurable w) (hmW : Measurable W)
    (hE : Integrable (fun x => w x^2))
    (hA : Integrable (fun x => w x^2*W x))
    (hB : Integrable (fun x => ((W x)⁻¹)^2)) :
    Integrable (fun ξ => (selfConvolution w ξ)^2) ∧
      (∫ ξ,(selfConvolution w ξ)^2) ≤
        (∫ x,((W x)⁻¹)^2)*(∫ x,w x^2*W x)^2 := by
  let A := fun x => w x^2*W x
  let b := fun x => (W x)⁻¹
  let B := ∫ x,b x^2
  have hnA : ∀ x,0 ≤ A x := fun x => mul_nonneg (sq_nonneg _) (hW x).le
  have hnb : ∀ x,0 ≤ b x := fun x => inv_nonneg.mpr (hW x).le
  have hmA : Measurable A := (hmw.pow_const 2).mul hmW
  have hmb : Measurable b := hmW.inv
  obtain ⟨hrows,hint,hmass⟩ := nonnegative_convolution_mass A hmA hA hnA
  have hBnonneg : 0 ≤ B := integral_nonneg (fun _ => sq_nonneg _)
  have hbound : ∀ᵐ ξ ∂volume,
      (selfConvolution w ξ)^2 ≤ B*selfConvolution A ξ := by
    filter_upwards [hrows] with ξ hξ
    obtain ⟨hb, hbc⟩ := selfConvolution_le_squareMass b hmb hB hnb ξ
    obtain ⟨hc, _⟩ := selfConvolution_le_squareMass w hmw hE hw ξ
    have hp := weighted_convolution_point w W hw hW ξ hξ hb hc
    exact le_trans hp (by
      rw [mul_comm B]
      exact mul_le_mul_of_nonneg_left hbc
        (integral_nonneg (fun η => mul_nonneg (hnA η) (hnA (ξ-η)))))
  have hkm : Measurable (fun z : Vec3 × Vec3 => w z.2*w (z.1-z.2)) :=
    (hmw.comp measurable_snd).mul (hmw.comp (measurable_fst.sub measurable_snd))
  have hmC : AEStronglyMeasurable (selfConvolution w) :=
    hkm.aestronglyMeasurable.integral_prod_right'
  have hC : Integrable (fun ξ => (selfConvolution w ξ)^2) :=
    (hint.const_mul B).mono' (hmC.pow 2) (by
      filter_upwards [hbound] with ξ hξ
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hξ)
  refine ⟨hC,?_⟩
  have hi := integral_mono_ae hC (hint.const_mul B) hbound
  rw [integral_const_mul,hmass] at hi
  exact hi

end
end DASHI.NavierStokes.EuclideanMidpoint
