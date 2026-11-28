import Synthesis.NavierStokesEuclideanDoubleInteractionKernelExact

/-!
Product, not additive, majorant for the actual nine-coordinate signed
centered kernel. Keep BOTH input pairs. The local Young estimate
|A|²+|B|² is unsuitable on an unrestricted independent spectator fibre.
Classical Cauchy/Lagrange and Leray contraction; DASHI same-cell attachment.
No cutoff-uniform spacetime bound is inferred.
-/
namespace DASHI.NavierStokes.EuclideanMidpoint
open MeasureTheory
noncomputable section

noncomputable def amplitude (u : CVec3) : ℝ := Real.sqrt (phaseMass u)

theorem amplitude_nonnegative (u : CVec3) : 0 ≤ amplitude u :=
  Real.sqrt_nonneg _

theorem amplitude_sq (u : CVec3) : amplitude u ^ 2 = phaseMass u :=
  Real.sq_sqrt (phaseMass_nonneg u)

def realLeray (a b : Vec3) : Vec3 :=
  fun i => b i-a i*realDot a b/massSq a

theorem realLeray_pythagoras (a b : Vec3) (ha : massSq a ≠ 0) :
    massSq (realLeray a b)+realDot a b ^ 2/massSq a = massSq b := by
  unfold realLeray realDot massSq at *
  simp only [Fin.sum_univ_three] at *
  field_simp [ha] <;> ring

def lerayVector (a : Vec3) (v : CVec3) : CVec3 :=
  fun i => v i-(a i/massSq a : ℝ)*outputDot a v

theorem projectedConvection_eq_lerayVector (a : Vec3) (u v : CVec3) :
    projectedConvection a u v = lerayVector a (rawConvection a u v) := by
  funext i
  unfold projectedConvection lerayVector
  push_cast
  ring

theorem lerayVector_real (a : Vec3) (v : CVec3) :
    (fun i => (lerayVector a v i).re) =
      realLeray a (fun i => (v i).re) := by
  funext i
  simp [lerayVector,realLeray,realDot,outputDot,Fin.sum_univ_three,
    Complex.sub_re,Complex.add_re,Complex.mul_re] <;> ring

theorem lerayVector_imag (a : Vec3) (v : CVec3) :
    (fun i => (lerayVector a v i).im) =
      realLeray a (fun i => (v i).im) := by
  funext i
  simp [lerayVector,realLeray,realDot,outputDot,Fin.sum_univ_three,
    Complex.sub_im,Complex.add_im,Complex.mul_im] <;> ring

theorem leray_phase_contraction (a : Vec3) (v : CVec3)
    (ha : 0 < massSq a) : phaseMass (lerayVector a v) ≤ phaseMass v := by
  unfold phaseMass
  rw [lerayVector_real,lerayVector_imag]
  have h1 := realLeray_pythagoras a (fun i => (v i).re) (ne_of_gt ha)
  have h2 := realLeray_pythagoras a (fun i => (v i).im) (ne_of_gt ha)
  have h3 := div_nonneg (sq_nonneg (realDot a (fun i => (v i).re))) ha.le
  have h4 := div_nonneg (sq_nonneg (realDot a (fun i => (v i).im))) ha.le
  linarith

theorem rawConvection_mass (a : Vec3) (u v : CVec3) :
    phaseMass (rawConvection a u v) = phaseDotSq a u * phaseMass v := by
  rw [phaseDotSq_eq_complex_normSq]
  change phaseMass (rawConvection a u v) = Complex.normSq (outputDot a u) * phaseMass v
  rw [phaseMass_eq_complex_normSq_sum,phaseMass_eq_complex_normSq_sum v]
  simp only [rawConvection,Complex.normSq_mul,Complex.normSq_I,one_mul,
    Finset.mul_sum]

theorem projected_cell_mass_bound (a : Vec3) (u v : CVec3)
    (ha : 0 < massSq a) :
    phaseMass (projectedConvection a u v) ≤ massSq a*phaseMass u*phaseMass v := by
  rw [projectedConvection_eq_lerayVector]
  calc
    phaseMass (lerayVector a (rawConvection a u v)) ≤
        phaseMass (rawConvection a u v) := leray_phase_contraction a _ ha
    _ = phaseDotSq a u*phaseMass v := rawConvection_mass a u v
    _ ≤ massSq a*phaseMass u*phaseMass v :=
      mul_le_mul_of_nonneg_right (phaseDotSq_le a u) (phaseMass_nonneg v)

theorem projected_cell_amplitude_bound (a : Vec3) (u v : CVec3)
    (ha : 0 < massSq a) :
    amplitude (projectedConvection a u v) ≤
      Real.sqrt (massSq a)*amplitude u*amplitude v := by
  unfold amplitude
  have h := Real.sqrt_le_sqrt (projected_cell_mass_bound a u v ha)
  rw [Real.sqrt_mul (mul_nonneg ha.le (phaseMass_nonneg u)),
      Real.sqrt_mul ha.le] at h
  exact h

def realHermitian (A B : CVec3) : ℝ :=
  ∑ i : Fin 3, ((A i).re*(B i).re+(A i).im*(B i).im)

theorem realHermitian_eq (A B : CVec3) :
    realHermitian A B = ∑ i : Fin 3, ((A i)*star (B i)).re := by
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re] <;> ring

/-- Full six-real-coordinate Lagrange identity, all 15 wedge minors. -/
theorem realHermitian_sq_bound (A B : CVec3) :
    realHermitian A B ^ 2 ≤ phaseMass A*phaseMass B := by
  have h01 := sq_nonneg ((A 0).re*(B 0).im-(A 0).im*(B 0).re)
  have h02 := sq_nonneg ((A 0).re*(B 1).re-(A 1).re*(B 0).re)
  have h03 := sq_nonneg ((A 0).re*(B 1).im-(A 1).im*(B 0).re)
  have h04 := sq_nonneg ((A 0).re*(B 2).re-(A 2).re*(B 0).re)
  have h05 := sq_nonneg ((A 0).re*(B 2).im-(A 2).im*(B 0).re)
  have h12 := sq_nonneg ((A 0).im*(B 1).re-(A 1).re*(B 0).im)
  have h13 := sq_nonneg ((A 0).im*(B 1).im-(A 1).im*(B 0).im)
  have h14 := sq_nonneg ((A 0).im*(B 2).re-(A 2).re*(B 0).im)
  have h15 := sq_nonneg ((A 0).im*(B 2).im-(A 2).im*(B 0).im)
  have h23 := sq_nonneg ((A 1).re*(B 1).im-(A 1).im*(B 1).re)
  have h24 := sq_nonneg ((A 1).re*(B 2).re-(A 2).re*(B 1).re)
  have h25 := sq_nonneg ((A 1).re*(B 2).im-(A 2).im*(B 1).re)
  have h34 := sq_nonneg ((A 1).im*(B 2).re-(A 2).re*(B 1).im)
  have h35 := sq_nonneg ((A 1).im*(B 2).im-(A 2).im*(B 1).im)
  have h45 := sq_nonneg ((A 2).re*(B 2).im-(A 2).im*(B 2).re)
  simp only [realHermitian,phaseMass,massSq,Fin.sum_univ_three]
  nlinarith only [h01,h02,h03,h04,h05,h12,h13,h14,h15,h23,h24,h25,h34,h35,h45]

theorem realHermitian_abs_bound (A B : CVec3) :
    |realHermitian A B| ≤ amplitude A * amplitude B := by
  have h := Real.sqrt_le_sqrt (realHermitian_sq_bound A B)
  rw [Real.sqrt_sq_eq_abs,Real.sqrt_mul (phaseMass_nonneg A)] at h
  exact h

noncomputable def pairAmplitude (U : Vec3 → CVec3) (ξ η : Vec3) : ℝ :=
  amplitude (U η)*amplitude (U (fun i => ξ i-η i))

theorem pairAmplitude_nonnegative (U : Vec3 → CVec3) (ξ η : Vec3) :
    0 ≤ pairAmplitude U ξ η :=
  mul_nonneg (amplitude_nonnegative _) (amplitude_nonnegative _)

theorem signed_gram_product_bound (U : Vec3 → CVec3) (ξ η η' : Vec3)
    (hξ : 0 < massSq ξ) :
    |projectedDoubleGram U ξ η η'| ≤
      2*massSq ξ*pairAmplitude U ξ η*pairAmplitude U ξ η' := by
  let A := projectedConvection ξ (U η) (U (fun i => ξ i-η i))
  let B := projectedConvection ξ (U η') (U (fun i => ξ i-η' i))
  change |2*(∑ i : Fin 3, ((A i)*star (B i)).re)| ≤ _
  rw [← realHermitian_eq,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)]
  have hA : amplitude A ≤ Real.sqrt (massSq ξ)*pairAmplitude U ξ η := by
    simpa [A,pairAmplitude,mul_assoc] using
      projected_cell_amplitude_bound ξ (U η) (U (fun i => ξ i-η i)) hξ
  have hB : amplitude B ≤ Real.sqrt (massSq ξ)*pairAmplitude U ξ η' := by
    simpa [B,pairAmplitude,mul_assoc] using
      projected_cell_amplitude_bound ξ (U η') (U (fun i => ξ i-η' i)) hξ
  have hp := mul_le_mul hA hB (amplitude_nonnegative B)
    (mul_nonneg (Real.sqrt_nonneg _) (pairAmplitude_nonnegative U ξ η))
  calc
    2*|realHermitian A B| ≤ 2*(amplitude A*amplitude B) :=
      mul_le_mul_of_nonneg_left (realHermitian_abs_bound A B) (by norm_num)
    _ ≤ 2*((Real.sqrt (massSq ξ)*pairAmplitude U ξ η)*
        (Real.sqrt (massSq ξ)*pairAmplitude U ξ η')) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 2*massSq ξ*pairAmplitude U ξ η*pairAmplitude U ξ η' := by
      rw [show (Real.sqrt (massSq ξ)*pairAmplitude U ξ η)*
          (Real.sqrt (massSq ξ)*pairAmplitude U ξ η') =
          (Real.sqrt (massSq ξ))^2*pairAmplitude U ξ η*pairAmplitude U ξ η' by ring,
        Real.sq_sqrt hξ.le]
      ring

def centeredSignedKernel (ν : ℝ) (U : Vec3 → CVec3) (ξ η η' : Vec3) : ℝ :=
  centeredCoefficient ν ξ η η' * projectedDoubleGram U ξ η η'

/-- The actual four-amplitude bound is integrable in the two input
variables whenever the original amplitude convolutions are integrable.
Unlike a sum of pair squares it retains BOTH independent fibres. -/
theorem centered_signed_product_majorant (ν : ℝ) (U : Vec3 → CVec3)
    (ξ η η' : Vec3) (hν : 0 < ν) (hξ : 0 < massSq ξ) :
    |centeredSignedKernel ν U ξ η η'| ≤
      (2/ν)*pairAmplitude U ξ η*pairAmplitude U ξ η' := by
  have ha : 0 < outputRate ν ξ := mul_pos hν hξ
  have hs := centeredDoubleRate_nonneg ν hν.le ξ η η'
  have hc : 0 ≤ centeredCoefficient ν ξ η η' := by
    rw [centeredCoefficient_eq_saturation ν ξ η η' hν hξ]
    exact div_nonneg hs (mul_nonneg ha.le (add_nonneg ha.le hs))
  unfold centeredSignedKernel
  rw [abs_mul,abs_of_nonneg hc]
  calc
    centeredCoefficient ν ξ η η' * |projectedDoubleGram U ξ η η'| ≤
        actualOutputResolvent ν ξ * |projectedDoubleGram U ξ η η'| :=
      mul_le_mul_of_nonneg_right
        (centeredCoefficient_le_outputResolvent ν ξ η η' hν hξ) (abs_nonneg _)
    _ ≤ actualOutputResolvent ν ξ *
        (2*massSq ξ*pairAmplitude U ξ η*pairAmplitude U ξ η') :=
      mul_le_mul_of_nonneg_left (signed_gram_product_bound U ξ η η' hξ)
        (div_nonneg (by norm_num) ha.le)
    _ = (2/ν)*pairAmplitude U ξ η*pairAmplitude U ξ η' := by
      unfold actualOutputResolvent outputRate
      field_simp [ne_of_gt hν,ne_of_gt hξ] <;> ring

/-- Actual same-output two-input integration. This uses a product of
the two physical pair amplitudes, not a spurious unweighted spectator.
Integrability of the signed source and amplitude is explicit. -/
theorem centered_fixed_output_integral_bound
    (ν : ℝ) (U : Vec3 → CVec3) (ξ : Vec3)
    (hν : 0 < ν) (hξ : 0 < massSq ξ)
    (hp : Integrable (pairAmplitude U ξ))
    (hk : ∀ η, Integrable (centeredSignedKernel ν U ξ η))
    (houter : Integrable (fun η => ∫ η', centeredSignedKernel ν U ξ η η')) :
    |∫ η, ∫ η', centeredSignedKernel ν U ξ η η'| ≤
      (2/ν)*(∫ η, pairAmplitude U ξ η)^2 := by
  let k := fun η η' => centeredSignedKernel ν U ξ η η'
  let p := pairAmplitude U ξ
  have hpoint (η : Vec3) :
      |∫ η', k η η'| ≤ ((2/ν)*p η)*(∫ η',p η') := by
    have h := integral_mono (hk η).abs (hp.const_mul ((2/ν)*p η))
      (fun η' => centered_signed_product_majorant ν U ξ η η' hν hξ)
    rw [integral_const_mul] at h
    exact le_trans (by simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (f := k η)) h
  have hE : 0 ≤ ∫ η, p η := integral_nonneg (pairAmplitude_nonnegative U ξ)
  have hi : Integrable (fun η => ((2/ν)*p η)*(∫ η',p η')) := by
    have h := (hp.const_mul (2/ν)).mul_const (∫ η',p η')
    simpa [p] using h
  have h := integral_mono houter.abs hi hpoint
  calc
    |∫ η, ∫ η', k η η'| ≤ ∫ η, |∫ η', k η η'| := by
      simpa [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (f := fun η => ∫ η', k η η')
    _ ≤ ∫ η, ((2/ν)*p η)*(∫ η',p η') := h
    _ = (2/ν)*(∫ η,p η)^2 := by
      rw [integral_mul_const,integral_const_mul]
      ring

/-- The physical L² energy alone controls the pair-amplitude convolution
at every fixed output. Translation-reflection preserves Lebesgue
measure (Mathlib additive Haar integral_sub_left_eq_self); no artificial
cutoff or extra assumption of integrability of the product is needed. -/
theorem pairAmplitude_integrable_and_energy_bound
    (U : Vec3 → CVec3) (ξ : Vec3)
    (hU : Measurable (fun η => amplitude (U η)))
    (hE : Integrable (fun η => phaseMass (U η))) :
    Integrable (pairAmplitude U ξ) ∧
      (∫ η, pairAmplitude U ξ η) ≤ ∫ η, phaseMass (U η) := by
  let e : Vec3 → ℝ := fun η => phaseMass (U η)
  have hs : Integrable (fun η : Vec3 => e (ξ-η)) :=
    hE.comp_sub_left ξ
  have hm : Measurable (pairAmplitude U ξ) := by
    exact hU.mul (hU.comp (measurable_const.sub measurable_id))
  have hb (η : Vec3) :
      pairAmplitude U ξ η ≤ (e η+e (ξ-η))/2 := by
    have h := sq_nonneg (amplitude (U η)-amplitude (U (ξ-η)))
    rw [show (amplitude (U η)-amplitude (U (ξ-η)))^2 =
        amplitude (U η)^2+amplitude (U (ξ-η))^2-
        2*amplitude (U η)*amplitude (U (ξ-η)) by ring,
      amplitude_sq,amplitude_sq] at h
    change amplitude (U η)*amplitude (U (ξ-η)) ≤ _
    linarith
  have hg : Integrable (fun η : Vec3 => (e η+e (ξ-η))/2) := by
    exact (hE.add hs).div_const 2
  have hp : Integrable (pairAmplitude U ξ) :=
    hg.mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pairAmplitude_nonnegative U ξ η)]
        exact hb η)
  refine ⟨hp,?_⟩
  calc
    (∫ η, pairAmplitude U ξ η) ≤ ∫ η, (e η+e (ξ-η))/2 :=
      integral_mono hp hg hb
    _ = ∫ η, phaseMass (U η) := by
      rw [integral_div,integral_add hE hs,integral_sub_left_eq_self e volume ξ]
      change ((∫ η, e η)+(∫ η,e η))/2 = _
      ring

/-- Source integrability at each output now follows from finite energy
and measurability of the actual cell; no extra positive pair-integral
authority. For the outer integral we retain the explicit measurable
inner marginal hypothesis (standard measurable integral/Fubini ingress). -/
theorem centered_fixed_output_energy_bound
    (ν : ℝ) (U : Vec3 → CVec3) (ξ : Vec3)
    (hν : 0 < ν) (hξ : 0 < massSq ξ)
    (hU : Measurable (fun η => amplitude (U η)))
    (hE : Integrable (fun η => phaseMass (U η)))
    (hk : ∀ η, AEStronglyMeasurable (centeredSignedKernel ν U ξ η))
    (houter : AEStronglyMeasurable
      (fun η => ∫ η', centeredSignedKernel ν U ξ η')) :
    |∫ η, ∫ η', centeredSignedKernel ν U ξ η η'| ≤
      (2/ν)*(∫ η, phaseMass (U η))^2 := by
  obtain ⟨hp,hpE⟩ := pairAmplitude_integrable_and_energy_bound U ξ hU hE
  let p := pairAmplitude U ξ
  let k := centeredSignedKernel ν U ξ
  have hi (η : Vec3) : Integrable (k η) :=
    (hp.const_mul ((2/ν)*p η)).mono' (hk η)
      (Filter.Eventually.of_forall fun η' => by
        rw [Real.norm_eq_abs]
        exact centered_signed_product_majorant ν U ξ η η' hν hξ)
  have hb (η : Vec3) :
      |∫ η', k η η'| ≤ ((2/ν)*p η)*(∫ η',p η') := by
    have h := norm_integral_le_of_norm_le (hp.const_mul ((2/ν)*p η))
      (Filter.Eventually.of_forall fun η' => by
        rw [Real.norm_eq_abs]
        exact centered_signed_product_majorant ν U ξ η η' hν hξ)
    rw [integral_const_mul] at h
    simpa [Real.norm_eq_abs] using h
  have hM : Integrable (fun η => ((2/ν)*p η)*(∫ η',p η')) :=
    (hp.const_mul (2/ν)).mul_const _
  have ho : Integrable (fun η => ∫ η',k η η') :=
    hM.mono' houter (Filter.Eventually.of_forall fun η => by
      rw [Real.norm_eq_abs]; exact hb η)
  have h := centered_fixed_output_integral_bound ν U ξ hν hξ hp hi ho
  have hnn : 0 ≤ ∫ η,p η := integral_nonneg (pairAmplitude_nonnegative U ξ)
  have hs : (∫ η,p η)^2 ≤ (∫ η,phaseMass (U η))^2 :=
    pow_le_pow_left₀ hnn hpE 2
  exact le_trans h (mul_le_mul_of_nonneg_left hs (div_nonneg (by norm_num) hν.le))

/-- Local output region: finite volume gives a finite integral from
energy alone. This does not assert an infinite-volume E-only bound or
a uniform time-integrated critical continuation estimate. -/
theorem finite_output_region_budget (ν E : ℝ) (hν : 0 < ν)
    (S : Set Vec3) (hS : volume S < ⊤) (g : Vec3 → ℝ)
    (hg : AEStronglyMeasurable g (volume.restrict S))
    (hb : ∀ᵐ ξ ∂volume.restrict S, |g ξ| ≤ (2/ν)*E^2) :
    Integrable g (volume.restrict S) ∧
      |∫ ξ in S,g ξ| ≤ (volume S).toReal*((2/ν)*E^2) := by
  letI : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa using hS⟩
  have hc : Integrable (fun _ : Vec3 => (2/ν)*E^2) (volume.restrict S) :=
    integrable_const _
  have hnorm : ∀ᵐ ξ ∂volume.restrict S, ‖g ξ‖ ≤ (2/ν)*E^2 := by
    simpa only [Real.norm_eq_abs] using hb
  refine ⟨hc.mono' hg hnorm,?_⟩
  have h := norm_integral_le_of_norm_le hc hnorm
  simpa [Real.norm_eq_abs,Measure.real,Measure.restrict_apply_univ,
    smul_eq_mul] using h

end
end DASHI.NavierStokes.EuclideanMidpoint
