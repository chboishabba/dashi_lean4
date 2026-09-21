import Synthesis.RiemannProjectiveHorizontalRadialMonotonicity
import Synthesis.RiemannNormalizedProjectiveHorizontalArbitraryCutoff

/-!
# A linearly growing signed band for the actual horizontal projective source

The normalized horizontal coefficient has the exact physical scaling

  Q_proj(t,a/t,delta/t)
    = 4 t^3 integral g_t(u) B_t(u)
        H_a(u) cos(delta*u) du,

where H_a=coshMinusOneDivSq a.

The canonical support radius is

  Lambda_t = 9*pi/(4t).

The radial monotonicity theorem shows that the weight
H_a(u) cos(delta*u) is strictly increasing in |u| whenever

  |delta| Lambda_t <= pi/4.

Thus every source with

  |delta| <= t/9

has strictly negative Q coefficient.  Multiplicity and the explicit a^2/t^2
factor are nonnegative, so the actual horizontal source term is nonpositive
throughout this entire linearly-growing ordinate band.

This removes the old fixed-width signed-near bottleneck.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

theorem coshMinusOneDivSq_scale
    {t a u : ℝ} (ht : 0 < t) :
    coshMinusOneDivSq (a/t) (t*u)
      = t^2 * coshMinusOneDivSq a u := by
  by_cases ha : a = 0
  · subst a
    simp [coshMinusOneDivSq]
    ring
  · have ht0 : t ≠ 0 := ne_of_gt ht
    have hat : a/t ≠ 0 := div_ne_zero ha ht0
    simp only [coshMinusOneDivSq, if_neg ha, if_neg hat]
    have harg : (a/t)*(t*u) = a*u := by
      field_simp [ht0]
    rw [harg]
    field_simp [ha,ht0]
    ring

theorem normalizedProjectivePhysicalProfile_scaled_plain
    {t u : ℝ} (ht : 0 < t) :
    normalizedProjectivePhysicalProfile t (t*u)
      =
    4 * quantitativeCanonicalTaper t u *
      twoRadiusBracket
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t) u := by
  have h :=
    normalizedProjectivePhysicalProfile_scaled_cosh
      (t:=t) (alpha:=0) (u:=u) ht
  simp only [zero_mul,Real.cosh_zero,mul_one] at h
  unfold reflectionPairWeight projTaper at h
  simpa [mul_assoc] using h

/--
Exact physical-coordinate scaling of the divided-square horizontal transform.
-/
theorem normalizedProjectiveHorizontalQuadratic_scaled_literal
    {t a delta : ℝ} (ht : 0 < t) :
    normalizedProjectiveHorizontalQuadratic
        t (a/t) (delta/t)
      =
    4*t^3 *
      ∫ u : ℝ,
        quantitativeCanonicalTaper t u *
          horizontalRadialWeight a delta u *
          twoRadiusBracket
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t) u := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  rw [normalizedProjectiveHorizontalQuadratic_eq_physicalCosine]
  let F : ℝ → ℝ := fun v =>
    normalizedProjectiveHorizontalPhysicalProfile t (a/t) v *
      Real.cos ((delta/t)*v)
  have hscale := Measure.integral_comp_mul_left F t
  have habs : |t⁻¹| = 1/t := by
    rw [abs_of_pos (inv_pos.mpr ht)]
    rfl
  have hpoint :
      (fun u : ℝ => F (t*u))
        =
      fun u : ℝ =>
        4*t^2 *
          (quantitativeCanonicalTaper t u *
            horizontalRadialWeight a delta u *
            twoRadiusBracket
              (quantitativeCanonicalTaper t)
              (quantitativeSampleRadius t) u) := by
    funext u
    dsimp [F]
    unfold normalizedProjectiveHorizontalPhysicalProfile
      horizontalRadialWeight
    rw [normalizedProjectivePhysicalProfile_scaled_plain ht,
      coshMinusOneDivSq_scale ht]
    have hcos : (delta/t)*(t*u)=delta*u := by
      field_simp [ht0]
    rw [hcos]
    ring
  have hscaled :
      (∫ u : ℝ,F (t*u))
        = (1/t) * ∫ v : ℝ,F v := by
    simpa [habs,smul_eq_mul] using hscale
  have hleft :
      (∫ u : ℝ,F (t*u))
        =
      4*t^2 *
        ∫ u : ℝ,
          quantitativeCanonicalTaper t u *
            horizontalRadialWeight a delta u *
            twoRadiusBracket
              (quantitativeCanonicalTaper t)
              (quantitativeSampleRadius t) u := by
    rw [hpoint,integral_const_mul]
  rw [hleft] at hscaled
  dsimp [F] at hscaled
  field_simp [ht0] at hscaled ⊢
  nlinarith

theorem canonical_horizontal_weight_projective_integral_neg
    {t a delta : ℝ}
    (ht : 18 ≤ t)
    (hdelta : |delta| ≤ t/9) :
    (∫ u : ℝ,
      quantitativeCanonicalTaper t u *
        horizontalRadialWeight a delta u *
        twoRadiusBracket
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t) u) < 0 := by
  have ht0 : 0 < t := by linarith
  let hd := quantitativeCanonicalGateData ht
  let Lambda : ℝ := 9*Real.pi/(4*t)
  have hLambda : 0 ≤ Lambda := by
    dsimp [Lambda]
    positivity
  have hphase : |delta|*Lambda ≤ Real.pi/4 := by
    dsimp [Lambda]
    have hm :=
      mul_le_mul_of_nonneg_right hdelta
        (show 0 ≤ 9*Real.pi/(4*t) by positivity)
    field_simp [ne_of_gt ht0] at hm ⊢
    nlinarith [Real.pi_pos]
  obtain ⟨u0,v0,hu0,hv0,huv⟩ := hd.twoPoint
  apply integral_weight_mul_twoRadiusBracket_neg
    hd.smooth.continuous hd.compactSupport hd.nonneg
    (horizontalRadialWeight_continuous a delta)
    hd.radiusPos hd.radial
  · intro u v hu hv huvle
    exact horizontalRadialWeight_mono_of_abs_le
      hLambda
      (hd.supportRadius u hu)
      (hd.supportRadius v hv)
      hphase huvle
  · exact hu0
  · exact hv0
  · exact huv
  · intro huvlt
    exact horizontalRadialWeight_strict_of_abs_lt
      hLambda
      (hd.supportRadius u0 (ne_of_gt hu0))
      (hd.supportRadius v0 (ne_of_gt hv0))
      hphase huvlt
  · intro hvult
    exact horizontalRadialWeight_strict_of_abs_lt
      hLambda
      (hd.supportRadius v0 (ne_of_gt hv0))
      (hd.supportRadius u0 (ne_of_gt hu0))
      hphase hvult

/--
The normalized Q surface is strictly negative throughout the canonical signed
band |delta| <= t/9.
-/
theorem normalizedProjectiveHorizontalQuadratic_neg_of_gap_le_ninth
    {t a delta : ℝ}
    (ht : 18 ≤ t)
    (hdelta : |delta| ≤ t/9) :
    normalizedProjectiveHorizontalQuadratic
        t (a/t) (delta/t) < 0 := by
  have ht0 : 0 < t := by linarith
  rw [normalizedProjectiveHorizontalQuadratic_scaled_literal ht0]
  have hI :=
    canonical_horizontal_weight_projective_integral_neg
      (t:=t) (a:=a) (delta:=delta) ht hdelta
  have hfactor : 0 < 4*t^3 := by positivity
  exact mul_neg_of_pos_of_neg hfactor hI

/--
Actual zero-source specialization.
-/
theorem normalizedProjectiveHorizontalSourceTerm_nonpos_of_gap_le_ninth
    {t : ℝ} (ht : 18 ≤ t)
    (sigma : Zeros)
    (hgap : |(sigma:ℂ).im-t| ≤ t/9) :
    normalizedProjectiveHorizontalSourceTerm t sigma ≤ 0 := by
  have ht0 : 0 < t := by linarith
  have hQ :
      normalizedProjectiveHorizontalQuadratic t
        (normalizedHorizontalHeight t sigma)
        (normalizedGap t sigma) < 0 := by
    unfold normalizedHorizontalHeight normalizedGap
    exact normalizedProjectiveHorizontalQuadratic_neg_of_gap_le_ninth
      (t:=t) (a:=heightOf sigma)
      (delta:=(sigma:ℂ).im-t) ht hgap
  unfold normalizedProjectiveHorizontalSourceTerm
  have hm : 0 ≤ ((zetaZeroConfig).mult (sigma:ℂ) : ℝ) := by positivity
  have hs : 0 ≤ (heightOf sigma)^2/t^2 := by positivity
  nlinarith [mul_nonneg hm hs]

/--
Every finite source window with cutoff J <= t/9 has nonpositive horizontal
sum, including the refined-middle subset.
-/
theorem refinedMiddle_sum_nonpos_of_cutoff_le_ninth
    {t : ℝ} (ht : 18 ≤ t)
    {J : ℕ} (hJ : (J:ℝ) ≤ t/9) :
    (∑ sigma ∈ normalizedProjectiveHorizontalRefinedMiddleFinsetAt t J,
      normalizedProjectiveHorizontalSourceTerm t (sigma:Zeros)) ≤ 0 := by
  classical
  apply Finset.sum_nonpos
  intro sigma hsigma
  have hmem :=
    (mem_normalizedProjectiveHorizontalRefinedMiddleFinsetAt
      (t:=t) (J:=J) sigma).mp hsigma
  have hgaplt : |((sigma:Zeros):ℂ).im-t| < J := hmem.1
  apply normalizedProjectiveHorizontalSourceTerm_nonpos_of_gap_le_ninth ht
  exact le_trans (le_of_lt hgaplt) hJ

end Synthesis
