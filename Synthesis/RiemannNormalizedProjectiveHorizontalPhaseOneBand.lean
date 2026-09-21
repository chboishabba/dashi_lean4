import Synthesis.RiemannNormalizedProjectiveHorizontalSignedBandCutoff
import Synthesis.RiemannProjectiveHorizontalRadialMonotonicity

/-!
# Sharper horizontal signed band from the exact derivative inequality

The previous canonical signed band used the sufficient phase restriction

  |delta| * Lambda <= pi/4.

The actual derivative calculation only needs

  2 cos y - y sin y > 0.

Using sin y <= y and 1-y^2/2 <= cos y gives this directly for 0 <= y < 1.
Therefore the radial covariance argument remains valid on the strictly larger
phase window

  |delta| * Lambda < 1.

For the canonical support Lambda_t = 9*pi/(4*t), every source satisfying

  |delta| * 9*pi/(4*t) < 1

has nonpositive horizontal contribution.  This replaces the convenient t/9
band by the natural elementary derivative window, approximately
4t/(9*pi).

The final theorem plugs this stronger sign window into the arbitrary-cutoff
literal tsum reduction, so any natural cutoff J inside this phase window has no
finite middle budget at all.
-/

noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.FarShellCutoffTailBound

theorem two_cos_sub_y_sin_pos_of_lt_one
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    0 < 2 * Real.cos y - y * Real.sin y := by
  have hsin : Real.sin y ≤ y := Real.sin_le hy0
  have hcos : 1 - y^2 / 2 ≤ Real.cos y :=
    Real.one_sub_sq_div_two_le_cos y
  have hy2 : y^2 < 1 := by
    nlinarith [sq_nonneg y]
  have hysin : y * Real.sin y ≤ y^2 :=
    mul_le_mul_of_nonneg_left hsin hy0
  nlinarith

theorem horizontalRadialWeight_deriv_pos_of_phase_lt_one
    {alpha delta x : ℝ}
    (hx : 0 < x)
    (hdelta : 0 ≤ delta)
    (hphase : delta * x < 1) :
    0 < horizontalRadialWeightDeriv alpha delta x := by
  have hy0 : 0 ≤ delta * x := mul_nonneg hdelta hx.le
  have hphasePos :=
    two_cos_sub_y_sin_pos_of_lt_one hy0 hphase
  have hpi : 1 < Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  have hcos : 0 < Real.cos (delta * x) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_pos]
    · exact hphase.trans hpi
  have hHpos := coshMinusOneDivSq_pos alpha hx
  have hgrowth :=
    two_coshMinusOneDivSq_le_x_mul_deriv alpha hx.le
  have hgrowthCos :
      2 * coshMinusOneDivSq alpha x * Real.cos (delta*x)
        ≤
      x * coshMinusOneDivSqDeriv alpha x * Real.cos (delta*x) := by
    exact mul_le_mul_of_nonneg_right hgrowth hcos.le
  have hmargin :
      0 <
      coshMinusOneDivSq alpha x *
        (2 * Real.cos (delta*x)
          - (delta*x) * Real.sin (delta*x)) :=
    mul_pos hHpos hphasePos
  unfold horizontalRadialWeightDeriv
  nlinarith

theorem horizontalRadialWeight_strictMonoOn_nonneg_of_phase_lt_one
    {alpha delta Lambda : ℝ}
    (hdelta : 0 ≤ delta)
    (hLambda : 0 ≤ Lambda)
    (hphase : delta * Lambda < 1) :
    StrictMonoOn (horizontalRadialWeight alpha delta) (Set.Icc 0 Lambda) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 Lambda)
  · exact (horizontalRadialWeight_continuous alpha delta).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hdx : delta * x < 1 := by
      have hle : delta * x ≤ delta * Lambda :=
        mul_le_mul_of_nonneg_left hx.2.le hdelta
      exact hle.trans_lt hphase
    rw [(hasDerivAt_horizontalRadialWeight alpha delta x).deriv]
    exact horizontalRadialWeight_deriv_pos_of_phase_lt_one
      hx.1 hdelta hdx

theorem horizontalRadialWeight_strict_of_abs_lt_phase_one
    {alpha delta Lambda u v : ℝ}
    (hLambda : 0 ≤ Lambda)
    (hu : |u| ≤ Lambda)
    (hv : |v| ≤ Lambda)
    (hphase : |delta| * Lambda < 1)
    (huv : |u| < |v|) :
    horizontalRadialWeight alpha delta u
      < horizontalRadialWeight alpha delta v := by
  have hm :=
    horizontalRadialWeight_strictMonoOn_nonneg_of_phase_lt_one
      (alpha := alpha) (delta := |delta|) (Lambda := Lambda)
      (abs_nonneg delta) hLambda hphase
  have huI : |u| ∈ Set.Icc (0 : ℝ) Lambda :=
    ⟨abs_nonneg u, hu⟩
  have hvI : |v| ∈ Set.Icc (0 : ℝ) Lambda :=
    ⟨abs_nonneg v, hv⟩
  have h := hm huI hvI huv
  rw [horizontalRadialWeight_abs_delta,
      horizontalRadialWeight_abs_delta] at h
  have huabs :
      horizontalRadialWeight alpha delta u
        = horizontalRadialWeight alpha delta |u| := by
    by_cases hs : 0 ≤ u
    · simp [abs_of_nonneg hs]
    · rw [abs_of_neg (lt_of_not_ge hs)]
      simpa using (horizontalRadialWeight_even alpha delta u).symm
  have hvabs :
      horizontalRadialWeight alpha delta v
        = horizontalRadialWeight alpha delta |v| := by
    by_cases hs : 0 ≤ v
    · simp [abs_of_nonneg hs]
    · rw [abs_of_neg (lt_of_not_ge hs)]
      simpa using (horizontalRadialWeight_even alpha delta v).symm
  rw [huabs, hvabs]
  exact h

theorem horizontalRadialWeight_mono_of_abs_le_phase_one
    {alpha delta Lambda u v : ℝ}
    (hLambda : 0 ≤ Lambda)
    (hu : |u| ≤ Lambda)
    (hv : |v| ≤ Lambda)
    (hphase : |delta| * Lambda < 1)
    (huv : |u| ≤ |v|) :
    horizontalRadialWeight alpha delta u
      ≤ horizontalRadialWeight alpha delta v := by
  rcases lt_or_eq_of_le huv with hlt | heq
  · exact (horizontalRadialWeight_strict_of_abs_lt_phase_one
      hLambda hu hv hphase hlt).le
  · have huabs :
      horizontalRadialWeight alpha delta u
        = horizontalRadialWeight alpha delta |u| := by
      by_cases hs : 0 ≤ u
      · simp [abs_of_nonneg hs]
      · rw [abs_of_neg (lt_of_not_ge hs)]
        simpa using (horizontalRadialWeight_even alpha delta u).symm
    have hvabs :
      horizontalRadialWeight alpha delta v
        = horizontalRadialWeight alpha delta |v| := by
      by_cases hs : 0 ≤ v
      · simp [abs_of_nonneg hs]
      · rw [abs_of_neg (lt_of_not_ge hs)]
        simpa using (horizontalRadialWeight_even alpha delta v).symm
    rw [huabs, hvabs, heq]

theorem canonical_horizontal_weight_projective_integral_neg_of_phase_one
    {t a delta : ℝ}
    (ht : 18 ≤ t)
    (hphase :
      |delta| * (9 * Real.pi / (4 * t)) < 1) :
    (∫ u : ℝ,
      quantitativeCanonicalTaper t u *
        horizontalRadialWeight a delta u *
        twoRadiusBracket
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t) u) < 0 := by
  let hd := quantitativeCanonicalGateData ht
  let Lambda : ℝ := 9 * Real.pi / (4 * t)
  have hLambda : 0 ≤ Lambda := by
    dsimp [Lambda]
    positivity
  obtain ⟨u0, v0, hu0, hv0, huv⟩ := hd.twoPoint
  apply integral_weight_mul_twoRadiusBracket_neg
    hd.smooth.continuous hd.compactSupport hd.nonneg
    (horizontalRadialWeight_continuous a delta)
    hd.radiusPos hd.radial
  · intro u v hu hv huvle
    exact horizontalRadialWeight_mono_of_abs_le_phase_one
      hLambda
      (hd.supportRadius u hu)
      (hd.supportRadius v hv)
      hphase huvle
  · exact hu0
  · exact hv0
  · exact huv
  · intro huvlt
    exact horizontalRadialWeight_strict_of_abs_lt_phase_one
      hLambda
      (hd.supportRadius u0 (ne_of_gt hu0))
      (hd.supportRadius v0 (ne_of_gt hv0))
      hphase huvlt
  · intro hvult
    exact horizontalRadialWeight_strict_of_abs_lt_phase_one
      hLambda
      (hd.supportRadius v0 (ne_of_gt hv0))
      (hd.supportRadius u0 (ne_of_gt hu0))
      hphase hvult

theorem normalizedProjectiveHorizontalQuadratic_neg_of_phase_one
    {t a delta : ℝ}
    (ht : 18 ≤ t)
    (hphase :
      |delta| * (9 * Real.pi / (4 * t)) < 1) :
    normalizedProjectiveHorizontalQuadratic
        t (a / t) (delta / t) < 0 := by
  have ht0 : 0 < t := by linarith
  rw [normalizedProjectiveHorizontalQuadratic_scaled_literal ht0]
  have hI :=
    canonical_horizontal_weight_projective_integral_neg_of_phase_one
      (t := t) (a := a) (delta := delta) ht hphase
  have hfactor : 0 < 4 * t^3 := by positivity
  exact mul_neg_of_pos_of_neg hfactor hI

theorem normalizedProjectiveHorizontalSourceTerm_nonpos_of_phase_one
    {t : ℝ} (ht : 18 ≤ t)
    (sigma : Zeros)
    (hphase :
      |(sigma : ℂ).im - t| * (9 * Real.pi / (4 * t)) < 1) :
    normalizedProjectiveHorizontalSourceTerm t sigma ≤ 0 := by
  have hQ :
      normalizedProjectiveHorizontalQuadratic t
        (normalizedHorizontalHeight t sigma)
        (normalizedGap t sigma) < 0 := by
    unfold normalizedHorizontalHeight normalizedGap
    exact normalizedProjectiveHorizontalQuadratic_neg_of_phase_one
      (t := t) (a := heightOf sigma)
      (delta := (sigma : ℂ).im - t) ht hphase
  unfold normalizedProjectiveHorizontalSourceTerm
  have hm : 0 ≤ ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) := by positivity
  have hs : 0 ≤ (heightOf sigma)^2 / t^2 := by positivity
  nlinarith [mul_nonneg hm hs]

theorem refinedMiddle_sum_nonpos_of_cutoff_phase_one
    {t : ℝ} (ht : 18 ≤ t)
    {J : ℕ}
    (hJphase :
      (J : ℝ) * (9 * Real.pi / (4 * t)) < 1) :
    (∑ sigma ∈ normalizedProjectiveHorizontalRefinedMiddleFinsetAt t J,
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)) ≤ 0 := by
  classical
  apply Finset.sum_nonpos
  intro sigma hsigma
  have hmem :=
    (mem_normalizedProjectiveHorizontalRefinedMiddleFinsetAt_iff
      (t := t) (J := J) sigma).mp hsigma
  have hgaplt : |((sigma : Zeros) : ℂ).im - t| < (J : ℝ) := hmem.1
  apply normalizedProjectiveHorizontalSourceTerm_nonpos_of_phase_one ht
  have hLambda : 0 < 9 * Real.pi / (4 * t) := by positivity
  have hmul :=
    mul_lt_mul_of_pos_right hgaplt hLambda
  exact hmul.trans hJphase

/--
Sharpened arbitrary-cutoff compiler: any natural cutoff whose physical phase
stays below one has no finite horizontal middle budget.
-/
theorem exists_offOrdProjectiveHorizontal_le_farShell_of_cutoff_phase_one
    {t : ℝ} (ht : 18 ≤ t)
    {J : ℕ} (hJ : 1 ≤ J)
    (hJphase :
      (J : ℝ) * (9 * Real.pi / (4 * t)) < 1) :
    ∃ A K : ℝ, 1 ≤ A ∧ 0 ≤ K ∧
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
        ≤ K * farShellBound A |t| J := by
  obtain ⟨A, K, hA, hK, hcut, hlim⟩ :=
    exists_offOrdProjectiveHorizontal_cutoff_reduction ht
  have hraw := hcut J hJ
  have hmiddle :=
    refinedMiddle_sum_nonpos_of_cutoff_phase_one
      (t := t) ht (J := J) hJphase
  refine ⟨A, K, hA, hK, ?_⟩
  linarith

end Synthesis
