import Zeta23Bridge.LiteralWeilEvenChannelTaper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Pole-window de-weighting

The positive taper construction cancels the modulated pole response at the
selected sample radius r=t/16 by combining:

* an outer positive pole window near tu=2*pi;
* an inner negative pole window near tu=pi.

The extra factor cos(r u) is strictly smaller on the outer window.  Therefore a
weighted cancellation can leave a positive unweighted residue.

This file isolates the algebraic and trigonometric mechanism.  It does not yet
re-open the local bump construction to discharge its integral hypotheses.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

/--
Abstract de-weighting lemma.

A1 is the positive unweighted mass, A2 the negative unweighted mass.
P1,P2 are the corresponding weighted masses.  If the positive window is
weighted by at most cOuter while the magnitude of the negative window is
weighted by at least cInner, with cOuter<cInner, then exact weighted cancellation
forces a positive unweighted residue.
-/
theorem positive_unweighted_of_separated_weighted_cancellation
    {A1 A2 P1 P2 lam cOuter cInner : ℝ}
    (hA1 : 0 < A1)
    (hA2 : A2 < 0)
    (hP1 : 0 < P1)
    (hP2 : P2 < 0)
    (hcOuter : 0 < cOuter)
    (hsep : cOuter < cInner)
    (hP1upper : P1 ≤ cOuter * A1)
    (hP2lower : cInner * (-A2) ≤ -P2)
    (hlam : lam = -P2 / P1) :
    0 < A2 + lam * A1 := by
  have hP1pos : 0 < cOuter * A1 := lt_of_lt_of_le hP1 hP1upper
  have hcInner : 0 < cInner := lt_trans hcOuter hsep
  have hratio :
      (-P2 / P1) * A1 > -A2 := by
    have hnegA2 : 0 < -A2 := by linarith
    have hleft :
        cInner * (-A2) / (cOuter * A1)
          < (-P2) / P1 := by
      have hP1le : P1 ≤ cOuter * A1 := hP1upper
      have hnum : cInner * (-A2) ≤ -P2 := hP2lower
      have hdenpos : 0 < cOuter * A1 := hP1pos
      have hP1pos' : 0 < P1 := hP1
      have hstep1 :
          cInner * (-A2) / (cOuter * A1)
            < cInner * (-A2) / P1 := by
        exact (div_lt_div_iff₀ hdenpos hP1pos').2 (by
          have hp : 0 < cInner * (-A2) := mul_pos hcInner hnegA2
          nlinarith)
      have hstep2 :
          cInner * (-A2) / P1 ≤ (-P2) / P1 :=
        (div_le_div_iff_of_pos_right hP1).2 hnum
      exact lt_of_lt_of_le hstep1 hstep2
    have hfactor :
        (-A2) / A1
          < cInner * (-A2) / (cOuter * A1) := by
      have hden : 0 < A1 := hA1
      field_simp [ne_of_gt hA1, ne_of_gt hcOuter] at *
      nlinarith [mul_pos hcOuter hA1, mul_pos hcInner hA1]
    have hmain : (-A2) / A1 < (-P2) / P1 :=
      lt_trans hfactor hleft
    have hA1pos := hA1
    exact (div_lt_iff₀ hA1pos).mp (by
      have := (lt_div_iff₀ hP1).mp ?_
      · nlinarith
      · exact (div_lt_iff₀ hA1pos).2 (by nlinarith))
  rw [hlam]
  linarith

/-- The two sample-window cosine constants. -/
def outerCosUpper : ℝ := Real.cos (7 * Real.pi / 64)
def innerCosLower : ℝ := Real.cos (5 * Real.pi / 64)

theorem outer_angle_lt_inner_pi :
    (0 : ℝ) ≤ 5 * Real.pi / 64
      ∧ 5 * Real.pi / 64 < 7 * Real.pi / 64
      ∧ 7 * Real.pi / 64 ≤ Real.pi := by
  have hp := Real.pi_pos
  constructor
  · positivity
  constructor <;> nlinarith

theorem outerCosUpper_lt_innerCosLower :
    outerCosUpper < innerCosLower := by
  unfold outerCosUpper innerCosLower
  obtain ⟨h0,h57,h7pi⟩ := outer_angle_lt_inner_pi
  exact Real.strictAntiOn_cos h0 h7pi h57

theorem outerCosUpper_pos : 0 < outerCosUpper := by
  unfold outerCosUpper
  apply Real.cos_pos_of_mem_Ioo
  have hp := Real.pi_pos
  constructor <;> nlinarith

/-- On the outer positive window the sample cosine is at most outerCosUpper. -/
theorem sampleCos_le_outerCosUpper
    {t u : ℝ} (ht : 0 < t)
    (huLow : 7 * Real.pi / (4 * t) < u)
    (huHigh : u < 9 * Real.pi / (4 * t)) :
    Real.cos ((t / 16) * u) ≤ outerCosUpper := by
  unfold outerCosUpper
  have hp := Real.pi_pos
  have hxLow : 7 * Real.pi / 64 < (t / 16) * u := by
    have := mul_lt_mul_of_pos_left huLow (show 0 < t / 16 by positivity)
    nlinarith
  have hxHigh : (t / 16) * u < 9 * Real.pi / 64 := by
    have := mul_lt_mul_of_pos_left huHigh (show 0 < t / 16 by positivity)
    nlinarith
  have hx0 : 0 ≤ 7 * Real.pi / 64 := by positivity
  have hxpi : (t / 16) * u ≤ Real.pi := by nlinarith
  exact Real.cos_le_cos_of_nonneg_of_le_pi hx0 hxpi hxLow.le

/-- On the inner negative window the sample cosine is at least innerCosLower. -/
theorem innerCosLower_le_sampleCos
    {t u : ℝ} (ht : 0 < t)
    (huLow : 3 * Real.pi / (4 * t) < u)
    (huHigh : u < 5 * Real.pi / (4 * t)) :
    innerCosLower ≤ Real.cos ((t / 16) * u) := by
  unfold innerCosLower
  have hp := Real.pi_pos
  have hxLow : 3 * Real.pi / 64 < (t / 16) * u := by
    have := mul_lt_mul_of_pos_left huLow (show 0 < t / 16 by positivity)
    nlinarith
  have hxHigh : (t / 16) * u < 5 * Real.pi / 64 := by
    have := mul_lt_mul_of_pos_left huHigh (show 0 < t / 16 by positivity)
    nlinarith
  have hx0 : 0 ≤ (t / 16) * u := by linarith
  have h5pi : 5 * Real.pi / 64 ≤ Real.pi := by nlinarith
  exact Real.cos_le_cos_of_nonneg_of_le_pi hx0 h5pi hxHigh.le

end Synthesis
