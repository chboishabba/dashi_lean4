import Synthesis.RiemannGammaToPoleRatioMonotonicity

/-!
# Explicit canonical Gamma/pole ratio gap

The inner positive-coordinate bump lies in

    3*pi/(4t) < u < 5*pi/(4t),

while its matched outer point u+pi/t lies in

    7*pi/(4t) < u+pi/t < 9*pi/(4t).

Since gammaToPoleRatio is strictly increasing across the whole canonical
positive support, the endpoint difference

    d(t) =
      R_t(7*pi/(4t)) - R_t(5*pi/(4t))

is strictly positive and is a uniform lower bound for every matched-coordinate
ratio gap.
-/

noncomputable section

open scoped Real

namespace Synthesis

def canonicalGammaRatioGap (t : ℝ) : ℝ :=
  gammaToPoleRatio t (7 * Real.pi / (4*t))
    - gammaToPoleRatio t (5 * Real.pi / (4*t))

theorem canonicalGammaRatioGap_pos {t : ℝ} (ht : 18 <= t) :
    0 < canonicalGammaRatioGap t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  unfold canonicalGammaRatioGap
  have h5 : 0 < 5 * Real.pi / (4*t) := by positivity
  have h57 : 5 * Real.pi / (4*t) < 7 * Real.pi / (4*t) := by
    have hp := Real.pi_pos
    positivity
  have h7can : 7 * Real.pi / (4*t) <= 9 * Real.pi / (4*t) := by
    have hp := Real.pi_pos
    positivity
  exact sub_pos.mpr
    (gammaToPoleRatio_strictMonoOn_canonical ht h5 h57 h7can)

theorem canonicalGammaRatioGap_nonneg {t : ℝ} (ht : 18 <= t) :
    0 <= canonicalGammaRatioGap t :=
  (canonicalGammaRatioGap_pos ht).le

theorem inner_ratio_le_five_endpoint
    {t u : ℝ} (ht : 18 <= t)
    (huLower : 3 * Real.pi/(4*t) <= u)
    (huUpper : u <= 5 * Real.pi/(4*t)) :
    gammaToPoleRatio t u
      <= gammaToPoleRatio t (5 * Real.pi/(4*t)) := by
  by_cases hEq : u = 5 * Real.pi/(4*t)
  · simp [hEq]
  · have hu0 : 0 < u := by
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
      exact lt_of_lt_of_le (by positivity) huLower
    have hlt : u < 5 * Real.pi/(4*t) := lt_of_le_of_ne huUpper hEq
    exact (gammaToPoleRatio_strictMonoOn_canonical
      ht hu0 hlt (by
        have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
        have hp := Real.pi_pos
        positivity)).le

theorem seven_endpoint_le_outer_ratio
    {t v : ℝ} (ht : 18 <= t)
    (hvLower : 7 * Real.pi/(4*t) <= v)
    (hvUpper : v <= 9 * Real.pi/(4*t)) :
    gammaToPoleRatio t (7 * Real.pi/(4*t))
      <= gammaToPoleRatio t v := by
  by_cases hEq : 7 * Real.pi/(4*t) = v
  · simp [hEq]
  · have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    have h70 : 0 < 7 * Real.pi/(4*t) := by positivity
    have hlt : 7 * Real.pi/(4*t) < v := lt_of_le_of_ne hvLower hEq
    exact (gammaToPoleRatio_strictMonoOn_canonical ht h70 hlt hvUpper).le

theorem canonicalGammaRatioGap_le_matched_gap
    {t u : ℝ} (ht : 18 <= t)
    (huLower : 3 * Real.pi/(4*t) <= u)
    (huUpper : u <= 5 * Real.pi/(4*t)) :
    canonicalGammaRatioGap t
      <= gammaToPoleRatio t (u + Real.pi/t)
        - gammaToPoleRatio t u := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hin :=
    inner_ratio_le_five_endpoint ht huLower huUpper
  have houtLower :
      7 * Real.pi/(4*t) <= u + Real.pi/t := by
    have h := huLower
    field_simp [ne_of_gt ht0] at h ⊢
    nlinarith [Real.pi_pos]
  have houtUpper :
      u + Real.pi/t <= 9 * Real.pi/(4*t) := by
    have h := huUpper
    field_simp [ne_of_gt ht0] at h ⊢
    nlinarith [Real.pi_pos]
  have hout := seven_endpoint_le_outer_ratio ht houtLower houtUpper
  unfold canonicalGammaRatioGap
  linarith

end Synthesis
