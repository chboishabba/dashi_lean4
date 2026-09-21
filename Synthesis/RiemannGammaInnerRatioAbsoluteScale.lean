import Synthesis.RiemannGammaInnerPoleAbsoluteScale
import Synthesis.RiemannGammaMatchedQuantitativeGain

/-!
# Absolute linear scale of the canonical Gamma-to-pole ratio

On the canonical positive inner window

  3*pi/(4t) <= u <= 5*pi/(4t),

the normalized phase theta=(t/16)u lies in

  3*pi/64 <= theta <= 5*pi/64.

Define the fixed positive phase floor

  A_* = 1 - cos(3*pi/64).

Since cos(theta)>0 and cos(theta)<=1,

  A_* <= (1-cos theta)/cos theta.

For the hyperbolic denominator

  H(u)=2 sinh(u) cosh(u/2),

the already-owned estimates give

  sinh(u) <= u cosh(u)

and, because u<=pi/8,

  cosh(u) cosh(u/2) <= 69/59.

Hence

  H(u) <= (345*pi/118)/t.

Therefore, with

  c_R = A_* / (345*pi/118) > 0,

one has uniformly on the inner window

  c_R * t <= gammaToPoleRatio t u.

Combined with the matched relative gain, this gives an absolute matched gap
of order t.
-/

noncomputable section

open scoped Real

namespace Synthesis

def canonicalInnerPhaseFloor : ℝ :=
  1 - Real.cos (3 * Real.pi / 64)

def canonicalInnerHyperbolicCeiling : ℝ :=
  345 * Real.pi / 118

def canonicalInnerRatioLinearConstant : ℝ :=
  canonicalInnerPhaseFloor / canonicalInnerHyperbolicCeiling

theorem canonicalInnerPhaseFloor_pos :
    0 < canonicalInnerPhaseFloor := by
  have htheta : 0 < 3 * Real.pi / 64 := by positivity
  have hlt :
      Real.cos (3 * Real.pi / 64) < Real.cos 0 := by
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      (by norm_num)
      (by nlinarith [Real.pi_pos])
      htheta
  simp only [Real.cos_zero] at hlt
  unfold canonicalInnerPhaseFloor
  linarith

theorem canonicalInnerHyperbolicCeiling_pos :
    0 < canonicalInnerHyperbolicCeiling := by
  unfold canonicalInnerHyperbolicCeiling
  positivity

theorem canonicalInnerRatioLinearConstant_pos :
    0 < canonicalInnerRatioLinearConstant := by
  unfold canonicalInnerRatioLinearConstant
  exact div_pos canonicalInnerPhaseFloor_pos
    canonicalInnerHyperbolicCeiling_pos

theorem canonicalInnerPhaseFloor_le_phaseRatio
    {t u : ℝ}
    (ht : 18 <= t)
    (huLower : 3 * Real.pi/(4*t) <= u)
    (huUpper : u <= 5 * Real.pi/(4*t)) :
    canonicalInnerPhaseFloor
      <= centeredPolePhaseRatio ((t/16)*u) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  obtain ⟨hlo, hhi⟩ :=
    paired_inner_phase_bounds ht0 huLower huUpper
  have htheta0 : 0 < (t/16)*u := by
    nlinarith [Real.pi_pos]
  have hthetaPi : (t/16)*u < Real.pi/2 := by
    nlinarith [Real.pi_pos]
  have hc : 0 < Real.cos ((t/16)*u) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hcosle1 : Real.cos ((t/16)*u) <= 1 :=
    Real.cos_le_one _
  have hcosorder :
      Real.cos ((t/16)*u)
        <= Real.cos (3 * Real.pi/64) := by
    exact Real.cos_le_cos_of_nonneg_of_le_pi
      (by positivity)
      (by nlinarith [Real.pi_pos])
      hlo
  have hnum :
      canonicalInnerPhaseFloor
        <= 1 - Real.cos ((t/16)*u) := by
    unfold canonicalInnerPhaseFloor
    linarith
  unfold centeredPolePhaseRatio
  rw [le_div_iff₀ hc]
  have hfloor0 : 0 <= canonicalInnerPhaseFloor :=
    canonicalInnerPhaseFloor_pos.le
  have hmul :
      canonicalInnerPhaseFloor * Real.cos ((t/16)*u)
        <= canonicalInnerPhaseFloor := by
    exact mul_le_of_le_one_right hfloor0 hcosle1
  exact le_trans hmul hnum

theorem gammaPoleHyperbolicDenom_inner_le_div_t
    {t u : ℝ}
    (ht : 18 <= t)
    (huLower : 3 * Real.pi/(4*t) <= u)
    (huUpper : u <= 5 * Real.pi/(4*t)) :
    gammaPoleHyperbolicDenom u
      <= canonicalInnerHyperbolicCeiling / t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) huLower
  have huPi : u <= Real.pi/8 := by
    have h5 : 5 * Real.pi/(4*t) <= Real.pi/8 := by
      rw [div_le_iff₀ ht0]
      nlinarith [Real.pi_pos]
    exact le_trans huUpper h5
  have hsinh :
      Real.sinh u <= u * Real.cosh u :=
    sinh_le_mul_cosh_of_nonneg hu0.le
  have hcosh :
      Real.cosh u * Real.cosh (u/2) <= 69/59 :=
    cosh_mul_cosh_half_le_sixtynine_fiftynine hu0.le huPi
  have h1 :
      gammaPoleHyperbolicDenom u
        <= 2 * u * (69/59 : ℝ) := by
    unfold gammaPoleHyperbolicDenom
    have hch0 : 0 <= Real.cosh (u/2) :=
      (Real.cosh_pos _).le
    have hstep :
        2 * Real.sinh u * Real.cosh (u/2)
          <= 2 * (u * Real.cosh u) * Real.cosh (u/2) := by
      gcongr
    have hstep2 :
        2 * (u * Real.cosh u) * Real.cosh (u/2)
          <= 2 * u * (69/59 : ℝ) := by
      have huNonneg : 0 <= 2*u := by positivity
      nlinarith
    exact le_trans hstep hstep2
  have h2 :
      2 * u * (69/59 : ℝ)
        <= canonicalInnerHyperbolicCeiling / t := by
    unfold canonicalInnerHyperbolicCeiling
    have h := mul_le_mul_of_nonneg_right huUpper
      (show (0:ℝ) <= 2*(69/59 : ℝ) by norm_num)
    field_simp [ne_of_gt ht0] at h ⊢
    nlinarith [Real.pi_pos]
  exact le_trans h1 h2

theorem gammaToPoleRatio_linear_lower_on_inner
    {t u : ℝ}
    (ht : 18 <= t)
    (huLower : 3 * Real.pi/(4*t) <= u)
    (huUpper : u <= 5 * Real.pi/(4*t)) :
    canonicalInnerRatioLinearConstant * t
      <= gammaToPoleRatio t u := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) huLower
  obtain ⟨hlo, hhi⟩ :=
    paired_inner_phase_bounds ht0 huLower huUpper
  have hangle0 : 0 <= (t/16)*u := by
    nlinarith [Real.pi_pos]
  have hanglePi : (t/16)*u < Real.pi/2 := by
    nlinarith [Real.pi_pos]
  have hphase :=
    canonicalInnerPhaseFloor_le_phaseRatio
      ht huLower huUpper
  have hH :=
    gammaPoleHyperbolicDenom_inner_le_div_t
      ht huLower huUpper
  have hHpos : 0 < gammaPoleHyperbolicDenom u :=
    gammaPoleHyperbolicDenom_pos hu0
  rw [gammaToPoleRatio_eq_phase_div_hyperbolic
    hu0 hangle0 hanglePi]
  rw [le_div_iff₀ hHpos]
  have hcpos : 0 < canonicalInnerRatioLinearConstant :=
    canonicalInnerRatioLinearConstant_pos
  have hmulH :
      canonicalInnerRatioLinearConstant * t
          * gammaPoleHyperbolicDenom u
        <=
      canonicalInnerRatioLinearConstant * t
          * (canonicalInnerHyperbolicCeiling / t) := by
    exact mul_le_mul_of_nonneg_left hH
      (mul_nonneg hcpos.le ht0.le)
  have hcollapse :
      canonicalInnerRatioLinearConstant * t
          * (canonicalInnerHyperbolicCeiling / t)
        =
      canonicalInnerPhaseFloor := by
    unfold canonicalInnerRatioLinearConstant
    field_simp [ne_of_gt ht0,
      ne_of_gt canonicalInnerHyperbolicCeiling_pos]
  rw [hcollapse] at hmulH
  exact le_trans hmulH hphase

theorem matched_gammaToPoleRatio_absolute_gap
    {t u : ℝ}
    (ht : 18 <= t)
    (huLower : 3 * Real.pi/(4*t) <= u)
    (huUpper : u <= 5 * Real.pi/(4*t)) :
    (2603/16100 : ℝ)
        * canonicalInnerRatioLinearConstant * t
      <
    gammaToPoleRatio t (u + Real.pi/t)
      - gammaToPoleRatio t u := by
  have hrel :=
    matched_gammaToPoleRatio_quantitative_gain
      ht huLower huUpper
  have hbase :=
    gammaToPoleRatio_linear_lower_on_inner
      ht huLower huUpper
  have hk : 0 < (2603/16100 : ℝ) := by norm_num
  have hscaled :=
    mul_le_mul_of_nonneg_left hbase hk.le
  exact lt_of_le_of_lt hscaled hrel

end Synthesis
