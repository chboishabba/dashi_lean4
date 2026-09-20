import Synthesis.RiemannNormalizedCanonicalFixedProfile

/-!
# Spectral gap of the normalized centered canonical profile

The normalized canonical two-window taper is supported away from v=0.

The inner window is centered at ±pi with normalized radius pi/4, hence any
nonzero inner-profile value satisfies

  3*pi/4 < |v|.

The outer window is centered at ±2*pi with the same radius, hence any nonzero
outer-profile value satisfies

  7*pi/4 < |v|.

Therefore the full normalized canonical profile, and hence its centered version,
has the exact zero-mode gap

  |v| <= 3*pi/4  ->  H_t(v)=0.

This is the geometric cancellation input for subtracting the smooth leading
zero density in the normalized aggregate: the test profile carries no Fourier
mass at or near v=0.
-/

noncomputable section

open scoped Real

namespace Synthesis

theorem normalizedInnerFixedProfile_support_gap
    {v : ℝ} (hv : normalizedInnerFixedProfile v ≠ 0) :
    3 * Real.pi / 4 < |v| := by
  rw [normalizedInnerFixedProfile_eq_symBump] at hv
  unfold quantitativeSymBump
    Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize at hv
  let R : ℝ := Real.pi / 4
  have hR : 0 < R := by dsimp [R]; positivity
  by_cases hp :
      scaledUnitBump Real.pi R v = 0
  · have hm : scaledUnitBump Real.pi R (-v) ≠ 0 := by
      intro hm
      apply hv
      simp [hp, hm]
    have hs := scaledUnitBump_support hR hm
    have hs' := (abs_lt.mp hs).1
    have hneg : v < 0 := by
      dsimp [R] at hs'
      nlinarith [Real.pi_pos]
    rw [abs_of_neg hneg]
    dsimp [R] at hs'
    nlinarith [Real.pi_pos]
  · have hs := scaledUnitBump_support hR hp
    have hs' := (abs_lt.mp hs).1
    have hpos : 0 < v := by
      dsimp [R] at hs'
      nlinarith [Real.pi_pos]
    rw [abs_of_pos hpos]
    dsimp [R] at hs'
    nlinarith [Real.pi_pos]

theorem normalizedOuterFixedProfile_support_gap
    {v : ℝ} (hv : normalizedOuterFixedProfile v ≠ 0) :
    7 * Real.pi / 4 < |v| := by
  rw [normalizedOuterFixedProfile_eq_symBump] at hv
  unfold quantitativeSymBump
    Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize at hv
  let R : ℝ := Real.pi / 4
  let c : ℝ := 2 * Real.pi
  have hR : 0 < R := by dsimp [R]; positivity
  by_cases hp :
      scaledUnitBump c R v = 0
  · have hm : scaledUnitBump c R (-v) ≠ 0 := by
      intro hm
      apply hv
      simp [hp, hm]
    have hs := scaledUnitBump_support hR hm
    have hs' := (abs_lt.mp hs).1
    have hneg : v < 0 := by
      dsimp [R, c] at hs'
      nlinarith [Real.pi_pos]
    rw [abs_of_neg hneg]
    dsimp [R, c] at hs'
    nlinarith [Real.pi_pos]
  · have hs := scaledUnitBump_support hR hp
    have hs' := (abs_lt.mp hs).1
    have hpos : 0 < v := by
      dsimp [R, c] at hs'
      nlinarith [Real.pi_pos]
    rw [abs_of_pos hpos]
    dsimp [R, c] at hs'
    nlinarith [Real.pi_pos]

theorem normalizedCanonicalFixedProfile_support_gap
    {t v : ℝ} (hv : normalizedCanonicalFixedProfile t v ≠ 0) :
    3 * Real.pi / 4 < |v| := by
  unfold normalizedCanonicalFixedProfile at hv
  by_cases hi : normalizedInnerFixedProfile v = 0
  · have ho : normalizedOuterFixedProfile v ≠ 0 := by
      intro ho
      apply hv
      simp [hi, ho]
    have houter := normalizedOuterFixedProfile_support_gap ho
    nlinarith [Real.pi_pos]
  · exact normalizedInnerFixedProfile_support_gap hi

theorem normalizedCenteredFixedProfile_support_gap
    {t v : ℝ} (hv : normalizedCenteredFixedProfile t v ≠ 0) :
    3 * Real.pi / 4 < |v| := by
  unfold normalizedCenteredFixedProfile at hv
  have hbase : normalizedCanonicalFixedProfile t v ≠ 0 := by
    intro h
    apply hv
    simp [h]
  exact normalizedCanonicalFixedProfile_support_gap hbase

theorem normalizedCenteredFixedProfile_zero_of_abs_le
    (t v : ℝ) (hv : |v| <= 3 * Real.pi / 4) :
    normalizedCenteredFixedProfile t v = 0 := by
  by_contra hne
  have hgap := normalizedCenteredFixedProfile_support_gap (t := t) hne
  linarith

theorem normalizedCenteredFixedProfile_zero (t : ℝ) :
    normalizedCenteredFixedProfile t 0 = 0 := by
  apply normalizedCenteredFixedProfile_zero_of_abs_le
  simp only [abs_zero]
  positivity

end Synthesis
