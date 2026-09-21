import Synthesis.RiemannProjectiveQuarticPhysicalRescale
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Short support of the physical quartic-escape detector

The normalized three-window witness uses centres 0, pi/3, pi/2 and a common
radius R<1.  Hence its support lies in

  |x| < pi/2 + R < pi/2 + 1.

After physical rescaling x=(t/16)u this becomes

  |u| < 16(pi/2+1)/t.

For t>=100 this is already strictly below log 2, so the literal prime side of
the Weil explicit formula vanishes exactly for the quartic detector as well.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

theorem quantitativeSymBump_support_abs_lt
    {c R u : ℝ} (hR : 0 < R)
    (hu : quantitativeSymBump c R u ≠ 0) :
    |u| < |c| + R := by
  unfold quantitativeSymBump
    Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize at hu
  by_cases hpos : scaledUnitBump c R u = 0
  · have hneg : scaledUnitBump c R (-u) ≠ 0 := by
      intro hz
      apply hu
      simp [hpos, hz]
    have hs := scaledUnitBump_support hR hneg
    have htri : |-u| ≤ |-u-c| + |c| := by
      have h := abs_add (-u-c) c
      simpa using h
    have habs : |-u| = |u| := by simp
    rw [habs] at htri
    linarith
  · have hs := scaledUnitBump_support hR hpos
    have htri : |u| ≤ |u-c| + |c| := by
      have h := abs_add (u-c) c
      simpa using h
    linarith

theorem quarticThreeWindowProfile_support_abs_lt
    {R lam u : ℝ} (hR : 0 < R)
    (hu : quarticThreeWindowProfile R lam u ≠ 0) :
    |u| < Real.pi/2 + R := by
  have hm : quarticWindowMass R ≠ 0 :=
    ne_of_gt (quarticWindowMass_pos hR)
  have hraw : quarticThreeWindowRaw R lam u ≠ 0 := by
    intro hz
    apply hu
    unfold quarticThreeWindowProfile
    rw [hz]
    ring
  have hone : |(1:ℝ)| = 1 := by norm_num
  by_contra hbad
  have hge : Real.pi/2 + R ≤ |u| := le_of_not_gt hbad
  have h0 :
      quantitativeSymBump 0 R u = 0 := by
    by_contra h
    have hs := quantitativeSymBump_support_abs_lt hR h
    simp only [abs_zero, zero_add] at hs
    have hpi : 0 < Real.pi/2 := by positivity
    linarith
  have h1 :
      quantitativeSymBump (Real.pi/3) R u = 0 := by
    by_contra h
    have hs := quantitativeSymBump_support_abs_lt hR h
    rw [abs_of_pos (by positivity : 0 < Real.pi/3)] at hs
    have hp := Real.pi_pos
    linarith
  have h2 :
      quantitativeSymBump (Real.pi/2) R u = 0 := by
    by_contra h
    have hs := quantitativeSymBump_support_abs_lt hR h
    rw [abs_of_pos (by positivity : 0 < Real.pi/2)] at hs
    linarith
  unfold quarticThreeWindowRaw at hraw
  rw [h0,h1,h2] at hraw
  simp at hraw

theorem quarticThreeWindowProfile_support_abs_lt_pi_half_add_one
    {R lam u : ℝ} (hR : 0 < R) (hRone : R < 1)
    (hu : quarticThreeWindowProfile R lam u ≠ 0) :
    |u| < Real.pi/2 + 1 := by
  have hs := quarticThreeWindowProfile_support_abs_lt hR hu
  linarith

theorem physicalQuarticProfile_support_abs_lt
    {R lam t u : ℝ}
    (hR : 0 < R) (hRone : R < 1)
    (ht : 0 < t)
    (hu :
      projectiveRescaleProfile
        (quarticThreeWindowProfile R lam) (t/16) u ≠ 0) :
    |u| < 16 * (Real.pi/2 + 1) / t := by
  have hr : 0 < t/16 := by positivity
  have hs :=
    quarticThreeWindowProfile_support_abs_lt_pi_half_add_one
      hR hRone hu
  unfold projectiveRescaleProfile at hs
  have habs : |(t/16)*u| = (t/16)*|u| := by
    rw [abs_mul, abs_of_pos hr]
  rw [habs] at hs
  rw [lt_div_iff₀ ht]
  nlinarith

theorem physicalQuarticProfile_short_of_hundred
    {R lam t : ℝ}
    (hR : 0 < R) (hRone : R < 1)
    (ht : 100 ≤ t) :
    ∀ u,
      projectiveRescaleProfile
        (quarticThreeWindowProfile R lam) (t/16) u ≠ 0 ->
      |u| < Real.log 2 := by
  intro u hu
  have htpos : 0 < t := by linarith
  have hs :=
    physicalQuarticProfile_support_abs_lt
      hR hRone htpos hu
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hbound :
      16 * (Real.pi/2 + 1) / t < (12/25 : ℝ) := by
    have hnum : 16 * (Real.pi/2 + 1) < 48 := by
      nlinarith
    have hden : 0 < t := htpos
    rw [div_lt_iff₀ hden]
    nlinarith
  have hlog : (12/25 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  exact hs.trans (hbound.trans hlog)

end Synthesis
