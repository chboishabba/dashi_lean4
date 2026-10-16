import Synthesis.RiemannImprovedZeroFreeHalfPlaneDonorAudit

/-!
# Quantitative G21 pole/off-line gap from the improved zero-free donor

For G21 the pole comparison height is `p = 1/2`, while the hypothetical
right-half off-line height is `a = |beta-1/2|`.  Once an exact same-zeta
attachment supplies the conservative donor cap

`a <= 187479/500000`,

we obtain the uniform separation

`p-a >= 62521/500000 = 0.125042 > 1/8`.

This is stronger information than the bare critical-strip fact `a < p`, which
allows the gap to approach zero.  It is therefore a useful quantitative input
for the live G21 Taylor/remainder and determinant-margin programme.  This file
still proves no hyperbolic TP2 theorem, actual parity minor, transversality, or
RH theorem.
-/

noncomputable section

namespace Synthesis

/-- Conservative uniform distance between the G21 pole height `1/2` and the
largest off-line height allowed by the safe donor cap. -/
def improvedZeroFreeUniformPoleGap : ℝ :=
  (1 : ℝ) / 2 - improvedZeroFreeSafeHorizontalCap

theorem improvedZeroFreeUniformPoleGap_eq :
    improvedZeroFreeUniformPoleGap = (62521 : ℝ) / 500000 := by
  rw [improvedZeroFreeSafeHorizontalCap_eq]
  norm_num [improvedZeroFreeUniformPoleGap]

/-- The donor creates a uniform gap slightly larger than `1/8`. -/
theorem oneEighth_lt_improvedZeroFreeUniformPoleGap :
    (1 : ℝ) / 8 < improvedZeroFreeUniformPoleGap := by
  rw [improvedZeroFreeUniformPoleGap_eq]
  norm_num

/-- Any attached off-line height beneath the safe donor cap stays uniformly
away from the pole height. -/
theorem improvedZeroFree_uniformPoleSeparation
    {a : ℝ}
    (ha : a ≤ improvedZeroFreeSafeHorizontalCap) :
    improvedZeroFreeUniformPoleGap ≤ (1 : ℝ) / 2 - a := by
  unfold improvedZeroFreeUniformPoleGap
  linarith

/-- A convenient weaker rational consequence: the actual pole/off-line gap is
strictly greater than `1/8`. -/
theorem oneEighth_lt_pole_sub_offLine_of_safeCap
    {a : ℝ}
    (ha : a ≤ improvedZeroFreeSafeHorizontalCap) :
    (1 : ℝ) / 8 < (1 : ℝ) / 2 - a := by
  exact oneEighth_lt_improvedZeroFreeUniformPoleGap.trans_le
    (improvedZeroFree_uniformPoleSeparation ha)

/-- Fail-closed current status for the G21 cross-pollination. -/
structure ImprovedZeroFreeG21GapAudit where
  uniformGapProvedFromSafeCap : Bool
  gapStrictlyExceedsOneEighth : Bool
  hyperbolicTP2Paid : Bool
  taylorRemainderPaid : Bool
  actualParityMinorPaid : Bool
  poleQuotientTransversalityPaid : Bool
  riemannHypothesisDerived : Bool

/-- The rational gap is paid; the substantive analytic consumers remain open. -/
def improvedZeroFreeG21GapAudit : ImprovedZeroFreeG21GapAudit where
  uniformGapProvedFromSafeCap := true
  gapStrictlyExceedsOneEighth := true
  hyperbolicTP2Paid := false
  taylorRemainderPaid := false
  actualParityMinorPaid := false
  poleQuotientTransversalityPaid := false
  riemannHypothesisDerived := false

end Synthesis
