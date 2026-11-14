import Mathlib

/-!
RH A2/G3 negative controls for the 14 November attachment.
This is NOT the original selected FarExact nor the repository's
signedFifthCorrelationGapAt. The latter is finite physical cap plus
outer budget minus 3*eps; this module audits only an offered surrogate.
SOURCE-WRITTEN; pinned Lean kernel check pending.
-/

namespace Synthesis

/-- Real part of the inverse square pole; no selected zero is asserted. -/
def rationalPoleCurvature (a b : ℚ) : ℚ :=
  (a^2-b^2)/(a^2+b^2)^2

/-- |vertical| = 1/2 < 1, yet the displayed local pole curvature is
negative, contrary to the attachment's positive floor. -/
theorem localPoleInsideUnitWindow_negative :
    rationalPoleCurvature (1/4) (1/2) = -(48/25 : ℚ) := by
  norm_num [rationalPoleCurvature]

theorem realPoleCurvature_negative_of_horizontal_sq_lt_vertical_sq
    {a b : ℝ} (h : a^2 < b^2) :
    (a^2-b^2)/(a^2+b^2)^2 < 0 := by
  have hnum : a^2-b^2 < 0 := sub_neg.mpr h
  have hb : 0 < b^2 := lt_of_le_of_lt (sq_nonneg a) h
  have hden : 0 < (a^2+b^2)^2 := by positivity
  exact div_neg_of_neg_of_pos hnum hden

/-- Artificial two-mode signed heat expression, NOT the original
Lean Route-B physical signed cap. Positive a,b represent heat weights.
The reference mean carries NO Mobius signs; the numerator has (+,-). -/
def twoModeSignedHeatFifth (x y a b : ℝ) : ℝ :=
  let m := (a*x^2+b*y^2)/(a+b)
  a*(x^5-m*x^3) - b*(y^5-m*y^3)

/-- Exact finite identity: the offered positive-leading-pair argument
has its sign reversed for Mobius signs (+1,-1). -/
theorem twoModeSignedHeatFifth_eq
    (x y a b : ℝ) (hden : a+b ≠ 0) :
    twoModeSignedHeatFifth x y a b =
      -(a*b/(a+b))*(y^2-x^2)*(x^3+y^3) := by
  unfold twoModeSignedHeatFifth
  dsimp
  field_simp [hden]
  ring

theorem twoModeSignedHeatFifth_strictly_negative
    {x y a b : ℝ} (hx : 0 ≤ x) (hxy : x < y)
    (ha : 0 < a) (hb : 0 < b) :
    twoModeSignedHeatFifth x y a b < 0 := by
  have hdenpos : 0 < a+b := add_pos ha hb
  rw [twoModeSignedHeatFifth_eq x y a b (ne_of_gt hdenpos)]
  have hy : 0 < y := lt_of_le_of_lt hx hxy
  have hsum : 0 < x+y := by linarith
  have hsq : 0 < y^2-x^2 := by
    nlinarith [mul_pos (sub_pos.mpr hxy) hsum]
  have hcub : 0 < x^3+y^3 := by positivity
  have hcoef : 0 < a*b/(a+b) := div_pos (mul_pos ha hb) hdenpos
  have hprod : 0 < (a*b/(a+b))*(y^2-x^2)*(x^3+y^3) :=
    mul_pos (mul_pos hcoef hsq) hcub
  linarith

end Synthesis
