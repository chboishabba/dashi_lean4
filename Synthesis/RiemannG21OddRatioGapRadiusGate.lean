import Mathlib
import Synthesis.RiemannImprovedZeroFreeG21TerminalMaxCut

/-!
# G21 odd ratio gap and explicit finite-radius existence

This owner pays two elementary ordered-field leaves that were still explicit in
`RiemannG21OddTaylorQuantitativeFrontierExact.agda`:

1. positive-mass cancellation from the strict cross-multiplied odd moment sign
   to the normalized gap `qp > qa`;
2. existence of a strictly positive sample radius satisfying the already-derived
   support-only gate

     `(510 R^4 + 100 R^6 + 4 R^8) r^2 < 900 (qp-qa)`.

No continuum TP2-to-moment theorem is smuggled in here: the strict cross product
and hence the positive ratio gap are producer inputs.  The point is that once
that genuinely analytic sign exists, *radius existence is automatic* and should
not remain a separate RH research obstruction.
-/

noncomputable section

namespace Synthesis

/-- Positive denominators turn the strict cross-multiplied odd moment sign into
the normalized ratio ordering used by the small-radius gate. -/
theorem oddRatioGap_of_crossProduct
    {n1A n3A n1P n3P : ℝ}
    (hA : 0 < n1A) (hP : 0 < n1P)
    (hcross : n3A * n1P < n1A * n3P) :
    n3A / n1A < n3P / n1P := by
  apply (div_lt_div_iff₀ hA hP).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcross

/-- Literal support-only polynomial already isolated by the Agda G21 audit. -/
def g21OddSupportPolynomial (R : ℝ) : ℝ :=
  510 * R^4 + 100 * R^6 + 4 * R^8

/-- The support-only coefficient is nonnegative for every real support radius. -/
theorem g21OddSupportPolynomial_nonneg (R : ℝ) :
    0 <= g21OddSupportPolynomial R := by
  unfold g21OddSupportPolynomial
  positivity

/-- Any positive normalized ratio gap admits a strictly positive finite radius
paying the support-only determinant gate.  This is an Archimedean/ordered-field
fact, not an additional analytic-number-theory hypothesis. -/
theorem exists_supportOnlyOddRadiusGate
    {R gap : ℝ} (hR : 0 <= R) (hgap : 0 < gap) :
    ∃ r : ℝ, 0 < r ∧
      g21OddSupportPolynomial R * r^2 < 900 * gap := by
  have htarget : 0 < (900 : ℝ) * gap := mul_pos (by norm_num) hgap
  obtain ⟨c, hcpos, hc⟩ := exists_pos_mul_lt htarget (g21OddSupportPolynomial R)
  let r : ℝ := min c 1
  have hrpos : 0 < r := by
    dsimp [r]
    exact lt_min hcpos zero_lt_one
  have hrle1 : r <= 1 := min_le_right _ _
  have hrlec : r <= c := min_le_left _ _
  have hrnonneg : 0 <= r := hrpos.le
  have hpoly : 0 <= g21OddSupportPolynomial R := g21OddSupportPolynomial_nonneg R
  have hrsq_le_r : r^2 <= r := by nlinarith
  have hrsq_le_c : r^2 <= c := hrsq_le_r.trans hrlec
  have hmul : g21OddSupportPolynomial R * r^2
      <= g21OddSupportPolynomial R * c :=
    mul_le_mul_of_nonneg_left hrsq_le_c hpoly
  exact ⟨r, hrpos, hmul.trans_lt hc⟩

/-- The same choice can be made inside the unit-radius regime required by the
existing fifth-order/Taylor budget. -/
theorem exists_unit_supportOnlyOddRadiusGate
    {R gap : ℝ} (hR : 0 <= R) (hgap : 0 < gap) :
    ∃ r : ℝ, 0 < r ∧ r <= 1 ∧
      g21OddSupportPolynomial R * r^2 < 900 * gap := by
  have htarget : 0 < (900 : ℝ) * gap := mul_pos (by norm_num) hgap
  obtain ⟨c, hcpos, hc⟩ := exists_pos_mul_lt htarget (g21OddSupportPolynomial R)
  let r : ℝ := min c 1
  have hrpos : 0 < r := by
    dsimp [r]
    exact lt_min hcpos zero_lt_one
  have hrle1 : r <= 1 := min_le_right _ _
  have hrlec : r <= c := min_le_left _ _
  have hrnonneg : 0 <= r := hrpos.le
  have hpoly : 0 <= g21OddSupportPolynomial R := g21OddSupportPolynomial_nonneg R
  have hrsq_le_r : r^2 <= r := by nlinarith
  have hrsq_le_c : r^2 <= c := hrsq_le_r.trans hrlec
  have hmul : g21OddSupportPolynomial R * r^2
      <= g21OddSupportPolynomial R * c :=
    mul_le_mul_of_nonneg_left hrsq_le_c hpoly
  exact ⟨r, hrpos, hrle1, hmul.trans_lt hc⟩

/-- End-to-end elementary compiler: a strict odd moment cross-product plus
positive N1 masses already implies existence of an admissible unit sample
radius.  The continuum moment sign remains the sole analytic input here. -/
theorem exists_unit_oddRadiusGate_of_crossProduct
    {R n1A n3A n1P n3P : ℝ}
    (hR : 0 <= R)
    (hA : 0 < n1A) (hP : 0 < n1P)
    (hcross : n3A * n1P < n1A * n3P) :
    ∃ r : ℝ, 0 < r ∧ r <= 1 ∧
      g21OddSupportPolynomial R * r^2
        < 900 * (n3P / n1P - n3A / n1A) := by
  have hratio : n3A / n1A < n3P / n1P :=
    oddRatioGap_of_crossProduct hA hP hcross
  exact exists_unit_supportOnlyOddRadiusGate hR (sub_pos.mpr hratio)

end Synthesis
