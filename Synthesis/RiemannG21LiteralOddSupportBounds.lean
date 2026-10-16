import Mathlib.Tactic
import Synthesis.RiemannG21IntegratedOddRemainder
import Synthesis.RiemannG21SupportMomentDomination

/-!
# Literal G21 N3/N5 compact-support bounds

Specialize the generic compact-support moment theorem to the corrected literal
odd response

  base_y(u) = u * phi(u) * sinh(yu).

Then

  supportMoment0 = N1,
  supportMoment2 = N3,
  supportMoment4 = N5,

so on `0 <= u <= R`

  N3 <= R^2 N1,
  N5 <= R^4 N1.

These are exactly the support-moment leaves named by the Agda G21 quantitative
frontier.
-/

noncomputable section

open MeasureTheory Set

namespace Synthesis

private theorem oddHeightWeight_nonneg
    {w : ℝ → ℝ} {R y x : ℝ}
    (hy : 0 < y)
    (hw : ∀ t ∈ Icc (0:ℝ) R, 0 <= w t)
    (hx : x ∈ Icc (0:ℝ) R) :
    0 <= oddHeightWeight R w y x := by
  unfold oddHeightWeight
  have hwc : 0 <= g21ClippedWeight R w x := by
    simpa [g21ClippedWeight, hx] using hw x hx
  have hs : 0 <= Real.sinh (y*x) :=
    (Real.sinh_nonneg_iff).2 (mul_nonneg hy.le hx.1)
  positivity

/-- Literal N3/N5 support domination. -/
theorem literalOddSupportMomentBounds
    {w : ℝ → ℝ} {R y : ℝ}
    (hR : 0 <= R) (hy : 0 < y)
    (hw : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (h1 : Integrable (oddHeightWeight R w y) volume)
    (h3 : Integrable (fun x => x^2 * oddHeightWeight R w y x) volume)
    (h5 : Integrable (fun x => x^4 * oddHeightWeight R w y x) volume) :
    oddN3 R w y <= R^2 * oddN1 R w y ∧
    oddN5 R w y <= R^4 * oddN1 R w y := by
  have hbase : ∀ x ∈ Icc (0:ℝ) R, 0 <= oddHeightWeight R w y x :=
    fun x hx => oddHeightWeight_nonneg hy hw hx
  have h2int : IntervalIntegrable (fun x => x^2 * oddHeightWeight R w y x) volume 0 R :=
    h3.intervalIntegrable
  have h4int : IntervalIntegrable (fun x => x^4 * oddHeightWeight R w y x) volume 0 R :=
    h5.intervalIntegrable
  have h0int : IntervalIntegrable (oddHeightWeight R w y) volume 0 R :=
    h1.intervalIntegrable
  have hbounds := g21OddSupportMomentBounds hR hbase h0int h2int h4int
  have hzeroOutside : ∀ x, x ∉ Icc (0:ℝ) R -> oddHeightWeight R w y x = 0 := by
    intro x hx
    simp [oddHeightWeight, g21ClippedWeight, hx]
  have hN1eq : oddN1 R w y = supportMoment0 (oddHeightWeight R w y) R := by
    unfold oddN1 moment0 supportMoment0
    rw [← integral_indicator measurableSet_Icc]
    rw [intervalIntegral.integral_of_le hR]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Icc (0:ℝ) R
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_not_mem hx, hzeroOutside x hx]
  have hN3eq : oddN3 R w y = supportMoment2 (oddHeightWeight R w y) R := by
    unfold oddN3 momentQ supportMoment2
    rw [← integral_indicator measurableSet_Icc]
    rw [intervalIntegral.integral_of_le hR]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Icc (0:ℝ) R
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_not_mem hx, hzeroOutside x hx]
  have hN5eq : oddN5 R w y = supportMoment4 (oddHeightWeight R w y) R := by
    unfold oddN5 supportMoment4
    rw [← integral_indicator measurableSet_Icc]
    rw [intervalIntegral.integral_of_le hR]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Icc (0:ℝ) R
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_not_mem hx, hzeroOutside x hx]
  constructor
  · simpa [hN1eq, hN3eq] using hbounds.1
  · simpa [hN1eq, hN5eq] using hbounds.2

end Synthesis
