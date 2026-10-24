import Mathlib.Tactic
import Synthesis.RiemannG21OddFiniteMinorClosure
import Synthesis.RiemannG21IntegratedOddRemainder
import Synthesis.RiemannG21LiteralOddSupportBounds
import Synthesis.RiemannG21OddContinuumToRadius

/-!
# Literal G21 finite odd parity minor exists

This is the end-to-end odd-sector P1->P2 compiler on the current G21 carrier.
Assume the positive-half taper is nonnegative, has a nontrivial positive
plateau, and the literal N1/N3/N5 integrands are integrable at heights
`0<a<p`.  Then there exists a finite sample radius `0<r<=1` for which the
actual six-scaled odd determinant (cubic response plus the integrated sine
remainder) is strictly negative.

No abstract determinant-error variable remains: the four remainders are the
literal `oddSixScaledRemainder` integrals.  The proof chain is

  TP2 + positive plateau
    -> Delta_odd > 0
    -> normalized ratio gap > 0
    -> support-only small radius exists
    -> N3/N5 support domination
    -> fifth-order integrated remainder
    -> six-term determinant bound
    -> actual finite odd minor < 0.

The remaining same-object debt is attaching the companion Zeta23 taper and
kernel-checking this source, not discovering another odd-sector inequality.
-/

noncomputable section

open MeasureTheory Set

namespace Synthesis

/-- Literal actual odd determinant built from N1/N3 and integrated remainders. -/
def literalOddFiniteDeterminant
    (R : ℝ) (w : ℝ → ℝ) (a p r : ℝ) : ℝ :=
  oddActualDeterminant r
    (oddN1 R w a) (oddN3 R w a)
    (oddN1 R w p) (oddN3 R w p)
    (oddSixScaledRemainder R w a r)
    (oddSixScaledRemainder R w a (2*r))
    (oddSixScaledRemainder R w p r)
    (oddSixScaledRemainder R w p (2*r))

private theorem oddHeightWeight_nonneg_all
    {w : ℝ → ℝ} {R y x : ℝ}
    (hy : 0 < y)
    (hw : ∀ t ∈ Icc (0:ℝ) R, 0 <= w t) :
    0 <= oddHeightWeight R w y x := by
  by_cases hx : x ∈ Icc (0:ℝ) R
  · unfold oddHeightWeight
    have hwc : 0 <= g21ClippedWeight R w x := by
      simpa [g21ClippedWeight, hx] using hw x hx
    have hs : 0 <= Real.sinh (y*x) :=
      (Real.sinh_nonneg_iff).2 (mul_nonneg hy.le hx.1)
    positivity
  · simp [oddHeightWeight, g21ClippedWeight, hx]

private theorem oddN3_nonneg
    {w : ℝ → ℝ} {R y : ℝ}
    (hy : 0 < y)
    (hw : ∀ t ∈ Icc (0:ℝ) R, 0 <= w t) :
    0 <= oddN3 R w y := by
  unfold oddN3 momentQ
  apply integral_nonneg_of_ae
  filter_upwards with x
  exact mul_nonneg (sq_nonneg x) (oddHeightWeight_nonneg_all hy hw)

private theorem oddN5_nonneg
    {w : ℝ → ℝ} {R y : ℝ}
    (hy : 0 < y)
    (hw : ∀ t ∈ Icc (0:ℝ) R, 0 <= w t) :
    0 <= oddN5 R w y := by
  unfold oddN5
  apply integral_nonneg_of_ae
  filter_upwards with x
  exact mul_nonneg (by positivity) (oddHeightWeight_nonneg_all hy hw)

/-- End-to-end existence of a strict literal odd parity minor. -/
theorem exists_literalOddFiniteDeterminant_neg_of_positivePlateau
    {w : ℝ → ℝ} {a p R l m r0 : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hl : 0 < l) (hlm : l < m) (hmr : m < r0) (hrR : r0 < R)
    (hwNonneg : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (hwPos : ∀ x ∈ Ioo l r0, 0 < w x)
    (h1a : Integrable (oddHeightWeight R w a) volume)
    (h3a : Integrable (fun x => x^2 * oddHeightWeight R w a x) volume)
    (h5a : Integrable (fun x => x^4 * oddHeightWeight R w a x) volume)
    (h1p : Integrable (oddHeightWeight R w p) volume)
    (h3p : Integrable (fun x => x^2 * oddHeightWeight R w p x) volume)
    (h5p : Integrable (fun x => x^4 * oddHeightWeight R w p x) volume) :
    ∃ r : ℝ, 0 < r ∧ r <= 1 ∧ literalOddFiniteDeterminant R w a p r < 0 := by
  have hp : 0 < p := ha.trans hap
  have hR : 0 <= R := by
    have : 0 < R := hl.trans (hlm.trans (hmr.trans hrR))
    exact this.le
  obtain ⟨r, hr, hr1, hgate⟩ :=
    exists_unit_oddRadiusGate_of_positivePlateau
      ha hap hl hlm hmr hrR hwNonneg hwPos h1a h1p h3a h3p
  have hN1a : 0 < oddN1 R w a :=
    oddN1_pos_of_positivePlateau ha hl (hlm.trans hmr) hrR hwNonneg hwPos h1a
  have hN1p : 0 < oddN1 R w p :=
    oddN1_pos_of_positivePlateau hp hl (hlm.trans hmr) hrR hwNonneg hwPos h1p
  have hN3a0 : 0 <= oddN3 R w a := oddN3_nonneg ha hwNonneg
  have hN3p0 : 0 <= oddN3 R w p := oddN3_nonneg hp hwNonneg
  have hN5a0 : 0 <= oddN5 R w a := oddN5_nonneg ha hwNonneg
  have hN5p0 : 0 <= oddN5 R w p := oddN5_nonneg hp hwNonneg
  have hsupportA := literalOddSupportMomentBounds hR ha hwNonneg h1a h3a h5a
  have hsupportP := literalOddSupportMomentBounds hR hp hwNonneg h1p h3p h5p
  have hea1raw := oddSixScaledRemainder_le_N5 (r := r) ha hwNonneg h5a
  have hea2raw := oddSixScaledRemainder_le_N5 (r := 2*r) ha hwNonneg h5a
  have hep1raw := oddSixScaledRemainder_le_N5 (r := r) hp hwNonneg h5p
  have hep2raw := oddSixScaledRemainder_le_N5 (r := 2*r) hp hwNonneg h5p
  have hea1 : |oddSixScaledRemainder R w a r| <= r^5*(oddN5 R w a/20) := by
    simpa [abs_of_pos hr] using hea1raw
  have hep1 : |oddSixScaledRemainder R w p r| <= r^5*(oddN5 R w p/20) := by
    simpa [abs_of_pos hr] using hep1raw
  have h2r : 0 < 2*r := mul_pos (by norm_num) hr
  have hea2 : |oddSixScaledRemainder R w a (2*r)| <=
      32*r^5*(oddN5 R w a/20) := by
    have := hea2raw
    rw [abs_of_pos h2r] at this
    nlinarith
  have hep2 : |oddSixScaledRemainder R w p (2*r)| <=
      32*r^5*(oddN5 R w p/20) := by
    have := hep2raw
    rw [abs_of_pos h2r] at this
    nlinarith
  have hneg := oddActualDeterminant_neg_of_supportGate
    hR hr hr1 hN1a hN3a0 hN5a0 hN1p hN3p0 hN5p0
    hsupportA.1 hsupportA.2 hsupportP.1 hsupportP.2 hgate
    hea1 hea2 hep1 hep2
  exact ⟨r, hr, hr1, by
    unfold literalOddFiniteDeterminant
    exact hneg⟩

end Synthesis
