import Mathlib.Tactic
import Synthesis.RiemannG21Zeta23PlateauAdapter
import Synthesis.RiemannG21OddRatioGapRadiusGate

/-!
# G21 odd continuum-to-radius compiler

This welds the literal N1/N3 continuum strict moment theorem to the existing
normalized small-radius gate.  Once the taper supplies a nonnegative positive
plateau and the four required integrability facts, the odd G21 lane gets:

* N1(a)>0 and N1(p)>0;
* Delta_odd = N1(a)N3(p)-N3(a)N1(p) > 0;
* q_p=N3(p)/N1(p) > q_a=N3(a)/N1(a);
* an existential `0<r<=1` satisfying the support-only radius gate.

The literal odd low response is `u*phi(u)*sinh(yu)`; this `u` factor is part of
the same-object contract and must not be dropped.
-/

noncomputable section

open MeasureTheory Set

namespace Synthesis

/-- Positive-half literal N1 response weight. -/
def oddHeightWeight (R : ℝ) (w : ℝ → ℝ) (y x : ℝ) : ℝ :=
  x * g21ClippedWeight R w x * Real.sinh (y*x)

/-- First odd moment. -/
def oddN1 (R : ℝ) (w : ℝ → ℝ) (y : ℝ) : ℝ :=
  moment0 (oddHeightWeight R w y) volume

/-- Third odd moment. -/
def oddN3 (R : ℝ) (w : ℝ → ℝ) (y : ℝ) : ℝ :=
  momentQ (fun x : ℝ => x^2) (oddHeightWeight R w y) volume

/-- Normalized odd support coordinate. -/
def oddRatio (R : ℝ) (w : ℝ → ℝ) (y : ℝ) : ℝ :=
  oddN3 R w y / oddN1 R w y

/-- The first literal odd moment is strictly positive under the same positive
plateau hypotheses used by the continuum TP2 compiler. -/
theorem oddN1_pos_of_positivePlateau
    {w : ℝ → ℝ} {y R l r : ℝ}
    (hy : 0 < y) (hl : 0 < l) (hlr : l < r) (hrR : r < R)
    (hwNonneg : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (hwPos : ∀ x ∈ Ioo l r, 0 < w x)
    (hA : Integrable (oddHeightWeight R w y) volume) :
    0 < oddN1 R w y := by
  unfold oddN1 moment0
  apply integral_pos_of_nonneg_of_pos_on_posMeasure hA
  · intro x
    unfold oddHeightWeight
    have hwc : 0 <= g21ClippedWeight R w x := by
      by_cases hx : x ∈ Icc (0:ℝ) R
      · simpa [g21ClippedWeight, hx] using hwNonneg x hx
      · simp [g21ClippedWeight, hx]
    by_cases hx0 : 0 <= x
    · exact mul_nonneg (mul_nonneg hx0 hwc)
        ((Real.sinh_nonneg_iff).2 (mul_nonneg hy.le hx0))
    · have hxnot : x ∉ Icc (0:ℝ) R := by
        intro hx
        exact hx0 hx.1
      simp [oddHeightWeight, g21ClippedWeight, hxnot]
  · have hs : 0 < volume (Ioo l r) := by
      simp [Real.volume_Ioo, ENNReal.ofReal_pos, sub_pos, hlr]
    exact hs
  · intro x hx
    have hx0 : 0 < x := hl.trans hx.1
    have hxR : x < R := hx.2.trans hrR
    have hxI : x ∈ Icc (0:ℝ) R := ⟨hx0.le, hxR.le⟩
    unfold oddHeightWeight
    have hwc : g21ClippedWeight R w x = w x := by
      simp [g21ClippedWeight, hxI]
    rw [hwc]
    exact mul_pos (mul_pos hx0 (hwPos x hx))
      ((Real.sinh_pos_iff).2 (mul_pos hy hx0))

/-- End-to-end literal odd continuum compiler through normalized-gap and radius
existence. -/
theorem exists_unit_oddRadiusGate_of_positivePlateau
    {w : ℝ → ℝ} {a p R l m r : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hl : 0 < l) (hlm : l < m) (hmr : m < r) (hrR : r < R)
    (hwNonneg : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (hwPos : ∀ x ∈ Ioo l r, 0 < w x)
    (hAa : Integrable (oddHeightWeight R w a) volume)
    (hAp : Integrable (oddHeightWeight R w p) volume)
    (hQa : Integrable (fun x => x^2 * oddHeightWeight R w a x) volume)
    (hQp : Integrable (fun x => x^2 * oddHeightWeight R w p x) volume) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ <= 1 ∧
      g21OddSupportPolynomial R * ρ^2 <
        900 * (oddRatio R w p - oddRatio R w a) := by
  have hN1a : 0 < oddN1 R w a :=
    oddN1_pos_of_positivePlateau ha hl (hlm.trans hmr) hrR hwNonneg hwPos hAa
  have hN1p : 0 < oddN1 R w p :=
    oddN1_pos_of_positivePlateau (ha.trans hap) hl (hlm.trans hmr) hrR hwNonneg hwPos hAp
  have hcross :
      0 < oddN1 R w a * oddN3 R w p - oddN3 R w a * oddN1 R w p := by
    simpa [oddN1, oddN3, oddHeightWeight, g21OddMomentWeight,
      mul_assoc, mul_left_comm, mul_comm] using
      (oddMomentCrossProduct_pos_of_positivePlateau
        ha hap hl hlm hmr hrR hwNonneg hwPos hAa hAp hQa hQp)
  have hratio : oddRatio R w a < oddRatio R w p := by
    unfold oddRatio
    apply oddRatioGap_of_crossProduct hN1a hN1p
    linarith
  exact exists_unit_supportOnlyOddRadiusGate (by
      have := hl.trans (hlm.trans (hmr.trans hrR))
      linarith) (sub_pos.mpr hratio)

end Synthesis
