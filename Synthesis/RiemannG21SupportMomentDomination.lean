import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import Synthesis.RiemannG21OddDeterminantMargin

/-!
# G21 compact-support moment domination

This is the real ordered-integral theorem behind the Agda owner
`RiemannG21ActualTaperOddMomentSupportExact`.

For a nonnegative base weight on `[0,R]`, the support inequalities

  `u^2 <= R^2`,  `u^4 <= R^4`

integrate directly to

  `M2 <= R^2 M0`,  `M4 <= R^4 M0`.

For the G21 odd family the base weight is schematically
`u * phi(u) * sinh(y*u)`, so these become exactly
`N3 <= R^2 N1` and `N5 <= R^4 N1` once the literal taper weight and its
integrability/nonnegativity receipts are instantiated.
-/

noncomputable section

open Set MeasureTheory intervalIntegral

namespace Synthesis

/-- Zeroth compact-support moment of a base weight. -/
def supportMoment0 (base : ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..R, base u

/-- Second compact-support moment. -/
def supportMoment2 (base : ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..R, u^2 * base u

/-- Fourth compact-support moment. -/
def supportMoment4 (base : ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..R, u^4 * base u

/-- On a nonnegative compact interval, the second support moment is bounded by
`R^2` times the zeroth moment. -/
theorem supportMoment2_le_sq_mul
    {base : ℝ → ℝ} {R : ℝ}
    (hR : 0 <= R)
    (hbase : ∀ u ∈ Icc (0 : ℝ) R, 0 <= base u)
    (h0 : IntervalIntegrable base volume 0 R)
    (h2 : IntervalIntegrable (fun u => u^2 * base u) volume 0 R) :
    supportMoment2 base R <= R^2 * supportMoment0 base R := by
  unfold supportMoment2 supportMoment0
  calc
    (∫ u in (0 : ℝ)..R, u^2 * base u)
        <= ∫ u in (0 : ℝ)..R, R^2 * base u := by
      refine intervalIntegral.integral_mono_on hR h2 (h0.const_mul _) ?_
      intro u hu
      have hu0 : 0 <= u := hu.1
      have huR : u <= R := hu.2
      have hb : 0 <= base u := hbase u hu
      have hsquares : u^2 <= R^2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hsquares hb
    _ = R^2 * ∫ u in (0 : ℝ)..R, base u := by
      rw [intervalIntegral.integral_const_mul]

/-- Fourth-moment companion. -/
theorem supportMoment4_le_fourth_mul
    {base : ℝ → ℝ} {R : ℝ}
    (hR : 0 <= R)
    (hbase : ∀ u ∈ Icc (0 : ℝ) R, 0 <= base u)
    (h0 : IntervalIntegrable base volume 0 R)
    (h4 : IntervalIntegrable (fun u => u^4 * base u) volume 0 R) :
    supportMoment4 base R <= R^4 * supportMoment0 base R := by
  unfold supportMoment4 supportMoment0
  calc
    (∫ u in (0 : ℝ)..R, u^4 * base u)
        <= ∫ u in (0 : ℝ)..R, R^4 * base u := by
      refine intervalIntegral.integral_mono_on hR h4 (h0.const_mul _) ?_
      intro u hu
      have hu0 : 0 <= u := hu.1
      have huR : u <= R := hu.2
      have hb : 0 <= base u := hbase u hu
      have hsq : u^2 <= R^2 := by nlinarith
      have hpow : u^4 <= R^4 := by
        nlinarith [sq_nonneg (u^2), sq_nonneg (R^2)]
      exact mul_le_mul_of_nonneg_right hpow hb
    _ = R^4 * ∫ u in (0 : ℝ)..R, base u := by
      rw [intervalIntegral.integral_const_mul]

/-- G21 odd-moment specialization in theorem form.  The definitions are kept
literal enough that a future exact taper import only has to identify the base
weight and discharge integrability/nonnegativity. -/
theorem g21OddSupportMomentBounds
    {base : ℝ → ℝ} {R : ℝ}
    (hR : 0 <= R)
    (hbase : ∀ u ∈ Icc (0 : ℝ) R, 0 <= base u)
    (h0 : IntervalIntegrable base volume 0 R)
    (h2 : IntervalIntegrable (fun u => u^2 * base u) volume 0 R)
    (h4 : IntervalIntegrable (fun u => u^4 * base u) volume 0 R) :
    supportMoment2 base R <= R^2 * supportMoment0 base R ∧
    supportMoment4 base R <= R^4 * supportMoment0 base R := by
  exact ⟨supportMoment2_le_sq_mul hR hbase h0 h2,
    supportMoment4_le_fourth_mul hR hbase h0 h4⟩

end Synthesis
