import Mathlib

/-!
# Exact original RH zero-location -> vanishing horizontal displacement

P0/P1 seam with DASHI's original target-centred G2 scalar consumers.

The target is Mathlib's own `RiemannHypothesis` on actual `riemannZeta`.
No abstract replacement zero type, no new analytic function. The horizontal
coordinate is literally `s.re - 1/2`. Once source zero identity and excluded
trivial/pole cases are paid, the external RH theorem gives zero displacement.

This is an elementary consumer theorem, NOT a proof of RH, G2 signed
cancellation, near/far inequalities, or an Agda/Lean proof transfer.
It can be elaborated independently in each selected compatible Mathlib
environment: do not import v4.33.1 oleans into the DASHI v4.35 root.
Source-written, local Lean kernel receipt still open. No CI.
-/

namespace DASHI.AlpogeRH

/-- Uses exactly Mathlib's original nontrivial-zero hypotheses. -/
theorem zero_horizontal_of_mathlib_rh
    (hRH : RiemannHypothesis) (s : ℂ)
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hpole : s ≠ 1) :
    s.re - (1 / 2 : ℝ) = 0 := by
  have hline : s.re = (1 / 2 : ℝ) := hRH s hz htriv hpole
  rw [hline]
  ring

/-- A source-defined horizontal zero is enough to make every real-parameter
cosh factor exactly one. This does not control the remaining cosine sum. -/
theorem cosh_horizontal_factor_of_mathlib_rh
    (hRH : RiemannHypothesis) (s : ℂ)
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hpole : s ≠ 1) (u : ℝ) :
    Real.cosh ((s.re - (1 / 2 : ℝ)) * u) = 1 := by
  rw [zero_horizontal_of_mathlib_rh hRH s hz htriv hpole]
  simp

#print axioms zero_horizontal_of_mathlib_rh
#print axioms cosh_horizontal_factor_of_mathlib_rh

end DASHI.AlpogeRH
