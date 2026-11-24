import Main
import Solution

/-!
# Optional arithmetic consumers of the original RH proof

Source attribution: the mathematics is Guy Robin's and Jeffrey C. Lagarias's;
the independent Robin1984 formalization (Jonas Whidden, CITATION.cff at
acab1a31f31e0499518a4416b63281e0b4838f9c) owns the equivalence proofs.
The original RH proof owns riemannHypothesis. Andrew Sutherland's independent
ArithSolution.lean already composes these two original sources. This DASHI
adapter only names those exact terminal statements for our receipt audit.
No source theorem is duplicated or independently claimed. Compatible Lean 4.33.1
kernel acceptance of this adapter is not asserted by source readback.
-/

namespace DASHI.AlpogeRH.Arithmetic

theorem robin :
    ∀ n : ℕ, 5040 < n →
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) <
        Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) :=
  Robin1984.robin_inequality_iff_riemannHypothesis.mpr _root_.riemannHypothesis

theorem lagarias :
    ∀ n : ℕ, 0 < n →
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
        (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) :=
  Robin1984.riemann_hypothesis_iff_lagarias_elementary_criterion.mp _root_.riemannHypothesis

#print axioms robin
#print axioms lagarias

end DASHI.AlpogeRH.Arithmetic
