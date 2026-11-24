import Main
import Solution

/-!
# Optional arithmetic consumers of the original RH proof

Source attribution: the mathematics is Guy Robin's and Jeffrey C. Lagarias's;
the independent Robin1984 formalization (Jonas Whidden, CITATION.cff at
5ce18bf3487c68d9353276ef5811057f60d17808) owns the equivalence proofs.
The original RH proof owns riemannHypothesis and LFunction_eq_zero_re.
Robin1984 also owns the cyclotomic ideal Robin equivalence and primitive
Dedekind factorization. Sutherland's 24 Nov 05:25 UTC report checks the third
arithmetic consequence independently. The fourth alias uses the same source
factorization directly; it is not a separately reported comparator target. Andrew Sutherland's independent
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

theorem cyclotomic_corrected_ideal_robin :
    ∀ (modulus : ℕ) [NeZero modulus],
      Robin1984.GRH.CorrectedIdealRobin (CyclotomicField modulus ℚ) :=
  Robin1984.GRH.dirichletGRH_iff_cyclotomicCorrectedIdealRobin.mp
    _root_.LFunction_eq_zero_re

theorem cyclotomic_dedekind_rh :
    ∀ (modulus : ℕ) [NeZero modulus],
      Robin1984.GRH.DedekindRH (CyclotomicField modulus ℚ) :=
  Robin1984.GRH.dirichletGRH_iff_cyclotomicDedekindRH.mp
    _root_.LFunction_eq_zero_re

#print axioms cyclotomic_corrected_ideal_robin
#print axioms cyclotomic_dedekind_rh
#print axioms robin
#print axioms lagarias

end DASHI.AlpogeRH.Arithmetic
