import Integration.EisensteinJZeroSplitJacobiCyclotomicExact

/-!
RED-first regression for the split-prime Jacobi -> cyclotomic-integer/norm tranche.

This contract deliberately stops before identifying Mathlib's complex
cyclotomic order with the repo's `EisensteinQA`.  It requires only the
same-prime facts that can be paid without such a carrier collapse:

* the canonical split Jacobi sum belongs to `Z[zeta_6]`;
* its inverse-character Jacobi partner is its complex conjugate;
* their product, hence complex norm-square, is exactly `p`.

The final `Z[zeta_6] ≃ Z[omega] ≃ EisensteinQA` carrier equivalence and
associate/canonical-prime selection remain separate typed payments.
-/

namespace Integration.EisensteinJZeroSplitJacobiCyclotomicRegression

open Integration.EisensteinJZeroSplitJacobiCyclotomicExact

example (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    splitJacobiSum p hp3 ∈ Algebra.adjoin ℤ ({sixthRoot : ℂ} : Set ℂ) :=
  splitJacobiSum_mem_sixthCyclotomicOrder p hp2 hp3

example (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    splitJacobiSum p hp3 * Complex.conj (splitJacobiSum p hp3) = (p : ℂ) :=
  splitJacobiSum_mul_conj p hp2 hp3

example (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    Complex.normSq (splitJacobiSum p hp3) = p :=
  splitJacobiSum_normSq p hp2 hp3

end Integration.EisensteinJZeroSplitJacobiCyclotomicRegression
