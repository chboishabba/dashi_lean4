import Integration.PositiveOddZetaImaginaryZeroExact

/-!
# Synthesis-level re-export: genuine odd Riemann zeta values are real

The proof resides at Integration.PositiveOddZetaImaginaryZeroExact on the
same Mathlib `riemannZeta`. This file is a thin receipt and does not
claim an Agda proof or an odd-zeta irrationality theorem.
-/

namespace Synthesis

theorem positiveOddZetaImaginaryZeroExact
    (k : ℕ) (hk : 1 ≤ k) :
    (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).im = 0 :=
  Integration.PositiveOddZetaImaginaryZeroExact.positive_odd_zeta_im_zero k hk

#print axioms positiveOddZetaImaginaryZeroExact

end Synthesis
