import Mathlib

/-!
# RH Route-B: nonpositive first-zero fifth coefficient

The proposed shortcut gamma1^5 - E[gamma^2]*gamma1^3 > 0
does not follow from gamma1 being the smallest positive ordinate.
If a nonnegative-weight mean of squares is at least gamma1^2,
then the first fifth-minus-third coefficient is NONPOSITIVE.

This is a negative control for the proposed sign inference, not a
counterexample to the actual signed Möbius-weighted zero spectrum,
the original signedFifthCorrelationGapAt, G3 or RH.
-/

namespace Synthesis

theorem firstZeroSignedFifthCoefficient_nonpos
    {gamma meanSq : ℝ}
    (hgamma : 0 ≤ gamma)
    (hmean : gamma^2 ≤ meanSq) :
    gamma^5 - meanSq*gamma^3 ≤ 0 := by
  calc
    gamma^5 - meanSq*gamma^3 =
        (gamma^2 - meanSq)*gamma^3 := by ring
    _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hmean) (pow_nonneg hgamma 3)

end Synthesis
