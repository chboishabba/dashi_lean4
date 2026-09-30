import Mathlib

/-!
# Characteristic-two 3-division polynomial arithmetic for y²+y=x³

For the long Weierstrass coefficients a₁=a₂=a₄=a₆=0, a₃=1
the classical 3-division polynomial specializes to x⁴+x.
This owner proves the underlying characteristic-two factorization;
it does NOT claim that a geometric Weil pairing has been constructed.

The independent geometric step is to establish that this specialized
polynomial classifies the x-coordinates of nonzero 3-torsion on the
actual base-changed curve, then construct the Weil pairing.
-/

namespace Integration.OggSSPP2F4GeometricThreeDivisionFrontier

theorem division_three_polynomial_factors (x : ZMod 2) :
    x^4 + x = x * (x + 1) * (x^2 + x + 1) := by
  ring

theorem three_division_polynomial_vanishes_at_zero :
    (0 : ZMod 2)^4 + 0 = 0 := by
  norm_num

theorem three_division_polynomial_vanishes_at_one :
    (1 : ZMod 2)^4 + 1 = 0 := by
  norm_num

end Integration.OggSSPP2F4GeometricThreeDivisionFrontier
