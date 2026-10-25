import Integration.EisensteinJZeroCMEndomorphismExact

/-!
RED-first regression for the next Eisenstein max-cut.

The production owner must put the order-three x-coordinate rotation on Mathlib's
actual affine Weierstrass point group.  The regression intentionally asks for
the group-endomorphism theorem, not only equation preservation.
-/

namespace Integration.EisensteinJZeroCMEndomorphismRegression

open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine K) (ω : K)

example
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0) (ha4 : W.a₄ = 0)
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    W.Point →+ W.Point :=
  jZeroRotationEndomorphism W ω ha1 ha2 ha3 ha4 hω3 hω1

example
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0) (ha4 : W.a₄ = 0)
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (P : W.Point) :
    (jZeroRotationEndomorphism W ω ha1 ha2 ha3 ha4 hω3 hω1)
      ((jZeroRotationEndomorphism W ω ha1 ha2 ha3 ha4 hω3 hω1)
        ((jZeroRotationEndomorphism W ω ha1 ha2 ha3 ha4 hω3 hω1) P)) = P :=
  jZeroRotationEndomorphism_orderThree W ω ha1 ha2 ha3 ha4 hω3 hω1 P

end Integration.EisensteinJZeroCMEndomorphismRegression
