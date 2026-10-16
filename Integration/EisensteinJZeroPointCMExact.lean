import Mathlib

namespace Dashi.EisensteinJZeroPointCMExact

open WeierstrassCurve

/-- The quadratic field `Q(ω)` in the basis `1,ω`, with `ω² = -1-ω`. -/
abbrev EisensteinField := QuadraticAlgebra ℚ (-1) (-1)

/-- The defining quadratic has no rational root: `r²+r+1` is strictly positive. -/
private theorem eisenstein_no_root :
    ∀ r : ℚ, r ^ 2 ≠ (-1 : ℚ) + (-1 : ℚ) * r := by
  intro r h
  have hs : 0 ≤ (2 * r + 1) ^ 2 := sq_nonneg (2 * r + 1)
  nlinarith

private local instance : Fact (∀ r : ℚ, r ^ 2 ≠ (-1 : ℚ) + (-1 : ℚ) * r) :=
  ⟨eisenstein_no_root⟩

noncomputable local instance : Field EisensteinField := inferInstance

/-- The Eisenstein cube root of unity. -/
def omega : EisensteinField := QuadraticAlgebra.omega

@[simp] theorem omega_re : omega.re = 0 := rfl
@[simp] theorem omega_im : omega.im = 1 := rfl

theorem omega_square : omega ^ 2 = -(1 : EisensteinField) - omega := by
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
  ext <;> norm_num [omega]

theorem omega_cube : omega ^ 3 = (1 : EisensteinField) := by
  calc
    omega ^ 3 = omega * omega ^ 2 := by ring
    _ = omega * (-1 - omega) := by rw [omega_square]
    _ = 1 := by
      rw [mul_sub, mul_neg, mul_one, ← pow_two, omega_square]
      ring

theorem omega_ne_zero : omega ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.im h
  simpa [omega] using this

/-- The concrete `j=0` short Weierstrass equation `y² = x³ + 1` over `Q(ω)`. -/
def jZeroCurve : WeierstrassCurve.Affine EisensteinField :=
  ⟨0, 0, 0, 0, 1⟩

@[simp] theorem jZeroCurve_equation (x y : EisensteinField) :
    jZeroCurve.Equation x y ↔ y ^ 2 = x ^ 3 + 1 := by
  simp [jZeroCurve, WeierstrassCurve.Affine.equation_iff]

/-- Its discriminant is the nonzero constant `-432`. -/
theorem jZeroCurve_delta_ne_zero : jZeroCurve.Δ ≠ 0 := by
  norm_num [jZeroCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- Multiplying the x-coordinate by `ω` preserves the same cubic equation. -/
theorem omega_preserves_equation {x y : EisensteinField}
    (h : jZeroCurve.Equation x y) :
    jZeroCurve.Equation (omega * x) y := by
  rw [jZeroCurve_equation] at h ⊢
  rw [mul_pow, omega_cube, one_mul]
  exact h

/-- The same coordinate action therefore preserves nonsingularity on this
elliptic curve, not merely the polynomial equation. -/
theorem omega_preserves_nonsingular {x y : EisensteinField}
    (h : jZeroCurve.Nonsingular x y) :
    jZeroCurve.Nonsingular (omega * x) y := by
  apply (jZeroCurve.equation_iff_nonsingular_of_Δ_ne_zero jZeroCurve_delta_ne_zero).mp
  apply omega_preserves_equation
  exact (jZeroCurve.equation_iff_nonsingular_of_Δ_ne_zero jZeroCurve_delta_ne_zero).mpr h

/-- The physical/algebraic C3 action lifted to Mathlib's actual nonsingular
Weierstrass point carrier, including the point at infinity. -/
noncomputable def omegaPoint : jZeroCurve.Point → jZeroCurve.Point
  | .zero => .zero
  | @.some _ _ _ x y h => .some (omega_preserves_nonsingular h)

@[simp] theorem omegaPoint_zero : omegaPoint 0 = 0 := rfl

@[simp] theorem omegaPoint_some {x y : EisensteinField}
    (h : jZeroCurve.Nonsingular x y) :
    omegaPoint (.some h) = .some (omega_preserves_nonsingular h) := rfl

/-- The lifted point action has exact order dividing three. -/
theorem omegaPoint_order_three (P : jZeroCurve.Point) :
    omegaPoint (omegaPoint (omegaPoint P)) = P := by
  rcases P with _ | @⟨x, y, h⟩
  · rfl
  · simp only [omegaPoint_some, WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · rw [mul_assoc, mul_assoc, ← pow_three, omega_cube, one_mul]
    · rfl

/-- The order-three point symmetry is bijective before any group-homomorphism
promotion. -/
theorem omegaPoint_bijective : Function.Bijective omegaPoint := by
  constructor
  · intro P Q h
    have h' := congrArg (fun X => omegaPoint (omegaPoint X)) h
    simpa [omegaPoint_order_three] using h'
  · intro P
    refine ⟨omegaPoint (omegaPoint P), ?_⟩
    exact omegaPoint_order_three P

/-- Claim-strength boundary.  The point-group carrier and exact order-three
bijection are paid here.  `map_add` is intentionally a separate theorem: an
order-three permutation of the point set is not yet a CM endomorphism. -/
structure CMPointBoundary where
  actualMathlibPointCarrierPaid : Bool := true
  sameCurveEquationPreservationPaid : Bool := true
  nonsingularPointActionPaid : Bool := true
  orderThreePointBijectionPaid : Bool := true
  groupLawHomomorphismPaid : Bool := false
  fullCMEndomorphismRingPaid : Bool := false
  heckeCharacterPaid : Bool := false
  localEulerFactorIdentificationPaid : Bool := false

/-- The explicit frontier after lifting the C3 action to actual elliptic points. -/
def canonicalBoundary : CMPointBoundary := {}

end Dashi.EisensteinJZeroPointCMExact
