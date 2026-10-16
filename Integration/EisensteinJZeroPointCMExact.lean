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

theorem omega_four : omega ^ 4 = omega := by
  rw [show (4 : Nat) = 3 + 1 by norm_num, pow_succ, omega_cube, one_mul]

theorem omega_ne_zero : omega ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.im h
  simpa [omega] using this

private theorem omega_mul_injective : Function.Injective (fun x : EisensteinField => omega * x) := by
  intro x y h
  have hz : omega * (x - y) = 0 := by
    calc
      omega * (x - y) = omega * x - omega * y := by ring
      _ = 0 := sub_eq_zero.mpr h
  rcases mul_eq_zero.mp hz with hω | hxy
  · exact (omega_ne_zero hω).elim
  · exact sub_eq_zero.mp hxy

/-- The concrete `j=0` short Weierstrass equation `y² = x³ + 1` over `Q(ω)`. -/
def jZeroCurve : WeierstrassCurve.Affine EisensteinField :=
  ⟨0, 0, 0, 0, 1⟩

@[simp] theorem jZeroCurve_equation (x y : EisensteinField) :
    jZeroCurve.Equation x y ↔ y ^ 2 = x ^ 3 + 1 := by
  simp [jZeroCurve, WeierstrassCurve.Affine.equation_iff]

@[simp] theorem jZeroCurve_negY (x y : EisensteinField) :
    jZeroCurve.negY x y = -y := by
  simp [jZeroCurve, WeierstrassCurve.Affine.negY]

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

/-- The order-three point symmetry is bijective before the group-homomorphism
calculation below. -/
theorem omegaPoint_bijective : Function.Bijective omegaPoint := by
  constructor
  · intro P Q h
    have h' := congrArg (fun X => omegaPoint (omegaPoint X)) h
    simpa [omegaPoint_order_three] using h'
  · intro P
    refine ⟨omegaPoint (omegaPoint P), ?_⟩
    exact omegaPoint_order_three P

------------------------------------------------------------------------
-- Exact covariance of the affine addition formulae.
------------------------------------------------------------------------

/-- The secant/tangent slope has C3 weight two. -/
theorem slope_omega_covariant (x₁ x₂ y₁ y₂ : EisensteinField) :
    jZeroCurve.slope (omega * x₁) (omega * x₂) y₁ y₂
      = omega ^ 2 * jZeroCurve.slope x₁ x₂ y₁ y₂ := by
  by_cases hx : x₁ = x₂
  · subst x₂
    by_cases hy : y₁ = -y₂
    · simp [WeierstrassCurve.Affine.slope, jZeroCurve, hy]
    · simp [WeierstrassCurve.Affine.slope, jZeroCurve, hy]
      ring
  · have hxo : omega * x₁ ≠ omega * x₂ := by
      intro h
      exact hx (omega_mul_injective h)
    rw [jZeroCurve.slope_of_X_ne hxo, jZeroCurve.slope_of_X_ne hx]
    have hden : omega * x₁ - omega * x₂ = omega * (x₁ - x₂) := by ring
    rw [hden]
    field_simp [omega_ne_zero, sub_ne_zero.mpr hx]
    rw [omega_cube]
    ring

/-- The x-coordinate of the group sum has C3 weight one. -/
theorem addX_omega_covariant (x₁ x₂ ℓ : EisensteinField) :
    jZeroCurve.addX (omega * x₁) (omega * x₂) (omega ^ 2 * ℓ)
      = omega * jZeroCurve.addX x₁ x₂ ℓ := by
  simp only [WeierstrassCurve.Affine.addX, jZeroCurve]
  have h4 : (omega ^ 2 * ℓ) ^ 2 = omega ^ 4 * ℓ ^ 2 := by ring
  rw [h4, omega_four]
  ring

/-- The y-coordinate of the group sum is C3-invariant. -/
theorem addY_omega_covariant (x₁ x₂ y₁ ℓ : EisensteinField) :
    jZeroCurve.addY (omega * x₁) (omega * x₂) y₁ (omega ^ 2 * ℓ)
      = jZeroCurve.addY x₁ x₂ y₁ ℓ := by
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    jZeroCurve_negY]
  rw [addX_omega_covariant]
  have h3 : omega ^ 2 * omega = (1 : EisensteinField) := by
    simpa [pow_two, mul_assoc] using omega_cube
  rw [show omega * jZeroCurve.addX x₁ x₂ ℓ - omega * x₁
      = omega * (jZeroCurve.addX x₁ x₂ ℓ - x₁) by ring]
  rw [← mul_assoc, h3, one_mul]

/-- Vertical-pair status is unchanged by the C3 x-scaling. -/
theorem vertical_pair_omega_iff (x₁ x₂ y₁ y₂ : EisensteinField) :
    (omega * x₁ = omega * x₂ ∧ y₁ = jZeroCurve.negY (omega * x₂) y₂)
      ↔ (x₁ = x₂ ∧ y₁ = jZeroCurve.negY x₂ y₂) := by
  simp only [jZeroCurve_negY]
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨omega_mul_injective hx, hy⟩
  · rintro ⟨rfl, hy⟩
    exact ⟨rfl, hy⟩

------------------------------------------------------------------------
-- Actual point-group endomorphism.
------------------------------------------------------------------------

/-- The C3 point action respects Mathlib's genuine elliptic-curve group law. -/
theorem omegaPoint_add (P Q : jZeroCurve.Point) :
    omegaPoint (P + Q) = omegaPoint P + omegaPoint Q := by
  rcases P with _ | @⟨x₁, y₁, h₁⟩ <;>
    rcases Q with _ | @⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  · by_cases hxy : x₁ = x₂ ∧ y₁ = jZeroCurve.negY x₂ y₂
    · have hxyω : omega * x₁ = omega * x₂ ∧
          y₁ = jZeroCurve.negY (omega * x₂) y₂ :=
        (vertical_pair_omega_iff x₁ x₂ y₁ y₂).2 hxy
      rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2,
        WeierstrassCurve.Affine.Point.add_of_Y_eq hxyω.1 hxyω.2]
      rfl
    · have hxyω : ¬(omega * x₁ = omega * x₂ ∧
          y₁ = jZeroCurve.negY (omega * x₂) y₂) := by
        intro h
        exact hxy ((vertical_pair_omega_iff x₁ x₂ y₁ y₂).1 h)
      rw [WeierstrassCurve.Affine.Point.add_some hxy,
        WeierstrassCurve.Affine.Point.add_some hxyω]
      simp only [omegaPoint_some, WeierstrassCurve.Affine.Point.some.injEq]
      have hs := slope_omega_covariant x₁ x₂ y₁ y₂
      constructor
      · rw [hs]
        exact (addX_omega_covariant x₁ x₂ (jZeroCurve.slope x₁ x₂ y₁ y₂)).symm
      · rw [hs]
        exact addY_omega_covariant x₁ x₂ y₁ (jZeroCurve.slope x₁ x₂ y₁ y₂)

/-- The same-object CM action as an actual endomorphism of the elliptic point
group, rather than a set-level C3 permutation. -/
noncomputable def omegaPointEndomorphism : jZeroCurve.Point →+ jZeroCurve.Point where
  toFun := omegaPoint
  map_zero' := omegaPoint_zero
  map_add' := omegaPoint_add

@[simp] theorem omegaPointEndomorphism_apply (P : jZeroCurve.Point) :
    omegaPointEndomorphism P = omegaPoint P := rfl

/-- The endomorphism itself has order three under composition. -/
theorem omegaPointEndomorphism_order_three (P : jZeroCurve.Point) :
    omegaPointEndomorphism
      (omegaPointEndomorphism (omegaPointEndomorphism P)) = P :=
  omegaPoint_order_three P

/-- The paid result is a genuine order-three group endomorphism on the same
`j=0` curve over `Q(ω)`.  Identifying the complete endomorphism ring with the
Eisenstein integers, constructing the associated Hecke character, and matching
all Euler factors remain distinct global arithmetic obligations. -/
structure CMPointBoundary where
  actualMathlibPointCarrierPaid : Bool := true
  sameCurveEquationPreservationPaid : Bool := true
  nonsingularPointActionPaid : Bool := true
  orderThreePointBijectionPaid : Bool := true
  groupLawHomomorphismPaid : Bool := true
  fullCMEndomorphismRingPaid : Bool := false
  heckeCharacterPaid : Bool := false
  localEulerFactorIdentificationPaid : Bool := false

/-- The explicit frontier after paying the same-object elliptic point-group
endomorphism. -/
def canonicalBoundary : CMPointBoundary := {}

end Dashi.EisensteinJZeroPointCMExact
