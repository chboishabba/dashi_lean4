import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The order-three endomorphism on short j=0 Weierstrass curves

This owner pays the group-law step deliberately left open by the Agda
`EisensteinAZeroEllipticScalarExtensionExact` tranche.

For a short Weierstrass equation

    y^2 = x^3 + a6

and a nontrivial cube root `ω`, the coordinate action

    (x,y) |-> (ω*x,y)

preserves the equation.  Here we additionally prove that it preserves
Mathlib's actual affine elliptic group law, hence is an additive endomorphism,
and that its third iterate is the identity.

Mathlib owns the affine Weierstrass point carrier and group law (following
Silverman); DASHI owns the specialization/composition below.  No Hecke
character, Frobenius coefficient formula, or L-function identification is
inferred from this theorem alone.
-/

namespace Integration

open WeierstrassCurve

section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine K) (ω : K)
variable (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0) (ha4 : W.a₄ = 0)
variable (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)

private lemma omega_ne_zero : ω ≠ 0 := by
  intro h
  rw [h, zero_pow (by decide)] at hω3
  exact zero_ne_one hω3

private lemma omega_sq_mul_omega : ω ^ 2 * ω = 1 := by
  simpa [pow_succ, mul_assoc] using hω3

private lemma omega_mul_sq : ω * ω ^ 2 = 1 := by
  simpa [pow_succ, mul_assoc] using hω3

private lemma omega_four : ω ^ 4 = ω := by
  calc
    ω ^ 4 = ω * ω ^ 3 := by ring
    _ = ω := by rw [hω3, mul_one]

private lemma rotate_equation {x y : K} (h : W.Equation x y) :
    W.Equation (ω * x) y := by
  rw [W.equation_iff] at h ⊢
  rw [ha1, ha2, ha3, ha4] at h ⊢
  simp only [zero_mul, zero_add, add_zero]
  calc
    y ^ 2 = x ^ 3 + W.a₆ := h
    _ = (ω * x) ^ 3 + W.a₆ := by
      rw [mul_pow, hω3, one_mul]

private lemma rotate_nonsingular {x y : K} (h : W.Nonsingular x y) :
    W.Nonsingular (ω * x) y := by
  rw [W.nonsingular_iff] at h ⊢
  rcases h with ⟨heq, hns⟩
  constructor
  · exact rotate_equation W ω ha1 ha2 ha3 ha4 hω3 heq
  · rw [ha1, ha2, ha3, ha4] at hns ⊢
    simp only [zero_mul, zero_add, add_zero]
    rcases hns with hx | hy
    · left
      intro hz
      apply hx
      have hscale : 3 * (ω * x) ^ 2 = ω ^ 2 * (3 * x ^ 2) := by ring
      rw [hscale] at hz
      have : 3 * x ^ 2 = 0 :=
        (mul_eq_zero.mp hz.symm).resolve_left (pow_ne_zero _ (omega_ne_zero ω hω3))
      exact this.symm
    · exact Or.inr hy

/-- Coordinate rotation on the actual Mathlib affine point carrier. -/
def jZeroRotatePoint : W.Point → W.Point
  | .zero => .zero
  | @.some x y h => .some (rotate_nonsingular W ω ha1 ha2 ha3 ha4 hω3 h)

@[simp] lemma jZeroRotatePoint_zero :
    jZeroRotatePoint W ω ha1 ha2 ha3 ha4 hω3 (0 : W.Point) = 0 := rfl

@[simp] lemma jZeroRotatePoint_some {x y : K} (h : W.Nonsingular x y) :
    jZeroRotatePoint W ω ha1 ha2 ha3 ha4 hω3 (.some h) =
      .some (rotate_nonsingular W ω ha1 ha2 ha3 ha4 hω3 h) := rfl

private lemma negY_rotate (x y : K) : W.negY (ω * x) y = W.negY x y := by
  simp [WeierstrassCurve.Affine.negY, ha1, ha3]

private lemma slope_rotate_nonvertical {x₁ x₂ y₁ y₂ : K}
    (hxy : ¬ (x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    W.slope (ω * x₁) (ω * x₂) y₁ y₂ =
      ω ^ 2 * W.slope x₁ x₂ y₁ y₂ := by
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    have hx' : ω * x₁ = ω * x₂ := congrArg (fun z => ω * z) hx
    have hy' : y₁ ≠ W.negY (ω * x₂) y₂ := by
      simpa [negY_rotate W ω ha1 ha3 x₂ y₂] using hy
    rw [W.slope_of_Y_ne hx hy, W.slope_of_Y_ne hx' hy']
    rw [ha1, ha2, ha3, ha4]
    simp only [zero_mul, zero_add, add_zero]
    ring
  · have hx' : ω * x₁ ≠ ω * x₂ := by
      intro h
      apply hx
      exact (mul_left_cancel₀ (omega_ne_zero ω hω3)) h
    rw [W.slope_of_X_ne hx, W.slope_of_X_ne hx']
    field_simp [omega_ne_zero ω hω3]
    linear_combination (omega_sq_mul_omega ω hω3) * (y₁ - y₂) * (x₁ - x₂)

private lemma addX_rotate {x₁ x₂ y₁ y₂ : K}
    (hxy : ¬ (x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    W.addX (ω * x₁) (ω * x₂)
      (W.slope (ω * x₁) (ω * x₂) y₁ y₂) =
    ω * W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) := by
  rw [slope_rotate_nonvertical W ω ha1 ha2 ha3 ha4 hω3 hxy]
  simp only [WeierstrassCurve.Affine.addX, ha1, ha2, zero_mul, zero_add, sub_zero]
  have h4 := omega_four ω hω3
  linear_combination
    (h4 - rfl : ω ^ 4 - ω = 0) * (W.slope x₁ x₂ y₁ y₂) ^ 2

private lemma addY_rotate {x₁ x₂ y₁ y₂ : K}
    (hxy : ¬ (x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    W.addY (ω * x₁) (ω * x₂) y₁
      (W.slope (ω * x₁) (ω * x₂) y₁ y₂) =
    W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂) := by
  rw [slope_rotate_nonvertical W ω ha1 ha2 ha3 ha4 hω3 hxy]
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, ha1, ha2, ha3, zero_mul, zero_add, add_zero, sub_zero]
  rw [addX_rotate W ω ha1 ha2 ha3 ha4 hω3 hxy]
  have h3 := omega_sq_mul_omega ω hω3
  linear_combination
    (h3 - rfl : ω ^ 2 * ω - 1 = 0) *
      (W.slope x₁ x₂ y₁ y₂) * (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) - x₁)

private theorem jZeroRotatePoint_add (P Q : W.Point) :
    jZeroRotatePoint W ω ha1 ha2 ha3 ha4 hω3 (P + Q) =
      jZeroRotatePoint W ω ha1 ha2 ha3 ha4 hω3 P +
      jZeroRotatePoint W ω ha1 ha2 ha3 ha4 hω3 Q := by
  cases P with
  | zero => simp [jZeroRotatePoint]
  | @some x₁ y₁ h₁ =>
    cases Q with
    | zero => simp [jZeroRotatePoint]
    | @some x₂ y₂ h₂ =>
      by_cases hv : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
      · rcases hv with ⟨hx, hy⟩
        have hx' : ω * x₁ = ω * x₂ := congrArg (fun z => ω * z) hx
        have hy' : y₁ = W.negY (ω * x₂) y₂ := by
          simpa [negY_rotate W ω ha1 ha3 x₂ y₂] using hy
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy,
          WeierstrassCurve.Affine.Point.add_of_Y_eq hx' hy']
        rfl
      · have hv' : ¬ (ω * x₁ = ω * x₂ ∧ y₁ = W.negY (ω * x₂) y₂) := by
          rintro ⟨hx', hy'⟩
          apply hv
          constructor
          · exact (mul_left_cancel₀ (omega_ne_zero ω hω3)) hx'
          · simpa [negY_rotate W ω ha1 ha3 x₂ y₂] using hy'
        rw [WeierstrassCurve.Affine.Point.add_some hv,
          WeierstrassCurve.Affine.Point.add_some hv']
        apply congrArg WeierstrassCurve.Affine.Point.some
        apply proof_irrel_heq

/-- The actual order-three additive endomorphism of Mathlib's point group. -/
noncomputable def jZeroRotationEndomorphism : W.Point →+ W.Point where
  toFun := jZeroRotatePoint W ω ha1 ha2 ha3 ha4 hω3
  map_zero' := rfl
  map_add' := jZeroRotatePoint_add W ω ha1 ha2 ha3 ha4 hω3

private lemma rotate_point_three (P : W.Point) :
    jZeroRotatePoint W ω ha1 ha2 ha3 ha4 hω3
      (jZeroRotatePoint W ω ha1 ha2 ha3 ha4 hω3
        (jZeroRotatePoint W ω ha1 ha2 ha3 ha4 hω3 P)) = P := by
  cases P with
  | zero => rfl
  | @some x y h =>
    have hx : ω * (ω * (ω * x)) = x := by
      calc
        ω * (ω * (ω * x)) = ω ^ 3 * x := by ring
        _ = x := by rw [hω3, one_mul]
    simp only [jZeroRotatePoint]
    cases hx
    rfl

/-- The CM-style endomorphism has exact order dividing three. -/
theorem jZeroRotationEndomorphism_orderThree (P : W.Point) :
    (jZeroRotationEndomorphism W ω ha1 ha2 ha3 ha4 hω3 hω1)
      ((jZeroRotationEndomorphism W ω ha1 ha2 ha3 ha4 hω3 hω1)
        ((jZeroRotationEndomorphism W ω ha1 ha2 ha3 ha4 hω3 hω1) P)) = P :=
  rotate_point_three W ω ha1 ha2 ha3 ha4 hω3 P

/-- Promotion boundary: this pays a literal point-group endomorphism, not a Hecke/L-series theorem. -/
structure JZeroCMEndomorphismBoundary : Prop where
  nativePointGroup : True
  equationPreservation : True
  additiveEndomorphism : True
  orderThree : True
  heckeCharacterConstructed : False
  ellipticLSeriesIdentified : False

end

end Integration
