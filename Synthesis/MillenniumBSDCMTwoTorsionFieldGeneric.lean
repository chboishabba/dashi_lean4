import Synthesis.MillenniumBSDRationalTwoTorsionEquiv
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-!
# Field-generic coordinate classification of CM two-torsion

For the curve y² = x³ - x over any characteristic-zero field, an affine
point fixed by the usual elliptic negation has y = 0, hence
x(x-1)(x+1)=0 and x is 0, 1, or -1.

This is deliberately stated below the point-group API, so it applies unchanged
to Q, algebraic closures, and separable closures.  The remaining base-change
task is only to connect `[2]P=0` in mathlib's actual point group to
`P=-P`, whose affine negation is `(x,-y)` for this short Weierstrass model.
-/

namespace Synthesis.Millennium.BSD

theorem cm_affine_self_neg_y_eq_zero
    {K : Type*} [Field K] [CharZero K]
    {y : K} (hneg : y = -y) :
    y = 0 := by
  have htwo : (2 : K) * y = 0 := by
    nlinarith
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem cm_affine_equation_y_zero_x_cases
    {K : Type*} [Field K] [CharZero K]
    {x y : K}
    (heq : y ^ 2 = x ^ 3 - x)
    (hy : y = 0) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  have hpoly : x ^ 3 - x = 0 := by
    rw [← heq, hy]
    simp
  have hfac : x * (x - 1) * (x + 1) = 0 := by
    calc
      x * (x - 1) * (x + 1) = x ^ 3 - x := by ring
      _ = 0 := hpoly
  rcases mul_eq_zero.mp hfac with hleft | hplus
  · rcases mul_eq_zero.mp hleft with hx | hx1
    · exact Or.inl hx
    · exact Or.inr (Or.inl (sub_eq_zero.mp hx1))
  · exact Or.inr (Or.inr (by linarith))

theorem cm_affine_self_neg_coordinates
    {K : Type*} [Field K] [CharZero K]
    {x y : K}
    (heq : y ^ 2 = x ^ 3 - x)
    (hneg : y = -y) :
    y = 0 ∧ (x = 0 ∨ x = 1 ∨ x = -1) := by
  have hy := cm_affine_self_neg_y_eq_zero hneg
  exact ⟨hy, cm_affine_equation_y_zero_x_cases heq hy⟩

theorem cm_affine_two_torsion_coordinate_cardinality_bound
    {K : Type*} [Field K] [CharZero K]
    {x y : K}
    (heq : y ^ 2 = x ^ 3 - x)
    (hneg : y = -y) :
    (x,y) = (0,0) ∨ (x,y) = (1,0) ∨ (x,y) = (-1,0) := by
  rcases cm_affine_self_neg_coordinates heq hneg with ⟨hy,hx⟩
  rcases hx with hx | hx | hx <;> subst x <;> subst y
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end Synthesis.Millennium.BSD
