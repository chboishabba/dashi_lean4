import Synthesis.MillenniumBSDActualRationalPointGroup
import Synthesis.MillenniumBSDSquareClassGroups
import Mathlib.Tactic

/-!
# Boundary cases for the actual global Kummer map

The rational point carrier now has the genuine elliptic group law.  This file
pays the formal boundary cases of global Kummer multiplicativity: identity,
negation, and inverse pairs.  After this, only the generic nonvertical
secant/tangent arithmetic remains before totalGlobalKummer is a homomorphism.
-/

namespace Synthesis.Millennium.BSD

theorem totalGlobalKummer_zero :
    totalGlobalKummer (0 : RationalProjectivePoint)
      =
    (1 : RatSquareClass × RatSquareClass) := by
  rw [rationalProjective_zero_eq_infinity]
  rfl

theorem rationalProjective_neg_affine
    (x y : ℚ)
    (h : y ^ 2 = x ^ 3 - x) :
    -(.affine x y h : RationalProjectivePoint)
      =
    .affine x (-y) (by simpa using h) := by
  apply rationalProjectivePointEquivMathlib.injective
  rw [rationalProjectivePointAddEquivMathlib.map_neg]
  simp [rationalProjectivePointEquivMathlib, cmWeierstrass]

theorem totalGlobalKummer_neg
    (P : RationalProjectivePoint) :
    totalGlobalKummer (-P) = totalGlobalKummer P := by
  cases P with
  | infinity =>
      rw [← rationalProjective_zero_eq_infinity]
      simp [totalGlobalKummer_zero]
  | affine x y h =>
      rw [rationalProjective_neg_affine x y h]
      simp only [totalGlobalKummer]
      split_ifs <;> rfl

theorem totalGlobalKummer_add_zero
    (P : RationalProjectivePoint) :
    totalGlobalKummer (P + 0)
      =
    totalGlobalKummer P * totalGlobalKummer 0 := by
  rw [add_zero, totalGlobalKummer_zero, mul_one]

theorem totalGlobalKummer_zero_add
    (P : RationalProjectivePoint) :
    totalGlobalKummer (0 + P)
      =
    totalGlobalKummer 0 * totalGlobalKummer P := by
  rw [zero_add, totalGlobalKummer_zero, one_mul]

theorem totalGlobalKummer_add_neg
    (P : RationalProjectivePoint) :
    totalGlobalKummer (P + (-P))
      =
    totalGlobalKummer P * totalGlobalKummer (-P) := by
  rw [add_neg_cancel, totalGlobalKummer_zero, totalGlobalKummer_neg]
  apply Prod.ext <;>
    simp [ratSquareClass_sq_eq_one]

def GenericGlobalKummerAdditionStatement : Prop :=
  ∀ P Q : RationalProjectivePoint,
    P ≠ 0 →
    Q ≠ 0 →
    Q ≠ -P →
    totalGlobalKummer (P + Q)
      =
    totalGlobalKummer P * totalGlobalKummer Q

def TotalGlobalKummerHomomorphismStatement : Prop :=
  ∀ P Q : RationalProjectivePoint,
    totalGlobalKummer (P + Q)
      =
    totalGlobalKummer P * totalGlobalKummer Q

theorem totalGlobalKummer_homomorphism_of_generic
    (hgeneric : GenericGlobalKummerAdditionStatement) :
    TotalGlobalKummerHomomorphismStatement := by
  intro P Q
  by_cases hP : P = 0
  · subst P
    exact totalGlobalKummer_zero_add Q
  by_cases hQ : Q = 0
  · subst Q
    exact totalGlobalKummer_add_zero P
  by_cases hQP : Q = -P
  · subst Q
    exact totalGlobalKummer_add_neg P
  exact hgeneric P Q hP hQ hQP

end Synthesis.Millennium.BSD
