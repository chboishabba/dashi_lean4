import Synthesis.MillenniumBSDCMTwoTorsionGaloisModule
import Synthesis.MillenniumBSDGlobalKummerBoundaryCases
import Synthesis.MillenniumBSDGlobalKummerTorsionTriangle
import Mathlib.Tactic

/-!
# Literal rational two-torsion classification for y² = x³ - x

The abstract CM two-torsion carrier `(Z/2)^2` is now tied to the actual
rational elliptic group.  A rational projective point killed by `2` is
proved to be exactly one of

  O, (0,0), (1,0), (-1,0).

This is the rational same-object theorem underlying the trivial Galois action.
The remaining arithmetic bridge is base change to Qbar / actual E[2] followed
by the cohomological Kummer comparison.
-/

namespace Synthesis.Millennium.BSD

def IsRationalTwoTorsion (P : RationalProjectivePoint) : Prop :=
  (2 : ℕ) • P = 0

theorem rationalZeroTorsion_two_nsmul_zero :
    (2 : ℕ) • rationalZeroTorsionPoint = 0 := by
  rw [two_nsmul]
  have h1 := rational_zero_add_one_torsion
  have h2 := rational_zero_add_minusOne_torsion
  rw [← h1] at h2
  abel

theorem rationalOneTorsion_two_nsmul_zero :
    (2 : ℕ) • rationalOneTorsionPoint = 0 := by
  rw [two_nsmul]
  have h1 := rational_zero_add_one_torsion
  have h3 := rational_one_add_minusOne_torsion
  rw [← h1] at h3
  abel

theorem rationalMinusOneTorsion_two_nsmul_zero :
    (2 : ℕ) • rationalMinusOneTorsionPoint = 0 := by
  rw [two_nsmul]
  have h2 := rational_zero_add_minusOne_torsion
  have h3 := rational_one_add_minusOne_torsion
  rw [← h2] at h3
  abel

theorem rationalTwoTorsion_affine_eq_neg
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x)
    (ht : IsRationalTwoTorsion (.affine x y h)) :
    (.affine x y h : RationalProjectivePoint) =
      -(.affine x y h : RationalProjectivePoint) := by
  unfold IsRationalTwoTorsion at ht
  rw [two_nsmul] at ht
  exact add_eq_zero_iff_eq_neg.mp ht

theorem rationalTwoTorsion_affine_y_eq_zero
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x)
    (ht : IsRationalTwoTorsion (.affine x y h)) :
    y = 0 := by
  have hself := rationalTwoTorsion_affine_eq_neg h ht
  rw [rationalProjective_neg_affine] at hself
  injection hself with _ hy
  linarith

theorem rationalTwoTorsion_affine_x_cases
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x)
    (ht : IsRationalTwoTorsion (.affine x y h)) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  have hy : y = 0 := rationalTwoTorsion_affine_y_eq_zero h ht
  have hpoly : x ^ 3 - x = 0 := by
    rw [← h]
    simp [hy]
  have hfac : x * (x - 1) * (x + 1) = 0 := by
    calc
      x * (x - 1) * (x + 1) = x ^ 3 - x := by ring
      _ = 0 := hpoly
  rcases mul_eq_zero.mp hfac with hleft | hplus
  · rcases mul_eq_zero.mp hleft with hx | hx1
    · exact Or.inl hx
    · exact Or.inr (Or.inl (sub_eq_zero.mp hx1))
  · exact Or.inr (Or.inr (by linarith))

theorem rationalTwoTorsion_classification
    (P : RationalProjectivePoint) :
    IsRationalTwoTorsion P ↔
      P = 0 ∨
      P = rationalZeroTorsionPoint ∨
      P = rationalOneTorsionPoint ∨
      P = rationalMinusOneTorsionPoint := by
  constructor
  · intro ht
    cases P with
    | infinity =>
        left
        exact rationalProjective_zero_eq_infinity.symm
    | affine x y h =>
        have hy : y = 0 := rationalTwoTorsion_affine_y_eq_zero h ht
        rcases rationalTwoTorsion_affine_x_cases h ht with hx | hx | hxm1
        · subst x
          subst y
          exact Or.inr (Or.inl rfl)
        · subst x
          subst y
          exact Or.inr (Or.inr (Or.inl rfl))
        · subst x
          subst y
          exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · simp [IsRationalTwoTorsion]
    · exact rationalZeroTorsion_two_nsmul_zero
    · exact rationalOneTorsion_two_nsmul_zero
    · exact rationalMinusOneTorsion_two_nsmul_zero

def rationalTwoTorsionSubgroup : Subgroup RationalProjectivePoint where
  carrier := {P | IsRationalTwoTorsion P}
  one_mem' := by simp [IsRationalTwoTorsion]
  mul_mem' := by
    intro P Q hP hQ
    change (2 : ℕ) • (P + Q) = 0
    rw [nsmul_add, hP, hQ, zero_add]
  inv_mem' := by
    intro P hP
    change (2 : ℕ) • (-P) = 0
    rw [nsmul_neg, hP, neg_zero]

theorem mem_rationalTwoTorsionSubgroup_iff_four_points
    (P : RationalProjectivePoint) :
    P ∈ rationalTwoTorsionSubgroup ↔
      P = 0 ∨
      P = rationalZeroTorsionPoint ∨
      P = rationalOneTorsionPoint ∨
      P = rationalMinusOneTorsionPoint := by
  exact rationalTwoTorsion_classification P

theorem rationalTwoTorsion_is_full_rational_four_point_set :
    ∀ P : RationalProjectivePoint,
      P ∈ rationalTwoTorsionSubgroup →
      P = 0 ∨
      P = rationalZeroTorsionPoint ∨
      P = rationalOneTorsionPoint ∨
      P = rationalMinusOneTorsionPoint := by
  intro P hP
  exact (mem_rationalTwoTorsionSubgroup_iff_four_points P).mp hP

end Synthesis.Millennium.BSD
