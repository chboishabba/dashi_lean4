import Synthesis.MillenniumBSDCMTwoTorsionFieldGeneric
import Synthesis.MillenniumBSDMathlibLFunctionWeld
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

/-!
# Actual CM two-torsion over Qbar

This file replaces the abstract four-element E[2] carrier by the literal
mathlib elliptic point group after base change to `AlgebraicClosure ℚ`.

For the base-changed curve y²=x³-x, every point killed by 2 is proved to be
exactly O, (0,0), (1,0), or (-1,0).  Thus the remaining Galois-module step is
only to transport the coordinatewise G_Q action and observe that these four
rational points are fixed.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

abbrev RatAlgClosure := AlgebraicClosure ℚ

noncomputable abbrev cmAlgClosureWeierstrass : WeierstrassCurve RatAlgClosure :=
  cmWeierstrass.baseChange RatAlgClosure

theorem cmAlgClosure_equation_iff (x y : RatAlgClosure) :
    cmAlgClosureWeierstrass.toAffine.Equation x y ↔
      y ^ 2 = x ^ 3 - x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [cmAlgClosureWeierstrass, cmWeierstrass]
  ring_nf

inductive CMAlgClosureProjectivePoint : Type where
  | infinity
  | affine (x y : RatAlgClosure) (onCurve : y ^ 2 = x ^ 3 - x)

noncomputable def cmAlgClosurePointEquivMathlib :
    CMAlgClosureProjectivePoint ≃ cmAlgClosureWeierstrass.toAffine.Point where
  toFun
    | .infinity => .zero
    | .affine x y h =>
        WeierstrassCurve.Affine.Point.mk
          ((cmAlgClosure_equation_iff x y).mpr h)
  invFun
    | .zero => .infinity
    | .some x y h =>
        .affine x y
          ((cmAlgClosure_equation_iff x y).mp
            (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h))
  left_inv := by intro P; cases P <;> rfl
  right_inv := by intro P; cases P <;> rfl

noncomputable instance cmAlgClosurePointAddCommGroup :
    AddCommGroup CMAlgClosureProjectivePoint :=
  cmAlgClosurePointEquivMathlib.addCommGroup

noncomputable def cmAlgClosurePointAddEquivMathlib :
    CMAlgClosureProjectivePoint ≃+ cmAlgClosureWeierstrass.toAffine.Point :=
  cmAlgClosurePointEquivMathlib.addEquiv

@[simp] theorem cmAlgClosure_zero_eq_infinity :
    (0 : CMAlgClosureProjectivePoint) = .infinity := by
  apply cmAlgClosurePointEquivMathlib.injective
  simp [cmAlgClosurePointAddEquivMathlib]

theorem cmAlgClosure_neg_affine
    (x y : RatAlgClosure)
    (h : y ^ 2 = x ^ 3 - x) :
    -(.affine x y h : CMAlgClosureProjectivePoint) =
      .affine x (-y) (by simpa using h) := by
  apply cmAlgClosurePointEquivMathlib.injective
  rw [cmAlgClosurePointAddEquivMathlib.map_neg]
  simp [cmAlgClosurePointEquivMathlib, cmAlgClosureWeierstrass, cmWeierstrass]

def IsCMAlgClosureTwoTorsion (P : CMAlgClosureProjectivePoint) : Prop :=
  (2 : ℕ) • P = 0

theorem cmAlgClosure_twoTorsion_affine_selfNeg
    {x y : RatAlgClosure} (h : y ^ 2 = x ^ 3 - x)
    (ht : IsCMAlgClosureTwoTorsion (.affine x y h)) :
    (.affine x y h : CMAlgClosureProjectivePoint) =
      -(.affine x y h : CMAlgClosureProjectivePoint) := by
  unfold IsCMAlgClosureTwoTorsion at ht
  rw [two_nsmul] at ht
  exact add_eq_zero_iff_eq_neg.mp ht

theorem cmAlgClosure_twoTorsion_affine_coordinates
    {x y : RatAlgClosure} (h : y ^ 2 = x ^ 3 - x)
    (ht : IsCMAlgClosureTwoTorsion (.affine x y h)) :
    y = 0 ∧ (x = 0 ∨ x = 1 ∨ x = -1) := by
  have hself := cmAlgClosure_twoTorsion_affine_selfNeg h ht
  rw [cmAlgClosure_neg_affine] at hself
  injection hself with _ hy
  have hy0 : y = 0 := by linarith
  exact ⟨hy0, cm_affine_equation_y_zero_x_cases h hy0⟩

theorem cmAlgClosure_twoTorsion_classification
    (P : CMAlgClosureProjectivePoint) :
    IsCMAlgClosureTwoTorsion P ↔
      P = 0 ∨
      P = .affine 0 0 (by norm_num) ∨
      P = .affine 1 0 (by norm_num) ∨
      P = .affine (-1) 0 (by norm_num) := by
  constructor
  · intro ht
    cases P with
    | infinity =>
        left
        exact cmAlgClosure_zero_eq_infinity.symm
    | affine x y h =>
        rcases cmAlgClosure_twoTorsion_affine_coordinates h ht with ⟨hy,hx⟩
        rcases hx with hx | hx | hx <;> subst x <;> subst y
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · simp [IsCMAlgClosureTwoTorsion]
    · unfold IsCMAlgClosureTwoTorsion
      rw [two_nsmul, cmAlgClosure_neg_affine 0 0]
      have hself :
          (.affine (0 : RatAlgClosure) 0 (by norm_num) : CMAlgClosureProjectivePoint) =
            -(.affine (0 : RatAlgClosure) 0 (by norm_num) : CMAlgClosureProjectivePoint) := by
        rw [cmAlgClosure_neg_affine]
        simp
      exact add_eq_zero_iff_eq_neg.mpr hself
    · unfold IsCMAlgClosureTwoTorsion
      rw [two_nsmul]
      apply add_eq_zero_iff_eq_neg.mpr
      rw [cmAlgClosure_neg_affine]
      simp
    · unfold IsCMAlgClosureTwoTorsion
      rw [two_nsmul]
      apply add_eq_zero_iff_eq_neg.mpr
      rw [cmAlgClosure_neg_affine]
      simp

def cmAlgClosureTwoTorsionSubgroup : Subgroup CMAlgClosureProjectivePoint where
  carrier := {P | IsCMAlgClosureTwoTorsion P}
  one_mem' := by simp [IsCMAlgClosureTwoTorsion]
  mul_mem' := by
    intro P Q hP hQ
    change (2 : ℕ) • (P + Q) = 0
    rw [nsmul_add, hP, hQ, zero_add]
  inv_mem' := by
    intro P hP
    change (2 : ℕ) • (-P) = 0
    rw [nsmul_neg, hP, neg_zero]

theorem cmAlgClosure_E2_exact_four_points :
    ∀ P : CMAlgClosureProjectivePoint,
      P ∈ cmAlgClosureTwoTorsionSubgroup ↔
        P = 0 ∨
        P = .affine 0 0 (by norm_num) ∨
        P = .affine 1 0 (by norm_num) ∨
        P = .affine (-1) 0 (by norm_num) := by
  intro P
  exact cmAlgClosure_twoTorsion_classification P

end Synthesis.Millennium.BSD
