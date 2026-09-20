import Synthesis.MillenniumBSDGlobalKummerTorsionTranslate
import Mathlib.Tactic

/-!
# Full global Kummer homomorphism on E(Q)

This assembles the rational secant/tangent and two-torsion translation
theorems into the total global two-descent Kummer homomorphism.
-/

namespace Synthesis.Millennium.BSD

theorem rational_y_eq_zero_of_x_eq_neg_one
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hx : x = -1) : y = 0 := by
  subst x
  norm_num at h
  exact sq_eq_zero_iff.mp h

theorem rationalZeroTorsion_neg :
    -rationalZeroTorsionPoint = rationalZeroTorsionPoint := by
  simp [rationalZeroTorsionPoint, rationalProjective_neg_affine]

theorem rationalOneTorsion_neg :
    -rationalOneTorsionPoint = rationalOneTorsionPoint := by
  simp [rationalOneTorsionPoint, rationalProjective_neg_affine]

theorem totalGlobalKummer_add_zeroTorsion
    (P : RationalProjectivePoint) :
    totalGlobalKummer (P + rationalZeroTorsionPoint)
      = totalGlobalKummer P * totalGlobalKummer rationalZeroTorsionPoint := by
  cases P with
  | infinity =>
      rw [← rationalProjective_zero_eq_infinity]
      exact totalGlobalKummer_zero_add rationalZeroTorsionPoint
  | affine x y h =>
      by_cases hx0 : x = 0
      · subst x
        have hy : y = 0 := rational_y_eq_zero_of_x_eq_zero h rfl
        subst y
        rw [← rationalZeroTorsion_neg]
        exact totalGlobalKummer_add_neg rationalZeroTorsionPoint
      by_cases hx1 : x = 1
      · subst x
        have hy : y = 0 := rational_y_eq_zero_of_x_eq_one h rfl
        subst y
        simpa [add_comm, mul_comm, rationalZeroTorsionPoint, rationalOneTorsionPoint]
          using totalGlobalKummer_zero_add_one_torsion
      by_cases hxm1 : x = -1
      · subst x
        have hy : y = 0 := rational_y_eq_zero_of_x_eq_neg_one h rfl
        subst y
        simpa [add_comm, mul_comm, rationalZeroTorsionPoint,
          rationalMinusOneTorsionPoint]
          using totalGlobalKummer_zero_add_minusOne_torsion
      exact totalGlobalKummer_add_zeroTorsion_ordinary h hx0 hx1 hxm1

theorem totalGlobalKummer_add_oneTorsion
    (P : RationalProjectivePoint) :
    totalGlobalKummer (P + rationalOneTorsionPoint)
      = totalGlobalKummer P * totalGlobalKummer rationalOneTorsionPoint := by
  cases P with
  | infinity =>
      rw [← rationalProjective_zero_eq_infinity]
      exact totalGlobalKummer_zero_add rationalOneTorsionPoint
  | affine x y h =>
      by_cases hx0 : x = 0
      · subst x
        have hy : y = 0 := rational_y_eq_zero_of_x_eq_zero h rfl
        subst y
        simpa [rationalZeroTorsionPoint, rationalOneTorsionPoint]
          using totalGlobalKummer_zero_add_one_torsion
      by_cases hx1 : x = 1
      · subst x
        have hy : y = 0 := rational_y_eq_zero_of_x_eq_one h rfl
        subst y
        rw [← rationalOneTorsion_neg]
        exact totalGlobalKummer_add_neg rationalOneTorsionPoint
      by_cases hxm1 : x = -1
      · subst x
        have hy : y = 0 := rational_y_eq_zero_of_x_eq_neg_one h rfl
        subst y
        simpa [add_comm, mul_comm, rationalOneTorsionPoint,
          rationalMinusOneTorsionPoint]
          using totalGlobalKummer_one_add_minusOne_torsion
      exact totalGlobalKummer_add_oneTorsion_ordinary h hx0 hx1 hxm1

theorem totalGlobalKummer_of_sum_torsion
    (T : RationalProjectivePoint)
    (htrans : ∀ P : RationalProjectivePoint,
      totalGlobalKummer (P + T) = totalGlobalKummer P * totalGlobalKummer T)
    (P Q : RationalProjectivePoint)
    (hsum : P + Q = T) :
    totalGlobalKummer (P + Q)
      = totalGlobalKummer P * totalGlobalKummer Q := by
  have hQ : Q = -P + T := by
    apply add_left_cancel P
    calc
      P + Q = T := hsum
      _ = P + (-P + T) := by abel
  rw [hsum, hQ, htrans, totalGlobalKummer_neg]
  apply Prod.ext <;>
    simp [mul_assoc, ratSquareClass_sq_eq_one]

theorem totalGlobalKummer_of_sum_zeroTorsion
    (P Q : RationalProjectivePoint)
    (hsum : P + Q = rationalZeroTorsionPoint) :
    totalGlobalKummer (P + Q)
      = totalGlobalKummer P * totalGlobalKummer Q :=
  totalGlobalKummer_of_sum_torsion rationalZeroTorsionPoint
    totalGlobalKummer_add_zeroTorsion P Q hsum

theorem totalGlobalKummer_of_sum_oneTorsion
    (P Q : RationalProjectivePoint)
    (hsum : P + Q = rationalOneTorsionPoint) :
    totalGlobalKummer (P + Q)
      = totalGlobalKummer P * totalGlobalKummer Q :=
  totalGlobalKummer_of_sum_torsion rationalOneTorsionPoint
    totalGlobalKummer_add_oneTorsion P Q hsum

theorem totalGlobalKummer_ordinary_inputs
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx₁0 : x₁ ≠ 0) (hx₁1 : x₁ ≠ 1)
    (hx₂0 : x₂ ≠ 0) (hx₂1 : x₂ ≠ 1)
    (hQnegP :
      (.affine x₂ y₂ h₂ : RationalProjectivePoint)
        ≠ -(.affine x₁ y₁ h₁ : RationalProjectivePoint)) :
    totalGlobalKummer
      ((.affine x₁ y₁ h₁ : RationalProjectivePoint) + .affine x₂ y₂ h₂)
      = totalGlobalKummer (.affine x₁ y₁ h₁)
          * totalGlobalKummer (.affine x₂ y₂ h₂) := by
  let P : RationalProjectivePoint := .affine x₁ y₁ h₁
  let Q : RationalProjectivePoint := .affine x₂ y₂ h₂
  cases hR : P + Q with
  | infinity =>
      exfalso
      apply hQnegP
      apply add_left_cancel P
      calc
        P + Q = (.infinity : RationalProjectivePoint) := hR
        _ = 0 := rationalProjective_zero_eq_infinity.symm
        _ = P + (-P) := (add_neg_cancel P).symm
  | affine xR yR hcurveR =>
      by_cases hxR0 : xR = 0
      · have hyR : yR = 0 := rational_y_eq_zero_of_x_eq_zero hcurveR hxR0
        have hsumT : P + Q = rationalZeroTorsionPoint := by
          rw [hR]
          subst xR
          subst yR
          rfl
        exact totalGlobalKummer_of_sum_zeroTorsion P Q hsumT
      by_cases hxR1 : xR = 1
      · have hyR : yR = 0 := rational_y_eq_zero_of_x_eq_one hcurveR hxR1
        have hsumT : P + Q = rationalOneTorsionPoint := by
          rw [hR]
          subst xR
          subst yR
          rfl
        exact totalGlobalKummer_of_sum_oneTorsion P Q hsumT
      apply totalGlobalKummer_affine_ordinary
        h₁ h₂ hx₁0 hx₁1 hx₂0 hx₂1 hQnegP
      exact ⟨xR, yR, hcurveR, hR, hxR0, hxR1⟩

theorem totalGlobalKummer_generic : GenericGlobalKummerAdditionStatement := by
  intro P Q hP hQ hQnegP
  cases P with
  | infinity =>
      exact (hP rationalProjective_zero_eq_infinity.symm).elim
  | affine x₁ y₁ h₁ =>
      cases Q with
      | infinity =>
          exact (hQ rationalProjective_zero_eq_infinity.symm).elim
      | affine x₂ y₂ h₂ =>
          by_cases hx₁0 : x₁ = 0
          · subst x₁
            have hy₁ : y₁ = 0 := rational_y_eq_zero_of_x_eq_zero h₁ rfl
            subst y₁
            simpa [rationalZeroTorsionPoint, add_comm, mul_comm]
              using totalGlobalKummer_add_zeroTorsion (.affine x₂ y₂ h₂)
          by_cases hx₁1 : x₁ = 1
          · subst x₁
            have hy₁ : y₁ = 0 := rational_y_eq_zero_of_x_eq_one h₁ rfl
            subst y₁
            simpa [rationalOneTorsionPoint, add_comm, mul_comm]
              using totalGlobalKummer_add_oneTorsion (.affine x₂ y₂ h₂)
          by_cases hx₂0 : x₂ = 0
          · subst x₂
            have hy₂ : y₂ = 0 := rational_y_eq_zero_of_x_eq_zero h₂ rfl
            subst y₂
            simpa [rationalZeroTorsionPoint]
              using totalGlobalKummer_add_zeroTorsion (.affine x₁ y₁ h₁)
          by_cases hx₂1 : x₂ = 1
          · subst x₂
            have hy₂ : y₂ = 0 := rational_y_eq_zero_of_x_eq_one h₂ rfl
            subst y₂
            simpa [rationalOneTorsionPoint]
              using totalGlobalKummer_add_oneTorsion (.affine x₁ y₁ h₁)
          exact totalGlobalKummer_ordinary_inputs
            h₁ h₂ hx₁0 hx₁1 hx₂0 hx₂1 hQnegP

theorem totalGlobalKummer_homomorphism :
    TotalGlobalKummerHomomorphismStatement :=
  totalGlobalKummer_homomorphism_of_generic totalGlobalKummer_generic

end Synthesis.Millennium.BSD
