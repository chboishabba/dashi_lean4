import Synthesis.MillenniumBSDLocalKummerOrdinaryHom
import Synthesis.MillenniumBSDLocalKummerTorsionTranslateAll
import Mathlib.Tactic

/-!
# The total local two-descent Kummer map is a homomorphism

This closes the classical local arithmetic theorem for E : y²=x³-x over Q_p.

All ingredients are literal:
* the domain is the actual transported elliptic AddCommGroup;
* the codomain is (Q_p^*/Q_p^{*2})² with its actual quotient group law;
* secant and tangent formulas are dispatched through mathlib's point addition;
* all three rational two-torsion translations are proved on every local point.

The only remaining exceptional-output cases are handled group-theoretically:
if P+Q=T, then Q=-P+T.  Translation by T, invariance under negation, and
exponent two of square classes give δ(P+Q)=δ(P)δ(Q).
-/

namespace Synthesis.Millennium.BSD

theorem totalLocalKummer_of_sum_torsion
    (p : ℕ) [Fact p.Prime]
    (T : PadicProjectivePoint p)
    (htrans :
      ∀ P : PadicProjectivePoint p,
        totalLocalKummer p (P + T)
          =
        totalLocalKummer p P * totalLocalKummer p T)
    (P Q : PadicProjectivePoint p)
    (hsum : P + Q = T) :
    totalLocalKummer p (P + Q)
      =
    totalLocalKummer p P * totalLocalKummer p Q := by
  have hQ : Q = -P + T := by
    apply add_left_cancel P
    calc
      P + Q = T := hsum
      _ = P + (-P + T) := by abel
  rw [hsum, hQ, htrans, totalLocalKummer_neg]
  apply Prod.ext <;>
    simp [mul_assoc, padicSquareClass_sq_eq_one]

theorem totalLocalKummer_of_sum_zeroTorsion
    (p : ℕ) [Fact p.Prime]
    (P Q : PadicProjectivePoint p)
    (hsum : P + Q = zeroTorsionPoint p) :
    totalLocalKummer p (P + Q)
      =
    totalLocalKummer p P * totalLocalKummer p Q :=
  totalLocalKummer_of_sum_torsion p
    (zeroTorsionPoint p)
    (totalLocalKummer_add_zeroTorsion p)
    P Q hsum

theorem totalLocalKummer_of_sum_oneTorsion
    (p : ℕ) [Fact p.Prime]
    (P Q : PadicProjectivePoint p)
    (hsum : P + Q = oneTorsionPoint p) :
    totalLocalKummer p (P + Q)
      =
    totalLocalKummer p P * totalLocalKummer p Q :=
  totalLocalKummer_of_sum_torsion p
    (oneTorsionPoint p)
    (totalLocalKummer_add_oneTorsion p)
    P Q hsum

theorem totalLocalKummer_ordinary_inputs
    {p : ℕ} [Fact p.Prime]
    {x₁ y₁ x₂ y₂ : ℚ_[p]}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx₁0 : x₁ ≠ 0) (hx₁1 : x₁ ≠ 1)
    (hx₂0 : x₂ ≠ 0) (hx₂1 : x₂ ≠ 1)
    (hQnegP :
      (.affine x₂ y₂ h₂ : PadicProjectivePoint p)
        ≠ -(.affine x₁ y₁ h₁ : PadicProjectivePoint p)) :
    totalLocalKummer p
      ((.affine x₁ y₁ h₁ : PadicProjectivePoint p)
        + .affine x₂ y₂ h₂)
      =
    totalLocalKummer p (.affine x₁ y₁ h₁)
      * totalLocalKummer p (.affine x₂ y₂ h₂) := by
  let P : PadicProjectivePoint p := .affine x₁ y₁ h₁
  let Q : PadicProjectivePoint p := .affine x₂ y₂ h₂
  cases hR : P + Q with
  | infinity =>
      exfalso
      apply hQnegP
      apply add_left_cancel P
      calc
        P + Q = (.infinity : PadicProjectivePoint p) := hR
        _ = 0 := (padicProjective_zero_eq_infinity p).symm
        _ = P + (-P) := (add_neg_cancel P).symm
  | affine xR yR hcurveR =>
      by_cases hxR0 : xR = 0
      · have hyR : yR = 0 :=
          y_eq_zero_of_x_eq_zero hcurveR hxR0
        have hsumT : P + Q = zeroTorsionPoint p := by
          rw [hR]
          subst xR
          subst yR
          rfl
        exact totalLocalKummer_of_sum_zeroTorsion p P Q hsumT
      by_cases hxR1 : xR = 1
      · have hyR : yR = 0 :=
          y_eq_zero_of_x_eq_one hcurveR hxR1
        have hsumT : P + Q = oneTorsionPoint p := by
          rw [hR]
          subst xR
          subst yR
          rfl
        exact totalLocalKummer_of_sum_oneTorsion p P Q hsumT
      apply totalLocalKummer_affine_ordinary
        h₁ h₂ hx₁0 hx₁1 hx₂0 hx₂1 hQnegP
      exact ⟨xR, yR, hcurveR, hR, hxR0, hxR1⟩

theorem totalLocalKummer_generic
    (p : ℕ) [Fact p.Prime] :
    GenericLocalKummerAdditionStatement p := by
  intro P Q hP hQ hQnegP
  cases P with
  | infinity =>
      exact (hP (padicProjective_zero_eq_infinity p).symm).elim
  | affine x₁ y₁ h₁ =>
      cases Q with
      | infinity =>
          exact (hQ (padicProjective_zero_eq_infinity p).symm).elim
      | affine x₂ y₂ h₂ =>
          by_cases hx₁0 : x₁ = 0
          · subst x₁
            have hy₁ : y₁ = 0 :=
              y_eq_zero_of_x_eq_zero h₁ rfl
            subst y₁
            simpa [zeroTorsionPoint, add_comm, mul_comm]
              using totalLocalKummer_add_zeroTorsion p
                (.affine x₂ y₂ h₂)
          by_cases hx₁1 : x₁ = 1
          · subst x₁
            have hy₁ : y₁ = 0 :=
              y_eq_zero_of_x_eq_one h₁ rfl
            subst y₁
            simpa [oneTorsionPoint, add_comm, mul_comm]
              using totalLocalKummer_add_oneTorsion p
                (.affine x₂ y₂ h₂)
          by_cases hx₂0 : x₂ = 0
          · subst x₂
            have hy₂ : y₂ = 0 :=
              y_eq_zero_of_x_eq_zero h₂ rfl
            subst y₂
            simpa [zeroTorsionPoint]
              using totalLocalKummer_add_zeroTorsion p
                (.affine x₁ y₁ h₁)
          by_cases hx₂1 : x₂ = 1
          · subst x₂
            have hy₂ : y₂ = 0 :=
              y_eq_zero_of_x_eq_one h₂ rfl
            subst y₂
            simpa [oneTorsionPoint]
              using totalLocalKummer_add_oneTorsion p
                (.affine x₁ y₁ h₁)
          exact totalLocalKummer_ordinary_inputs
            h₁ h₂ hx₁0 hx₁1 hx₂0 hx₂1 hQnegP

theorem totalLocalKummer_homomorphism
    (p : ℕ) [Fact p.Prime] :
    TotalLocalKummerHomomorphismStatement p :=
  totalLocalKummer_homomorphism_of_generic p
    (totalLocalKummer_generic p)

theorem localKummerImage_mul_closed
    (p : ℕ) [Fact p.Prime] :
    LocalKummerMulClosed p :=
  localKummerMulClosed_of_total_homomorphism p
    (totalLocalKummer_homomorphism p)

def localKummerImageSubgroup
    (p : ℕ) [Fact p.Prime] :
    Subgroup (PadicSquareClass p × PadicSquareClass p) where
  carrier := LocalKummerImage p
  one_mem' := by
    refine ⟨0, ?_⟩
    exact totalLocalKummer_zero p
  mul_mem' := localKummerImage_mul_closed p
  inv_mem' := by
    intro a ha
    rcases ha with ⟨P, rfl⟩
    refine ⟨-P, ?_⟩
    rw [totalLocalKummer_neg]
    apply Prod.ext <;>
      exact padicSquareClass_inv_eq_self p _

end Synthesis.Millennium.BSD
