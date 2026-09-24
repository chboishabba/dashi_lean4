import Synthesis.MillenniumBSDLocalKummerSecantDispatch
import Synthesis.MillenniumBSDLocalKummerTangentDispatch
import Mathlib.Tactic

/-!
# Ordinary affine local Kummer multiplicativity: secant or tangent

For ordinary affine points P,Q on y²=x³-x, assume Q ≠ -P and that P,Q,P+Q
all stay off the exceptional x=0,1 Kummer branches.

Then δ(P+Q)=δ(P)δ(Q).

The proof is exactly the classical dichotomy:
* x(P) ≠ x(Q): use the actual secant dispatch theorem;
* x(P) = x(Q): the curve equation gives y(Q)=±y(P); the inverse sign is
  excluded by Q ≠ -P, so Q=P and the tangent dispatch theorem applies.
-/

namespace Synthesis.Millennium.BSD

theorem affine_y_eq_or_eq_neg_of_same_x
    {p : ℕ} [Fact p.Prime]
    {x y₁ y₂ : ℚ_[p]}
    (h₁ : y₁ ^ 2 = x ^ 3 - x)
    (h₂ : y₂ ^ 2 = x ^ 3 - x) :
    y₁ = y₂ ∨ y₁ = -y₂ := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  calc
    y₁ ^ 2 = x ^ 3 - x := h₁
    _ = y₂ ^ 2 := h₂.symm

theorem ordinary_same_x_noninverse_forces_same_y
    {p : ℕ} [Fact p.Prime]
    {x y₁ y₂ : ℚ_[p]}
    (h₁ : y₁ ^ 2 = x ^ 3 - x)
    (h₂ : y₂ ^ 2 = x ^ 3 - x)
    (hQnegP :
      (.affine x y₂ h₂ : PadicProjectivePoint p)
        ≠ -(.affine x y₁ h₁ : PadicProjectivePoint p)) :
    y₁ = y₂ := by
  rcases affine_y_eq_or_eq_neg_of_same_x h₁ h₂ with h | h
  · exact h
  · exfalso
    apply hQnegP
    rw [padicProjective_neg_affine p x y₁ h₁]
    congr
    exact h.symm

theorem ordinary_same_x_noninverse_y_ne_zero
    {p : ℕ} [Fact p.Prime]
    {x y₁ y₂ : ℚ_[p]}
    (h₁ : y₁ ^ 2 = x ^ 3 - x)
    (h₂ : y₂ ^ 2 = x ^ 3 - x)
    (hQnegP :
      (.affine x y₂ h₂ : PadicProjectivePoint p)
        ≠ -(.affine x y₁ h₁ : PadicProjectivePoint p)) :
    y₁ ≠ 0 := by
  have hy := ordinary_same_x_noninverse_forces_same_y h₁ h₂ hQnegP
  intro hy0
  apply hQnegP
  rw [padicProjective_neg_affine p x y₁ h₁]
  congr
  calc
    y₂ = y₁ := hy.symm
    _ = 0 := hy0
    _ = -y₁ := by simp [hy0]

theorem totalLocalKummer_affine_ordinary
    {p : ℕ} [Fact p.Prime]
    {x₁ y₁ x₂ y₂ : ℚ_[p]}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx₁0 : x₁ ≠ 0) (hx₁1 : x₁ ≠ 1)
    (hx₂0 : x₂ ≠ 0) (hx₂1 : x₂ ≠ 1)
    (hQnegP :
      (.affine x₂ y₂ h₂ : PadicProjectivePoint p)
        ≠ -(.affine x₁ y₁ h₁ : PadicProjectivePoint p))
    (hSumOrd :
      ∃ xR yR hR,
        (.affine x₁ y₁ h₁ : PadicProjectivePoint p)
            + .affine x₂ y₂ h₂
          = .affine xR yR hR
        ∧ xR ≠ 0 ∧ xR ≠ 1) :
    totalLocalKummer p
      ((.affine x₁ y₁ h₁ : PadicProjectivePoint p)
        + .affine x₂ y₂ h₂)
      =
    totalLocalKummer p (.affine x₁ y₁ h₁)
      * totalLocalKummer p (.affine x₂ y₂ h₂) := by
  by_cases hx : x₁ = x₂
  · subst x₂
    have hy : y₁ = y₂ :=
      ordinary_same_x_noninverse_forces_same_y h₁ h₂ hQnegP
    subst y₂
    have hy0 : y₁ ≠ 0 :=
      ordinary_same_x_noninverse_y_ne_zero h₁ h₁ hQnegP
    rcases hSumOrd with ⟨xR, yR, hR, hsum, hxR0, hxR1⟩
    have htan :=
      padicProjective_tangent_double h₁ hy0
    have hxEq :
        tangentSumX x₁ y₁ = xR := by
      rw [htan] at hsum
      cases hsum
      rfl
    have hxT0 : tangentSumX x₁ y₁ ≠ 0 := by
      rw [hxEq]
      exact hxR0
    have hxT1 : tangentSumX x₁ y₁ ≠ 1 := by
      rw [hxEq]
      exact hxR1
    exact totalLocalKummer_tangent_ordinary
      h₁ hy0 hx₁0 hx₁1 hxT0 hxT1
  · have hsec :=
      padicProjective_secant_add h₁ h₂ hx
    rcases hSumOrd with ⟨xR, yR, hR, hsum, hxR0, hxR1⟩
    have hxEq :
        secantSumX x₁ y₁ x₂ y₂ = xR := by
      rw [hsec] at hsum
      cases hsum
      rfl
    have hxS0 : secantSumX x₁ y₁ x₂ y₂ ≠ 0 := by
      rw [hxEq]
      exact hxR0
    have hxS1 : secantSumX x₁ y₁ x₂ y₂ ≠ 1 := by
      rw [hxEq]
      exact hxR1
    exact totalLocalKummer_secant_ordinary
      h₁ h₂ hx
      hx₁0 hx₁1 hx₂0 hx₂1
      hxS0 hxS1

end Synthesis.Millennium.BSD
