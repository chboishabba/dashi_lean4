import Mathlib.Tactic

/-!
# BSD: exact real affine-locus exclusion for y^2=x^3-x

This is a proof on the literal polynomial equation over the real field.
It pays a genuine preliminary archimedean geometry fact without claiming
an archimedean cohomological Kummer map or the dimension of its image.

Real solutions have x in [-1,0] union [1,infinity].  In particular,
there are no real affine points with x<-1 or 0<x<1.  The two real
components and E(R)/2E(R) still require the actual elliptic group
topology and remain open.
-/

namespace Synthesis.Millennium.BSD

/-- Real points of the original selected CM curve cannot have x below -1,
nor strictly between 0 and 1. No external elliptic-point carrier is assumed. -/
theorem cmRealAffine_x_locus
    (x y : ℝ)
    (hcurve : y ^ 2 = x ^ 3 - x) :
    (-1 ≤ x ∧ x ≤ 0) ∨ 1 ≤ x := by
  by_cases hLow : x < -1
  · have hnegX : x < 0 := by linarith
    have hnegXMinus : x - 1 < 0 := by linarith
    have hnegXPlus : x + 1 < 0 := by linarith
    have hpos : 0 < x * (x - 1) :=
      mul_pos_of_neg_of_neg hnegX hnegXMinus
    have hnegative : x * (x - 1) * (x + 1) < 0 :=
      mul_neg_of_pos_of_neg hpos hnegXPlus
    have hpoly : x ^ 3 - x < 0 := by
      calc
        x ^ 3 - x = x * (x - 1) * (x + 1) := by ring
        _ < 0 := hnegative
    nlinarith [sq_nonneg y]
  · by_cases hNonpos : x ≤ 0
    · exact Or.inl ⟨by linarith, hNonpos⟩
    · by_cases hHigh : 1 ≤ x
      · exact Or.inr hHigh
      · have hposX : 0 < x := by linarith
        have hnegMinus : x - 1 < 0 := by linarith
        have hposPlus : 0 < x + 1 := by linarith
        have hnegProd : x * (x - 1) < 0 :=
          mul_neg_of_pos_of_neg hposX hnegMinus
        have hnegative : x * (x - 1) * (x + 1) < 0 :=
          mul_neg_of_neg_of_pos hnegProd hposPlus
        have hpoly : x ^ 3 - x < 0 := by
          calc
            x ^ 3 - x = x * (x - 1) * (x + 1) := by ring
            _ < 0 := hnegative
        nlinarith [sq_nonneg y]

/-- Explicit exclusion of the interval between 0 and 1. -/
theorem cmRealAffine_no_x_between_zero_one
    (x y : ℝ)
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx0 : 0 < x)
    (hx1 : x < 1) : False := by
  rcases cmRealAffine_x_locus x y hcurve with h | h
  · linarith [h.2]
  · linarith

/-- Explicit exclusion of all x below -1. -/
theorem cmRealAffine_no_x_below_minus_one
    (x y : ℝ)
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hx : x < -1) : False := by
  rcases cmRealAffine_x_locus x y hcurve with h | h
  · linarith [h.1]
  · linarith

end Synthesis.Millennium.BSD
