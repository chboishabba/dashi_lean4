import Synthesis.MillenniumBSDLocalKummerTorsionTriangle
import Mathlib.Tactic

/-!
# Total translation laws by all three rational two-torsion points

The previous files prove:
* ordinary affine translation by T₀=(0,0), T₁=(1,0), T₋₁=(-1,0);
* the exact Klein-four addition/Kummer table on the three torsion points;
* identity and inverse Kummer laws.

This file combines those facts into translation laws valid for every
P : E(Q_p).
-/

namespace Synthesis.Millennium.BSD

theorem y_eq_zero_of_x_eq_neg_one
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (onCurve : y ^ 2 = x ^ 3 - x)
    (hx : x = -1) :
    y = 0 := by
  subst x
  norm_num at onCurve
  exact sq_eq_zero_iff.mp onCurve

theorem zeroTorsion_neg
    (p : ℕ) [Fact p.Prime] :
    -(zeroTorsionPoint p) = zeroTorsionPoint p := by
  simp [zeroTorsionPoint, padicProjective_neg_affine]

theorem oneTorsion_neg
    (p : ℕ) [Fact p.Prime] :
    -(oneTorsionPoint p) = oneTorsionPoint p := by
  simp [oneTorsionPoint, padicProjective_neg_affine]

theorem minusOneTorsion_neg
    (p : ℕ) [Fact p.Prime] :
    -(minusOneTorsionPoint p) = minusOneTorsionPoint p := by
  simp [minusOneTorsionPoint, padicProjective_neg_affine]

theorem totalLocalKummer_add_zeroTorsion
    (p : ℕ) [Fact p.Prime]
    (P : PadicProjectivePoint p) :
    totalLocalKummer p (P + zeroTorsionPoint p)
      =
    totalLocalKummer p P
      * totalLocalKummer p (zeroTorsionPoint p) := by
  cases P with
  | infinity =>
      rw [← padicProjective_zero_eq_infinity p]
      exact totalLocalKummer_zero_add p (zeroTorsionPoint p)
  | affine x y h =>
      by_cases hx0 : x = 0
      · subst x
        have hy : y = 0 :=
          y_eq_zero_of_x_eq_zero h rfl
        subst y
        rw [← zeroTorsionPoint_neg p]
        exact totalLocalKummer_add_neg p (zeroTorsionPoint p)
      by_cases hx1 : x = 1
      · subst x
        have hy : y = 0 :=
          y_eq_zero_of_x_eq_one h rfl
        subst y
        simpa [add_comm, mul_comm, zeroTorsionPoint, oneTorsionPoint]
          using totalLocalKummer_zero_add_one_torsion p
      by_cases hxm1 : x = -1
      · subst x
        have hy : y = 0 :=
          y_eq_zero_of_x_eq_neg_one h rfl
        subst y
        simpa [add_comm, mul_comm, zeroTorsionPoint, minusOneTorsionPoint]
          using totalLocalKummer_zero_add_minusOne_torsion p
      exact totalLocalKummer_add_zeroTorsion_ordinary
        h hx0 hx1 hxm1

theorem totalLocalKummer_add_oneTorsion
    (p : ℕ) [Fact p.Prime]
    (P : PadicProjectivePoint p) :
    totalLocalKummer p (P + oneTorsionPoint p)
      =
    totalLocalKummer p P
      * totalLocalKummer p (oneTorsionPoint p) := by
  cases P with
  | infinity =>
      rw [← padicProjective_zero_eq_infinity p]
      exact totalLocalKummer_zero_add p (oneTorsionPoint p)
  | affine x y h =>
      by_cases hx0 : x = 0
      · subst x
        have hy : y = 0 :=
          y_eq_zero_of_x_eq_zero h rfl
        subst y
        simpa [zeroTorsionPoint, oneTorsionPoint]
          using totalLocalKummer_zero_add_one_torsion p
      by_cases hx1 : x = 1
      · subst x
        have hy : y = 0 :=
          y_eq_zero_of_x_eq_one h rfl
        subst y
        rw [← oneTorsion_neg p]
        exact totalLocalKummer_add_neg p (oneTorsionPoint p)
      by_cases hxm1 : x = -1
      · subst x
        have hy : y = 0 :=
          y_eq_zero_of_x_eq_neg_one h rfl
        subst y
        simpa [add_comm, mul_comm, oneTorsionPoint, minusOneTorsionPoint]
          using totalLocalKummer_one_add_minusOne_torsion p
      exact totalLocalKummer_add_oneTorsion_ordinary
        h hx0 hx1 hxm1

theorem totalLocalKummer_add_minusOneTorsion
    (p : ℕ) [Fact p.Prime]
    (P : PadicProjectivePoint p) :
    totalLocalKummer p (P + minusOneTorsionPoint p)
      =
    totalLocalKummer p P
      * totalLocalKummer p (minusOneTorsionPoint p) := by
  cases P with
  | infinity =>
      rw [← padicProjective_zero_eq_infinity p]
      exact totalLocalKummer_zero_add p (minusOneTorsionPoint p)
  | affine x y h =>
      by_cases hx0 : x = 0
      · subst x
        have hy : y = 0 :=
          y_eq_zero_of_x_eq_zero h rfl
        subst y
        simpa [zeroTorsionPoint, minusOneTorsionPoint]
          using totalLocalKummer_zero_add_minusOne_torsion p
      by_cases hx1 : x = 1
      · subst x
        have hy : y = 0 :=
          y_eq_zero_of_x_eq_one h rfl
        subst y
        simpa [oneTorsionPoint, minusOneTorsionPoint]
          using totalLocalKummer_one_add_minusOne_torsion p
      by_cases hxm1 : x = -1
      · subst x
        have hy : y = 0 :=
          y_eq_zero_of_x_eq_neg_one h rfl
        subst y
        rw [← minusOneTorsion_neg p]
        exact totalLocalKummer_add_neg p (minusOneTorsionPoint p)
      exact totalLocalKummer_add_minusOneTorsion_ordinary
        h hx0 hx1 hxm1

end Synthesis.Millennium.BSD
