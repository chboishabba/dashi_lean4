import Synthesis.MillenniumBSDActualLocalPointGroup
import Mathlib.Tactic

/-!
# Identity and inversion laws for the total local Kummer map

After transferring the actual elliptic group law onto `PadicProjectivePoint`,
we can discharge the formal group-theoretic boundary cases of Kummer
multiplicativity.

The identity maps to the multiplicative identity.  Negating an elliptic point
does not change its x-coordinate, hence does not change either Kummer square
class; this remains true on the exceptional x=0 and x=1 branches.

Therefore the homomorphism theorem is already paid for pairs involving the
identity and for inverse pairs.  The remaining theorem is the generic
chord/tangent addition identity.
-/

namespace Synthesis.Millennium.BSD

theorem totalLocalKummer_zero
    (p : ℕ) [Fact p.Prime] :
    totalLocalKummer p (0 : PadicProjectivePoint p)
      =
    (1 : PadicSquareClass p × PadicSquareClass p) := by
  rw [padicProjective_zero_eq_infinity]
  exact localInfinityKummer_eq_one p

theorem padicProjective_neg_affine
    (p : ℕ) [Fact p.Prime]
    (x y : ℚ_[p])
    (h : y ^ 2 = x ^ 3 - x) :
    -(.affine x y h : PadicProjectivePoint p)
      =
    .affine x (-y) (by simpa using h) := by
  apply (padicProjectivePointEquivMathlib p).injective
  rw [(padicProjectivePointAddEquivMathlib p).map_neg]
  simp [padicProjectivePointEquivMathlib,
    cmPadicWeierstrass, cmWeierstrass]

theorem totalLocalKummer_neg
    (p : ℕ) [Fact p.Prime]
    (P : PadicProjectivePoint p) :
    totalLocalKummer p (-P) =
      totalLocalKummer p P := by
  cases P with
  | infinity =>
      rw [← padicProjective_zero_eq_infinity p]
      simp [totalLocalKummer_zero]
  | affine x y h =>
      rw [padicProjective_neg_affine p x y h]
      simp only [totalLocalKummer]
      split_ifs <;> rfl

theorem totalLocalKummer_add_zero
    (p : ℕ) [Fact p.Prime]
    (P : PadicProjectivePoint p) :
    totalLocalKummer p (P + 0)
      =
    totalLocalKummer p P * totalLocalKummer p 0 := by
  rw [add_zero, totalLocalKummer_zero, mul_one]

theorem totalLocalKummer_zero_add
    (p : ℕ) [Fact p.Prime]
    (P : PadicProjectivePoint p) :
    totalLocalKummer p (0 + P)
      =
    totalLocalKummer p 0 * totalLocalKummer p P := by
  rw [zero_add, totalLocalKummer_zero, one_mul]

theorem totalLocalKummer_add_neg
    (p : ℕ) [Fact p.Prime]
    (P : PadicProjectivePoint p) :
    totalLocalKummer p (P + (-P))
      =
    totalLocalKummer p P * totalLocalKummer p (-P) := by
  rw [add_neg_cancel, totalLocalKummer_zero,
      totalLocalKummer_neg]
  apply Prod.ext <;>
    simp [padicSquareClass_sq_eq_one]

def GenericLocalKummerAdditionStatement
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ P Q : PadicProjectivePoint p,
    P ≠ 0 →
    Q ≠ 0 →
    Q ≠ -P →
    totalLocalKummer p (P + Q)
      =
    totalLocalKummer p P * totalLocalKummer p Q

theorem totalLocalKummer_homomorphism_of_generic
    (p : ℕ) [Fact p.Prime]
    (hgeneric : GenericLocalKummerAdditionStatement p) :
    TotalLocalKummerHomomorphismStatement p := by
  intro P Q
  by_cases hP : P = 0
  · subst P
    exact totalLocalKummer_zero_add p Q
  by_cases hQ : Q = 0
  · subst Q
    exact totalLocalKummer_add_zero p P
  by_cases hQP : Q = -P
  · subst Q
    exact totalLocalKummer_add_neg p P
  exact hgeneric P Q hP hQ hQP

theorem localKummerMulClosed_of_generic
    (p : ℕ) [Fact p.Prime]
    (hgeneric : GenericLocalKummerAdditionStatement p) :
    LocalKummerMulClosed p :=
  localKummerMulClosed_of_total_homomorphism p
    (totalLocalKummer_homomorphism_of_generic p hgeneric)

end Synthesis.Millennium.BSD
