import Integration.RationalCayleyDicksonOctonion
import Mathlib

/-!
# Native rational octonion anisotropic norm / zero-divisor max-cut

The repository's literal rational octonion norm is the positive eight-square
form.  Over `ℚ` this immediately gives a genuinely theorem-bearing original-form
invariant: the norm is anisotropic.

Combined with the already-proved multiplicativity of `normSq`, anisotropy rules
out zero divisors on the same native octonion carrier.

This is DASHI-owned mathematics on the literal repo object.  It does **not** by
itself identify the automorphism group of the associated Albert algebra with a
named rational `F4` form, nor does it replace the classical Albert/F4/E6
classification theorem.
-/

namespace Integration.RationalCayleyDicksonOctonion.RationalOctonion

/-- The native rational octonion norm is nonnegative. -/
theorem normSq_nonneg (x : RationalOctonion) : 0 ≤ normSq x := by
  rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
  simp [normSq, RationalQuaternion.normSq]
  positivity

/-- Exact anisotropy of the native positive eight-square norm over `ℚ`. -/
theorem normSq_eq_zero_iff (x : RationalOctonion) : normSq x = 0 ↔ x = 0 := by
  rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
  constructor
  · intro h
    simp [normSq, RationalQuaternion.normSq] at h
    have ha0 : a0 = 0 := by
      nlinarith [sq_nonneg a0, sq_nonneg a1, sq_nonneg a2, sq_nonneg a3,
        sq_nonneg b0, sq_nonneg b1, sq_nonneg b2, sq_nonneg b3]
    have ha1 : a1 = 0 := by
      nlinarith [sq_nonneg a0, sq_nonneg a1, sq_nonneg a2, sq_nonneg a3,
        sq_nonneg b0, sq_nonneg b1, sq_nonneg b2, sq_nonneg b3]
    have ha2 : a2 = 0 := by
      nlinarith [sq_nonneg a0, sq_nonneg a1, sq_nonneg a2, sq_nonneg a3,
        sq_nonneg b0, sq_nonneg b1, sq_nonneg b2, sq_nonneg b3]
    have ha3 : a3 = 0 := by
      nlinarith [sq_nonneg a0, sq_nonneg a1, sq_nonneg a2, sq_nonneg a3,
        sq_nonneg b0, sq_nonneg b1, sq_nonneg b2, sq_nonneg b3]
    have hb0 : b0 = 0 := by
      nlinarith [sq_nonneg a0, sq_nonneg a1, sq_nonneg a2, sq_nonneg a3,
        sq_nonneg b0, sq_nonneg b1, sq_nonneg b2, sq_nonneg b3]
    have hb1 : b1 = 0 := by
      nlinarith [sq_nonneg a0, sq_nonneg a1, sq_nonneg a2, sq_nonneg a3,
        sq_nonneg b0, sq_nonneg b1, sq_nonneg b2, sq_nonneg b3]
    have hb2 : b2 = 0 := by
      nlinarith [sq_nonneg a0, sq_nonneg a1, sq_nonneg a2, sq_nonneg a3,
        sq_nonneg b0, sq_nonneg b1, sq_nonneg b2, sq_nonneg b3]
    have hb3 : b3 = 0 := by
      nlinarith [sq_nonneg a0, sq_nonneg a1, sq_nonneg a2, sq_nonneg a3,
        sq_nonneg b0, sq_nonneg b1, sq_nonneg b2, sq_nonneg b3]
    subst a0; subst a1; subst a2; subst a3
    subst b0; subst b1; subst b2; subst b3
    rfl
  · rintro rfl
    norm_num [normSq, RationalQuaternion.normSq]

/-- A nonzero native rational octonion has nonzero norm. -/
theorem normSq_ne_zero {x : RationalOctonion} (hx : x ≠ 0) : normSq x ≠ 0 := by
  intro hn
  exact hx ((normSq_eq_zero_iff x).mp hn)

/-- Multiplicativity plus anisotropy eliminates zero divisors. -/
theorem mul_eq_zero {x y : RationalOctonion} (hxy : x * y = 0) : x = 0 ∨ y = 0 := by
  have hnorm : normSq x * normSq y = 0 := by
    rw [← normSq_mul x y, hxy]
    norm_num [normSq, RationalQuaternion.normSq]
  rcases _root_.mul_eq_zero.mp hnorm with hx | hy
  · exact Or.inl ((normSq_eq_zero_iff x).mp hx)
  · exact Or.inr ((normSq_eq_zero_iff y).mp hy)

/-- Product of two nonzero native rational octonions is nonzero. -/
theorem mul_ne_zero {x y : RationalOctonion} (hx : x ≠ 0) (hy : y ≠ 0) : x * y ≠ 0 := by
  intro hxy
  rcases mul_eq_zero hxy with hx0 | hy0
  · exact hx hx0
  · exact hy hy0

structure Boundary where
  positiveEightSquareNormPaid : Bool
  normAnisotropyPaid : Bool
  multiplicativeNormPaidUpstream : Bool
  noZeroDivisorsPaid : Bool
  originalQFormGroupClassificationPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  positiveEightSquareNormPaid := true
  normAnisotropyPaid := true
  multiplicativeNormPaidUpstream := true
  noZeroDivisorsPaid := true
  originalQFormGroupClassificationPaid := false

end Integration.RationalCayleyDicksonOctonion.RationalOctonion
