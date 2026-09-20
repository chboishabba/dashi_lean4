import Synthesis.MillenniumBSDCMPrimeClassification
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic

/-!
# Quartic character and Jacobi norm at split CM primes

For p ≡ 1 mod 4, the finite field F_p admits a multiplicative character χ
of exact order four with values in C.  Its square is the unique quadratic
character, and the Jacobi sum J(χ,χ) has algebraic norm p.

This is the exact CM object needed to identify the Frobenius trace for
E : y² = x³ - x at split primes.
-/

namespace Synthesis.Millennium.BSD

open Complex

theorem four_dvd_prime_sub_one_of_mod_four_eq_one
    {p : ℕ} (hmod : p % 4 = 1) :
    4 ∣ p - 1 := by
  omega

noncomputable def splitQuarticCharacter
    (p : ℕ) [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    MulChar (ZMod p) ℂ :=
  Classical.choose <|
    MulChar.exists_mulChar_orderOf (ZMod p)
      (by
        simpa using four_dvd_prime_sub_one_of_mod_four_eq_one hmod)
      Complex.isPrimitiveRoot_I

theorem splitQuarticCharacter_orderOf
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    orderOf (splitQuarticCharacter p hmod) = 4 :=
  (Classical.choose_spec <|
    MulChar.exists_mulChar_orderOf (ZMod p)
      (by simpa using four_dvd_prime_sub_one_of_mod_four_eq_one hmod)
      Complex.isPrimitiveRoot_I)

theorem splitQuarticCharacter_ne_one
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    splitQuarticCharacter p hmod ≠ 1 := by
  intro h
  have ho := splitQuarticCharacter_orderOf hmod
  rw [h, orderOf_one] at ho
  norm_num at ho

theorem splitQuarticCharacter_sq_ne_one
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    splitQuarticCharacter p hmod ^ 2 ≠ 1 := by
  intro hsquare
  have hdiv : orderOf (splitQuarticCharacter p hmod) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hsquare
  rw [splitQuarticCharacter_orderOf hmod] at hdiv
  norm_num at hdiv

theorem splitQuarticCharacter_inv_ne_one
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    (splitQuarticCharacter p hmod)⁻¹ ≠ 1 := by
  simpa using inv_ne_one.mpr (splitQuarticCharacter_ne_one hmod)

theorem splitQuarticCharacter_inv_sq_ne_one
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    (splitQuarticCharacter p hmod)⁻¹ *
      (splitQuarticCharacter p hmod)⁻¹ ≠ 1 := by
  rw [← inv_mul, ← pow_two]
  simpa using inv_ne_one.mpr (splitQuarticCharacter_sq_ne_one hmod)

noncomputable def splitQuarticJacobiSum
    (p : ℕ) [Fact p.Prime] (hmod : p % 4 = 1) : ℂ :=
  jacobiSum (splitQuarticCharacter p hmod)
    (splitQuarticCharacter p hmod)

theorem star_splitQuarticJacobiSum
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    star (splitQuarticJacobiSum p hmod)
      = jacobiSum (splitQuarticCharacter p hmod)⁻¹
          (splitQuarticCharacter p hmod)⁻¹ := by
  unfold splitQuarticJacobiSum jacobiSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [map_mul, MulChar.star_apply', MulChar.star_apply']
  simp

theorem splitQuarticJacobiSum_mul_star
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    splitQuarticJacobiSum p hmod * star (splitQuarticJacobiSum p hmod)
      = (p : ℂ) := by
  rw [star_splitQuarticJacobiSum hmod]
  unfold splitQuarticJacobiSum
  have hchar : ringChar ℂ ≠ ringChar (ZMod p) := by
    simp [hp.out.ne_zero]
  simpa using
    (jacobiSum_mul_jacobiSum_inv
      (F := ZMod p) (F' := ℂ)
      hchar
      (splitQuarticCharacter_ne_one hmod)
      (splitQuarticCharacter_ne_one hmod)
      (by simpa [pow_two] using splitQuarticCharacter_sq_ne_one hmod))

theorem normSq_splitQuarticJacobiSum
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    Complex.normSq (splitQuarticJacobiSum p hmod) = p := by
  have h := splitQuarticJacobiSum_mul_star hmod
  rw [Complex.mul_conj] at h
  exact_mod_cast congrArg Complex.re h

theorem norm_splitQuarticJacobiSum_sq
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    ‖splitQuarticJacobiSum p hmod‖ ^ 2 = p := by
  rw [sq_norm]
  simpa using normSq_splitQuarticJacobiSum hmod

end Synthesis.Millennium.BSD
