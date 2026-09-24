import Synthesis.MillenniumBSDCMSplitCharacterSum
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Tactic

/-!
# Hasse bound for the CM curve y² = x³ - x

At split primes p ≡ 1 mod 4 the cubic quadratic-character sum is

  S_p = J + conjugate(J)

for J = J(χ,χ²), while the Jacobi norm identity gives

  J * conjugate(J) = p.

Hence |S_p|² ≤ 4p.  At inert primes the trace is already proved zero, so
the same bound holds at every odd prime.  Since a_p = -S_p, this is the
Hasse bound for the repository's literal Frobenius coefficient.
-/

namespace Synthesis.Millennium.BSD

open scoped BigOperators

theorem splitQuadraticShadow_isQuadratic
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    (splitQuadraticShadow p hmod).IsQuadratic := by
  unfold splitQuadraticShadow
  exact splitQuarticCharacter_sq_isQuadratic hmod

theorem splitQuadraticShadow_ne_one
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    splitQuadraticShadow p hmod ≠ 1 := by
  unfold splitQuadraticShadow
  exact splitQuarticCharacter_sq_ne_one hmod

theorem splitQuadraticShadow_inv
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    (splitQuadraticShadow p hmod)⁻¹ =
      splitQuadraticShadow p hmod :=
  (splitQuadraticShadow_isQuadratic hmod).inv

theorem splitQuartic_mul_shadow_ne_one
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    splitQuarticCharacter p hmod * splitQuadraticShadow p hmod ≠ 1 := by
  change splitQuarticCharacter p hmod ^ 3 ≠ 1
  intro h
  have hdiv : orderOf (splitQuarticCharacter p hmod) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one h
  rw [splitQuarticCharacter_orderOf hmod] at hdiv
  norm_num at hdiv

theorem star_jacobiSum_complex
    {F : Type*} [Field F] [Fintype F]
    (χ ψ : MulChar F ℂ) :
    star (jacobiSum χ ψ) = jacobiSum χ⁻¹ ψ⁻¹ := by
  classical
  unfold jacobiSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [map_mul, MulChar.star_apply', MulChar.star_apply']

theorem star_splitJacobiPlus
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    star (splitJacobiPlus p hmod) = splitJacobiMinus p hmod := by
  unfold splitJacobiPlus splitJacobiMinus
  rw [star_jacobiSum_complex, splitQuadraticShadow_inv hmod]

theorem splitJacobiPlus_mul_minus
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    splitJacobiPlus p hmod * splitJacobiMinus p hmod = (p : ℂ) := by
  unfold splitJacobiPlus splitJacobiMinus
  rw [← splitQuadraticShadow_inv hmod]
  have hchar : ringChar ℂ ≠ ringChar (ZMod p) := by
    simp [hp.out.ne_zero]
  exact jacobiSum_mul_jacobiSum_inv
    (F := ZMod p) (F' := ℂ)
    hchar
    (splitQuarticCharacter_ne_one hmod)
    (splitQuadraticShadow_ne_one hmod)
    (splitQuartic_mul_shadow_ne_one hmod)

theorem splitJacobiPlus_mul_star
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    splitJacobiPlus p hmod * star (splitJacobiPlus p hmod) = (p : ℂ) := by
  rw [star_splitJacobiPlus hmod]
  exact splitJacobiPlus_mul_minus hmod

theorem splitJacobiPlus_norm_sq
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    ‖splitJacobiPlus p hmod‖ ^ 2 = (p : ℝ) := by
  have h := congrArg norm (splitJacobiPlus_mul_star hmod)
  simpa [norm_mul, norm_star, pow_two] using h

theorem split_cmCharacterSum_cast_eq_add_star
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    (cmCharacterSum p : ℂ) =
      splitJacobiPlus p hmod + star (splitJacobiPlus p hmod) := by
  rw [split_cmCharacterSum_eq_two_jacobi hmod, star_splitJacobiPlus hmod]

theorem split_cmCharacterSum_abs_sq_le_four_mul_prime
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    (|cmCharacterSum p| : ℝ) ^ 2 ≤ 4 * p := by
  have hsum := split_cmCharacterSum_cast_eq_add_star hmod
  have htri :
      ‖(cmCharacterSum p : ℂ)‖
        ≤ ‖splitJacobiPlus p hmod‖ +
          ‖star (splitJacobiPlus p hmod)‖ := by
    rw [hsum]
    exact norm_add_le _ _
  rw [norm_star] at htri
  have hnorm := splitJacobiPlus_norm_sq hmod
  have hJ : 0 ≤ ‖splitJacobiPlus p hmod‖ := norm_nonneg _
  have hS : 0 ≤ ‖(cmCharacterSum p : ℂ)‖ := norm_nonneg _
  have hcast : ‖(cmCharacterSum p : ℂ)‖ = (|cmCharacterSum p| : ℝ) := by
    simp
  rw [hcast] at htri hS
  nlinarith [sq_nonneg ((|cmCharacterSum p| : ℝ) -
    2 * ‖splitJacobiPlus p hmod‖)]

theorem split_frobeniusCoefficient_sq_le_four_mul_prime
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    (frobeniusCoefficient p : ℝ) ^ 2 ≤ 4 * p := by
  have h := split_cmCharacterSum_abs_sq_le_four_mul_prime hmod
  rw [frobeniusCoefficient_eq_neg_characterSum (by
    intro hp2; subst p; norm_num at hmod)]
  norm_num [sq]
  exact h

theorem inert_frobeniusCoefficient_sq_le_four_mul_prime
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 3) :
    (frobeniusCoefficient p : ℝ) ^ 2 ≤ 4 * p := by
  rw [inert_frobeniusCoefficient_eq_zero hmod]
  positivity

theorem frobeniusCoefficient_sq_le_four_mul_prime
    {p : ℕ} [Fact hp : p.Prime] (hp2 : p ≠ 2) :
    (frobeniusCoefficient p : ℝ) ^ 2 ≤ 4 * p := by
  obtain ⟨hcase, _⟩ := oddPrimeCMCase_exists hp.out hp2
  rcases hcase with h1 | h3
  · exact split_frobeniusCoefficient_sq_le_four_mul_prime h1
  · exact inert_frobeniusCoefficient_sq_le_four_mul_prime h3

theorem frobeniusCoefficient_abs_le_two_mul_sqrt
    {p : ℕ} [Fact hp : p.Prime] (hp2 : p ≠ 2) :
    |(frobeniusCoefficient p : ℝ)| ≤ 2 * Real.sqrt p := by
  have hsq := frobeniusCoefficient_sq_le_four_mul_prime hp2
  have hsqrt : (Real.sqrt p) ^ 2 = (p : ℝ) := by
    rw [sq_sqrt]
    positivity
  have habs : 0 ≤ |(frobeniusCoefficient p : ℝ)| := abs_nonneg _
  have hsqrt0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (|(frobeniusCoefficient p : ℝ)| - 2 * Real.sqrt p)]

end Synthesis.Millennium.BSD
