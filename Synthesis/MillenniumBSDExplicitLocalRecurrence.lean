import Synthesis.MillenniumBSDFrobeniusPointCount
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Explicit local Euler polynomial, coefficient bound, and prime-power recurrence

This file works directly from the literal finite-field coefficient

  a_p = p + 1 - #E(F_p),    E : y² = x³ - x,

rather than through an abstract CM sign convention.

For every odd prime we define the good local Euler polynomial

  P_p(T) = 1 - a_p T + p T²,

prove the elementary but global point-count bound |a_p| ≤ p, and define the
prime-power coefficient recurrence determined by 1 / P_p(T):

  A_p(0) = 1
  A_p(1) = a_p
  A_p(n+2) = a_p A_p(n+1) - p A_p(n).

At inert primes p = 3 mod 4 the already-proved theorem a_p = 0 therefore gives
the exact closed form

  A_p(2k)   = (-p)^k,
  A_p(2k+1) = 0.

This is an actual analytic/arithmetic producer, not a convergence interface.
-/

namespace Synthesis.Millennium.BSD

open scoped BigOperators
open Polynomial

theorem quadraticChar_cmCubic_abs_le_one
    {p : ℕ} [Fact p.Prime]
    (x : ZMod p) :
    |quadraticChar (ZMod p) (cmCubic x)| ≤ (1 : ℤ) := by
  by_cases hx : cmCubic x = 0
  · simp [hx]
  · rcases quadraticChar_dichotomy hx with h | h
    · simp [h]
    · simp [h]

theorem cmCharacterSum_abs_le_prime
    {p : ℕ} [Fact p.Prime] :
    |cmCharacterSum p| ≤ (p : ℤ) := by
  unfold cmCharacterSum cmCharacterTerm
  calc
    |∑ x : ZMod p, quadraticChar (ZMod p) (cmCubic x)|
        ≤ ∑ x : ZMod p, |quadraticChar (ZMod p) (cmCubic x)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : ZMod p, (1 : ℤ) := by
          exact Finset.sum_le_sum
            (fun x _hx => quadraticChar_cmCubic_abs_le_one x)
    _ = (p : ℤ) := by simp

theorem frobeniusCoefficient_abs_le_prime
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    |frobeniusCoefficient p| ≤ (p : ℤ) := by
  rw [frobeniusCoefficient_eq_neg_characterSum hp2, abs_neg]
  exact cmCharacterSum_abs_le_prime

def explicitGoodLocalPolynomial
    (p : ℕ) [Fact p.Prime] :
    ℤ[X] :=
  1
    - C (frobeniusCoefficient p) * X
    + C (p : ℤ) * X ^ 2

theorem explicitGoodLocalPolynomial_constantCoeff
    (p : ℕ) [Fact p.Prime] :
    (explicitGoodLocalPolynomial p).coeff 0 = 1 := by
  simp [explicitGoodLocalPolynomial]

theorem inert_explicitGoodLocalPolynomial
    {p : ℕ} [Fact p.Prime]
    (hmod : p % 4 = 3) :
    explicitGoodLocalPolynomial p
      = 1 + C (p : ℤ) * X ^ 2 := by
  rw [explicitGoodLocalPolynomial,
    inert_frobeniusCoefficient_eq_zero hmod]
  simp

def explicitPrimePowerCoefficient
    (p : ℕ) [Fact p.Prime] :
    ℕ → ℤ
  | 0 => 1
  | 1 => frobeniusCoefficient p
  | n + 2 =>
      frobeniusCoefficient p
        * explicitPrimePowerCoefficient p (n + 1)
      - (p : ℤ) * explicitPrimePowerCoefficient p n

@[simp] theorem explicitPrimePowerCoefficient_zero
    (p : ℕ) [Fact p.Prime] :
    explicitPrimePowerCoefficient p 0 = 1 :=
  rfl

@[simp] theorem explicitPrimePowerCoefficient_one
    (p : ℕ) [Fact p.Prime] :
    explicitPrimePowerCoefficient p 1 =
      frobeniusCoefficient p :=
  rfl

theorem explicitPrimePowerCoefficient_recurrence
    (p : ℕ) [Fact p.Prime]
    (n : ℕ) :
    explicitPrimePowerCoefficient p (n + 2)
      =
      frobeniusCoefficient p
        * explicitPrimePowerCoefficient p (n + 1)
      - (p : ℤ) * explicitPrimePowerCoefficient p n :=
  rfl

theorem inert_primePowerCoefficient_even_odd
    {p : ℕ} [Fact p.Prime]
    (hmod : p % 4 = 3) :
    ∀ k : ℕ,
      explicitPrimePowerCoefficient p (2 * k) = (-(p : ℤ)) ^ k
      ∧
      explicitPrimePowerCoefficient p (2 * k + 1) = 0 := by
  intro k
  induction k with
  | zero =>
      simp [explicitPrimePowerCoefficient]
  | succ k ih =>
      rcases ih with ⟨heven, hodd⟩
      have hap : frobeniusCoefficient p = 0 :=
        inert_frobeniusCoefficient_eq_zero hmod
      constructor
      · rw [show 2 * (Nat.succ k) = 2 * k + 2 by omega,
            explicitPrimePowerCoefficient_recurrence,
            hap, zero_mul, zero_sub, heven]
        ring
      · rw [show 2 * (Nat.succ k) + 1 = (2 * k + 1) + 2 by omega,
            explicitPrimePowerCoefficient_recurrence,
            hap, zero_mul, hodd]
        ring

theorem inert_primePowerCoefficient_even
    {p : ℕ} [Fact p.Prime]
    (hmod : p % 4 = 3)
    (k : ℕ) :
    explicitPrimePowerCoefficient p (2 * k)
      = (-(p : ℤ)) ^ k :=
  (inert_primePowerCoefficient_even_odd hmod k).1

theorem inert_primePowerCoefficient_odd
    {p : ℕ} [Fact p.Prime]
    (hmod : p % 4 = 3)
    (k : ℕ) :
    explicitPrimePowerCoefficient p (2 * k + 1) = 0 :=
  (inert_primePowerCoefficient_even_odd hmod k).2

theorem inert_primePowerCoefficient_even_abs
    {p : ℕ} [Fact p.Prime]
    (hmod : p % 4 = 3)
    (k : ℕ) :
    |explicitPrimePowerCoefficient p (2 * k)|
      = (p : ℤ) ^ k := by
  rw [inert_primePowerCoefficient_even hmod]
  simp [abs_pow]

end Synthesis.Millennium.BSD
