import Synthesis.MillenniumBSDCMSplitCharacterSum
import Mathlib.Tactic

/-!
# Split-prime Frobenius trace as the real part of one Jacobi sum

The split cubic character sum is already the sum of two quartic/quadratic
Jacobi sums.  The quadratic shadow is real-valued and conjugation sends the
quartic character to its inverse, so those two sums are complex conjugates.

This reduces the remaining signed CM trace theorem to the phase/primary
normalization of one norm-p Jacobi sum.
-/

namespace Synthesis.Millennium.BSD

open Complex
open scoped BigOperators

theorem star_splitQuadraticShadow_apply
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1)
    (x : ZMod p) :
    star (splitQuadraticShadow p hmod x) =
      splitQuadraticShadow p hmod x := by
  rw [splitQuadraticShadow_eq_complexQuadraticChar hmod]
  unfold complexQuadraticChar
  rw [MulChar.ringHomComp_apply]
  change star ((quadraticChar (ZMod p) x : ℂ)) =
    (quadraticChar (ZMod p) x : ℂ)
  norm_num

theorem star_splitJacobiPlus
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    star (splitJacobiPlus p hmod) = splitJacobiMinus p hmod := by
  classical
  unfold splitJacobiPlus splitJacobiMinus jacobiSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [map_mul, MulChar.star_apply', star_splitQuadraticShadow_apply hmod]

theorem splitJacobiMinus_eq_star_plus
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    splitJacobiMinus p hmod = star (splitJacobiPlus p hmod) := by
  exact (star_splitJacobiPlus hmod).symm

theorem split_cmCharacterSum_eq_plus_star
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    (cmCharacterSum p : ℂ) =
      splitJacobiPlus p hmod + star (splitJacobiPlus p hmod) := by
  rw [split_cmCharacterSum_eq_two_jacobi hmod,
    splitJacobiMinus_eq_star_plus hmod]

theorem split_cmCharacterSum_eq_two_re
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    (cmCharacterSum p : ℂ) =
      (2 * (splitJacobiPlus p hmod).re : ℝ) := by
  rw [split_cmCharacterSum_eq_plus_star hmod]
  apply Complex.ext
  · simp
  · simp

theorem split_frobeniusCoefficient_eq_neg_plus_star
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    (frobeniusCoefficient p : ℂ) =
      -(splitJacobiPlus p hmod + star (splitJacobiPlus p hmod)) := by
  have hp2 : p ≠ 2 := by omega
  rw [frobeniusCoefficient_eq_neg_characterSum hp2]
  norm_cast
  rw [split_cmCharacterSum_eq_plus_star hmod]

/--
Prize-facing remaining split-prime CM producer: identify the real part of the
single norm-p Jacobi sum with the primary signed Gaussian coordinate.
-/
def SplitPrimeJacobiPrimaryNormalization : Prop :=
  ∀ (p : ℕ) (_hp : p.Prime) (hmod : p % 4 = 1),
    ∃ a b : ℤ,
      a ^ 2 + b ^ 2 = p ∧
      splitJacobiPlus p hmod = (a : ℂ) + (b : ℂ) * Complex.I

end Synthesis.Millennium.BSD
