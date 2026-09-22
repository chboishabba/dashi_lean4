import Synthesis.MillenniumBSDCMSplitJacobiGaussianNorm
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Tactic

/-!
# Parity and the exact primary-associate residual for the split Jacobi sum

Mathlib's Jacobi congruence theorem gives

  J(χ,χ²) = -1 + z (i-1)²,   z ∈ Z[i].

Writing z=c+di and using (i-1)²=-2i yields

  J = (-1+2d) + (-2c)i.

So the real coordinate is odd and the imaginary coordinate is even.  Together
with the already-proved norm equation this leaves exactly one sign datum:
the primary normalization of the odd real coordinate modulo 4.
-/

namespace Synthesis.Millennium.BSD

open Complex Algebra

theorem splitJacobiPlus_negOne_add_square
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    ∃ z : ℂ,
      z ∈ Algebra.adjoin ℤ ({Complex.I} : Set ℂ) ∧
      splitJacobiPlus p hmod =
        -1 + z * (Complex.I - 1) ^ 2 := by
  unfold splitJacobiPlus
  exact exists_jacobiSum_eq_neg_one_add
    (n := 4) (by norm_num)
    (splitQuarticCharacter_pow_four_eq_one hmod)
    (splitQuadraticShadow_pow_four_eq_one hmod)
    (four_dvd_prime_sub_one_of_mod_four_eq_one hmod)
    Complex.isPrimitiveRoot_I

theorem splitJacobiPlus_parity_coordinates
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    ∃ c d : ℤ,
      splitJacobiPlus p hmod =
        ((-1 + 2*d : ℤ) : ℂ) + ((-2*c : ℤ) : ℂ) * Complex.I := by
  rcases splitJacobiPlus_negOne_add_square hmod with ⟨z,hz,hJ⟩
  rcases exists_int_coords_of_mem_adjoin_I hz with ⟨c,d,hzcd⟩
  refine ⟨c,d,?_⟩
  rw [hJ, hzcd]
  push_cast
  rw [Complex.I_sq]
  ring

theorem splitJacobiPlus_norm_with_parity
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    ∃ a b : ℤ,
      a ^ 2 + b ^ 2 = (p : ℤ) ∧
      Odd a ∧ Even b ∧
      splitJacobiPlus p hmod = (a : ℂ) + (b : ℂ) * Complex.I := by
  rcases splitJacobiPlus_parity_coordinates hmod with ⟨c,d,hJ⟩
  let a : ℤ := -1 + 2*d
  let b : ℤ := -2*c
  have hnorm := normSq_splitJacobiPlus hmod
  rw [hJ] at hnorm
  have hab : a ^ 2 + b ^ 2 = (p : ℤ) := by
    have hr : (((a ^ 2 + b ^ 2 : ℤ) : ℝ)) = p := by
      simpa [a,b,Complex.normSq_apply] using hnorm
    exact_mod_cast hr
  refine ⟨a,b,hab,?_,?_,?_⟩
  · refine ⟨d - 1, ?_⟩
    simp [a]
    ring
  · refine ⟨-c, ?_⟩
    simp [b]
  · simpa [a,b] using hJ

/--
The exact remaining split-prime sign theorem.  The norm and parity are already
proved above; only the primary real-coordinate congruence is missing.
-/
def SplitJacobiPrimaryRealCongruence : Prop :=
  ∀ (p : ℕ) (_hp : p.Prime) (hmod : p % 4 = 1),
    ∃ a b : ℤ,
      a ^ 2 + b ^ 2 = (p : ℤ) ∧
      a % 4 = 1 ∧
      Even b ∧
      splitJacobiPlus p hmod = (a : ℂ) + (b : ℂ) * Complex.I

theorem split_frobenius_signed_of_primaryRealCongruence
    (hprimary : SplitJacobiPrimaryRealCongruence)
    {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1) :
    ∃ a b : ℤ,
      a ^ 2 + b ^ 2 = (p : ℤ) ∧
      a % 4 = 1 ∧ Even b ∧
      frobeniusCoefficient p = -2 * a := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hprimary p hp hmod with ⟨a,b,hnorm,ha4,hbeven,hJ⟩
  refine ⟨a,b,hnorm,ha4,hbeven,?_⟩
  have htrace := split_frobeniusCoefficient_eq_neg_plus_star hmod
  rw [hJ] at htrace
  apply_fun Complex.re at htrace
  norm_num at htrace
  exact_mod_cast htrace

end Synthesis.Millennium.BSD
