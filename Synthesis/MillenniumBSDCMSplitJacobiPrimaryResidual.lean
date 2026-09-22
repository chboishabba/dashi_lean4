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
The exact remaining split-prime sign theorem.

For the mixed quartic/quadratic Jacobi sum the classical primary normalization
is the cube congruence

  J ≡ -1 mod (i-1)^3.

The generic mathlib theorem supplies only the square congruence.  This stronger
specialized cube congruence is exactly the remaining phase datum.
-/
def SplitJacobiPrimaryCubeCongruence : Prop :=
  ∀ (p : ℕ) (_hp : p.Prime) (hmod : p % 4 = 1),
    ∃ c d : ℤ,
      splitJacobiPlus p hmod =
        -1 +
          ((c : ℂ) + (d : ℂ) * Complex.I) *
            (Complex.I - 1) ^ 3

theorem primaryCubeCongruence_coordinates
    (hprimary : SplitJacobiPrimaryCubeCongruence)
    {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1) :
    ∃ a b : ℤ,
      a ^ 2 + b ^ 2 = (p : ℤ) ∧
      Int.ModEq 4 (a + b) (-1) ∧
      splitJacobiPlus p hmod = (a : ℂ) + (b : ℂ) * Complex.I := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hprimary p hp hmod with ⟨c,d,hcube⟩
  let a : ℤ := -1 + 2 * (c - d)
  let b : ℤ := 2 * (c + d)
  have hcoords :
      splitJacobiPlus p hmod =
        (a : ℂ) + (b : ℂ) * Complex.I := by
    rw [hcube]
    dsimp [a,b]
    push_cast
    rw [Complex.I_sq]
    ring
  have hnorm := normSq_splitJacobiPlus hmod
  rw [hcoords] at hnorm
  have hab : a ^ 2 + b ^ 2 = (p : ℤ) := by
    have hr : (((a ^ 2 + b ^ 2 : ℤ) : ℝ)) = p := by
      simpa [Complex.normSq_apply] using hnorm
    exact_mod_cast hr
  refine ⟨a,b,hab,?_,hcoords⟩
  rw [Int.modEq_iff_dvd]
  use c
  dsimp [a,b]
  ring

/--
After the cube congruence, the remaining conversion to the Jacobi theta
coefficient sign is only the uniqueness/associate statement for a prime
sum-of-two-squares representation.  We keep that as a separate arithmetic
owner instead of folding it into the character-sum theorem.
-/
def SplitPrimeRepresentationSignCompiler : Prop :=
  ∀ (p r s : ℕ),
    p.Prime →
    p = (2 * r + 1) ^ 2 + 4 * s ^ 2 →
    ∀ a b : ℤ,
      a ^ 2 + b ^ 2 = (p : ℤ) →
      Int.ModEq 4 (a + b) (-1) →
      -2 * a = 2 * ((-1 : ℤ) ^ (r + s)) * (2 * r + 1)

theorem split_frobenius_signed_of_primary_and_representation
    (hprimary : SplitJacobiPrimaryCubeCongruence)
    (hsign : SplitPrimeRepresentationSignCompiler)
    {p r s : ℕ} (hp : p.Prime)
    (hrep : p = (2 * r + 1) ^ 2 + 4 * s ^ 2)
    (hmod : p % 4 = 1) :
    frobeniusCoefficient p =
      2 * ((-1 : ℤ) ^ (r + s)) * (2 * r + 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases primaryCubeCongruence_coordinates hprimary hp hmod with
    ⟨a,b,hnorm,hcong,hJ⟩
  have htrace := split_frobeniusCoefficient_eq_neg_plus_star hmod
  rw [hJ] at htrace
  apply_fun Complex.re at htrace
  norm_num at htrace
  have hfa : frobeniusCoefficient p = -2 * a := by
    exact_mod_cast htrace
  rw [hfa]
  exact hsign p r s hp hrep a b hnorm hcong

end Synthesis.Millennium.BSD
