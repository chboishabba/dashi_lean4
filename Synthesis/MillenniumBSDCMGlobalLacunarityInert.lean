import Synthesis.MillenniumBSDFullyExplicitGlobalCoefficients
import Synthesis.MillenniumBSDExplicitLocalRecurrence
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic

/-!
# Global CM coefficient vanishing from an inert odd valuation

For an odd n, the literal global coefficient is the product of the explicit
prime-power coefficients.  If an inert prime p ≡ 3 (mod 4) occurs to odd
exponent 2k+1, its local coefficient vanishes, hence so does the global one.

This pays the elliptic L-function part of the mod-4 lacunarity theorem.  The
remaining purely elementary number-theory producer is that n ≡ 3 (mod 4)
forces such an inert prime to occur to odd exponent.
-/

namespace Synthesis.Millennium.BSD

theorem factorization_mem_support_of_eq_odd
    {n p k : ℕ}
    (h : n.factorization p = 2 * k + 1) :
    p ∈ n.factorization.support := by
  rw [Finsupp.mem_support_iff]
  omega

theorem explicitPrimePowerCoefficientNat_eq_zero_of_inert_odd
    {p k : ℕ} (hp : p.Prime)
    (hmod : p % 4 = 3) :
    explicitPrimePowerCoefficientNat p (2 * k + 1) = 0 := by
  rw [explicitPrimePowerCoefficientNat_of_prime hp]
  letI : Fact p.Prime := ⟨hp⟩
  exact inert_primePowerCoefficient_odd hmod k

theorem cmAllNCoefficient_eq_zero_of_inert_odd_factorization
    {n p k : ℕ}
    (hn0 : n ≠ 0)
    (hnodd : Odd n)
    (hp : p.Prime)
    (hmod : p % 4 = 3)
    (hfac : n.factorization p = 2 * k + 1) :
    cmAllNCoefficient n = 0 := by
  rw [cmAllNCoefficient_odd_factorization hn0 hnodd]
  apply (Finsupp.prod_eq_zero_iff).2
  refine ⟨p, factorization_mem_support_of_eq_odd hfac, ?_⟩
  rw [hfac]
  exact explicitPrimePowerCoefficientNat_eq_zero_of_inert_odd hp hmod

/--
The exact remaining number-theory interface needed to conclude vanishing for
every n ≡ 3 mod 4.
-/
def InertOddFactorWitness (n : ℕ) : Prop :=
  ∃ p k : ℕ,
    p.Prime ∧
    p % 4 = 3 ∧
    n.factorization p = 2 * k + 1

theorem cmAllNCoefficient_eq_zero_of_inertOddFactorWitness
    {n : ℕ} (hn0 : n ≠ 0) (hnodd : Odd n)
    (h : InertOddFactorWitness n) :
    cmAllNCoefficient n = 0 := by
  rcases h with ⟨p,k,hp,hmod,hfac⟩
  exact cmAllNCoefficient_eq_zero_of_inert_odd_factorization
    hn0 hnodd hp hmod hfac

end Synthesis.Millennium.BSD
