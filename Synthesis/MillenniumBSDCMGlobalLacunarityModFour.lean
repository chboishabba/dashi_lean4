import Synthesis.MillenniumBSDCMGlobalLacunarityInert
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-!
# Complete mod-four lacunarity for the CM elliptic coefficients

If n ≡ 3 mod 4 and every inert prime valuation were even, the two-squares
criterion would make n a sum of two squares.  But squares modulo four are
0 or 1, so a sum of two squares is never 3 mod 4.  Therefore some
p ≡ 3 mod 4 occurs to odd exponent, and the inert local coefficient kills
the global coefficient.
-/

namespace Synthesis.Millennium.BSD

theorem sq_add_sq_mod_four_ne_three (x y : ℕ) :
    (x ^ 2 + y ^ 2) % 4 ≠ 3 := by
  intro h
  have hx : x % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hy : y % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h' : ((x % 4) ^ 2 + (y % 4) ^ 2) % 4 = 3 := by
    simpa [Nat.add_mod, Nat.pow_mod] using h
  interval_cases hxv : x % 4 <;>
    interval_cases hyv : y % 4 <;>
    norm_num [hxv, hyv] at h'

theorem inertOddFactorWitness_of_mod_four_eq_three
    {n : ℕ} (hmod : n % 4 = 3) :
    InertOddFactorWitness n := by
  by_contra hnone
  have hallEven :
      ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n) := by
    intro q hq hq4
    rcases Nat.even_or_odd (padicValNat q n) with he | ho
    · exact he
    · obtain ⟨k, hk⟩ := ho.exists_bit1
      exfalso
      apply hnone
      refine ⟨q, k, Nat.prime_of_mem_primeFactors hq, hq4, ?_⟩
      rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hq)]
      exact hk
  have hsum : ∃ x y : ℕ, n = x ^ 2 + y ^ 2 :=
    Nat.eq_sq_add_sq_iff.mpr hallEven
  rcases hsum with ⟨x,y,rfl⟩
  exact sq_add_sq_mod_four_ne_three x y hmod

theorem cmAllNCoefficient_eq_zero_of_mod_four_eq_three
    {n : ℕ} (hmod : n % 4 = 3) :
    cmAllNCoefficient n = 0 := by
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    norm_num at hmod
  have hnodd : Odd n := by
    exact Nat.odd_iff.mpr (by omega)
  exact cmAllNCoefficient_eq_zero_of_inertOddFactorWitness
    hn0 hnodd (inertOddFactorWitness_of_mod_four_eq_three hmod)

theorem cmAllNCoefficient_eq_zero_unless_one_mod_four
    {n : ℕ} (hnpos : 0 < n) (hnot : n % 4 ≠ 1) :
    cmAllNCoefficient n = 0 := by
  have hcases : n % 4 = 0 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
    omega
  rcases hcases with h0 | h2 | h3
  · have heven : ¬ Odd n := by
      intro hodd
      have := hodd.not_two_dvd_nat
      apply this
      exact ⟨n / 2, by omega⟩
    exact cmAllNCoefficient_eq_zero_of_not_odd heven
  · have heven : ¬ Odd n := by
      intro hodd
      have := hodd.not_two_dvd_nat
      apply this
      exact ⟨n / 2, by omega⟩
    exact cmAllNCoefficient_eq_zero_of_not_odd heven
  · exact cmAllNCoefficient_eq_zero_of_mod_four_eq_three h3

end Synthesis.Millennium.BSD
