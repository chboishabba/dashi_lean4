import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# BSD compatibility: rational square criterion over pinned mathlib v4.28

The theorem Rat.isSquare_iff_even_factorization is present in newer
Mathlib (October/November 2026) but not in the project's pinned v4.28.0
sources. This file ports its actual mathematical proof from the original
mathlib authors using v4.28's Nat.factorization_prod_pow_eq_self,
Rat.isSquare_iff, and established rational p-adic valuations.

Attribution: mathlib4 Mathlib/Data/Nat/Factorization/Defs.lean and
Mathlib/NumberTheory/Padics/PadicVal/Basic.lean (upstream theorem
isSquare_iff_even_factorization), plus original v4.28.0 factorization
and square-fraction owners. DASHI composition is source-written only;
local Lean kernel verification is pending.

This is not a new number-theoretic result.
-/

namespace Synthesis.Millennium.BSD

/-- Backport of the positive direction of the original mathlib
natural-number square/prime-factorization criterion. -/
theorem cmPinnedNatSquare_of_even_factorization
    {n : ℕ}
    (h : ∀ p : ℕ, p.Prime → Even (n.factorization p)) :
    IsSquare n := by
  classical
  by_cases hzero : n = 0
  · subst n
    exact ⟨0, by simp⟩
  refine ⟨n.factorization.prod (fun p e => p ^ (e / 2)), ?_⟩
  rw [← pow_two, ← powMonoidHom_apply, map_finsuppProd]
  nth_rw 1 [← Nat.factorization_prod_pow_eq_self hzero]
  refine Finsupp.prod_congr fun p hp => ?_
  rw [powMonoidHom_apply, ← pow_mul,
    div_two_mul_two_of_even (h p (Nat.prime_of_mem_primeFactors hp))]

/-- Reduced numerator and denominator cannot both have strictly
positive valuation at the same prime. -/
theorem cmPinnedRat_num_den_padic_one_zero
    (a : ℚ) (p : ℕ) (hp : p.Prime) :
    padicValNat p a.num.natAbs = 0 ∨
      padicValNat p a.den = 0 := by
  by_cases hn : p ∣ a.num.natAbs
  · right
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have hcommon : p ∣ Nat.gcd a.num.natAbs a.den :=
      Nat.dvd_gcd hn hd
    have hOne : p ∣ 1 := by
      simpa [a.reduced] using hcommon
    exact hp.ne_one (Nat.dvd_one.mp hOne)
  · exact Or.inl (padicValNat.eq_zero_of_not_dvd hn)

/-- Ported rational arithmetic: if v_p(a) is even, coprimality of
reduced numerator and denominator makes both valuations even. -/
theorem cmPinnedRat_num_den_even
    (a : ℚ) (p : ℕ) (hp : p.Prime)
    (h : Even (padicValRat p a)) :
    Even (padicValInt p a.num) ∧ Even (padicValNat p a.den) := by
  obtain ⟨k, hk⟩ := h
  have hval :
      (padicValNat p a.num.natAbs : ℤ) -
        (padicValNat p a.den : ℤ) = k + k := by
    simpa only [padicValRat_def, padicValInt] using hk
  rcases cmPinnedRat_num_den_padic_one_zero a p hp with hn | hd
  · constructor
    · change Even ((padicValNat p a.num.natAbs : ℕ) : ℤ)
      simp [hn]
    · have he : Even ((padicValNat p a.den : ℕ) : ℤ) :=
        ⟨-k, by rw [hn] at hval; omega⟩
      exact_mod_cast he
  · constructor
    · change Even ((padicValNat p a.num.natAbs : ℕ) : ℤ)
      exact ⟨k, by rw [hd] at hval; omega⟩
    · simp [hd]

/-- Backport of mathlib's integer square criterion in the direction
needed for rational square-class support. -/
theorem cmPinnedIntSquare_of_nonneg_even_factorization
    (n : ℤ)
    (hn : 0 ≤ n)
    (he : ∀ p : ℕ, p.Prime → Even (padicValInt p n)) :
    IsSquare n := by
  have hNat : IsSquare n.natAbs :=
    cmPinnedNatSquare_of_even_factorization (n := n.natAbs)
      (fun p hp => by
        simpa [Nat.factorization_def _ hp, padicValInt] using he p hp)
  obtain ⟨r, hr⟩ := hNat
  exact ⟨r, by rw [← Int.natAbs_of_nonneg hn, hr, Nat.cast_mul]⟩

/-- Same original rational square-factorization theorem, adapted to
the repository's exact mathlib v4.28.0 API, not a free hypothesis. -/
theorem cmPinnedRatSquare_of_nonneg_even_padicVal
    (a : ℚ)
    (ha : 0 ≤ a)
    (he : ∀ p : ℕ, p.Prime → Even (padicValRat p a)) :
    IsSquare a := by
  rw [Rat.isSquare_iff]
  constructor
  · exact cmPinnedIntSquare_of_nonneg_even_factorization a.num
      (Rat.num_nonneg.mpr ha)
      (fun p hp => (cmPinnedRat_num_den_even a p hp (he p hp)).1)
  · exact cmPinnedNatSquare_of_even_factorization (n := a.den)
      (fun p hp => by
        simpa [Nat.factorization_def _ hp] using
          (cmPinnedRat_num_den_even a p hp (he p hp)).2)

end Synthesis.Millennium.BSD
