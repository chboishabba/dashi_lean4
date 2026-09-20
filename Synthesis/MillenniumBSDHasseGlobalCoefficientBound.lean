import Synthesis.MillenniumBSDHasseLocalCoefficientBound
import Synthesis.MillenniumBSDFullyExplicitGlobalCoefficients
import Synthesis.MillenniumBSDFullGlobalAnalyticLFunction
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Tactic

/-!
# Global coefficient growth from Hasse local bounds

For odd n, multiplicativity and the local estimate

  |A_p(k)| <= (k+1) p^(k/2)

give

  |a_n| <= d(n) sqrt(n).

Using mathlib's elementary d(n) <= n gives |a_n| <= n^(3/2).  This is not
the optimal divisor bound, but already moves the literal global L-series
absolute-convergence and holomorphy half-plane from Re(s)>3 to Re(s)>5/2.
-/

namespace Synthesis.Millennium.BSD

open ArithmeticFunction

theorem cmAllNCoefficient_abs_le_divisors_mul_sqrt_of_odd
    {n : ℕ} (hn0 : n ≠ 0) (hnodd : Odd n) :
    |(cmAllNCoefficient n : ℝ)|
      ≤ (n.divisors.card : ℝ) * Real.sqrt n := by
  rw [cmAllNCoefficient_factorization_allPrime hn0]
  rw [Int.cast_finsupp_prod]
  rw [abs_prod]
  have hsqrtProd :
      n.primeFactors.prod
          (fun p => (Real.sqrt p) ^ (n.factorization p))
        = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    rw [← Nat.cast_prod_primeFactors_pow_factorization hn0]
    push_cast
    rw [← Finset.prod_rpow]
    · apply Finset.prod_congr rfl
      intro p hpMem
      rw [← Real.rpow_natCast]
      ring_nf
    · intro p hpMem
      positivity
  have hdiv := Nat.card_divisors hn0
  rw [hdiv]
  calc
    |n.factorization.prod
      (fun p k => explicitAllPrimePowerCoefficientNat p k : ℤ)|
      = n.primeFactors.prod
          (fun p =>
            |(explicitAllPrimePowerCoefficientNat p (n.factorization p) : ℝ)|) := by
          rw [Finsupp.prod, ← n.support_factorization]
          push_cast
          rw [abs_prod]
          rfl
    _ ≤ n.primeFactors.prod
          (fun p =>
            ((n.factorization p + 1 : ℕ) : ℝ) *
              (Real.sqrt p) ^ (n.factorization p)) := by
          apply Finset.prod_le_prod
          · intro p hpMem
            positivity
          · intro p hpMem
            have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
            have hp2 : p ≠ 2 := by
              intro hpEq
              subst p
              have h2dvd : 2 ∣ n :=
                Nat.dvd_of_mem_primeFactors hpMem
              exact hnodd.not_two_dvd_nat h2dvd
            letI : Fact p.Prime := ⟨hp⟩
            rw [explicitAllPrimePowerCoefficientNat_of_prime hp]
            rw [explicitAllPrimePowerCoefficient_odd hp2]
            simpa using
              explicitPrimePowerCoefficient_abs_le_hasse hp2 (n.factorization p)
    _ = (n.primeFactors.prod
            (fun p => ((n.factorization p + 1 : ℕ) : ℝ)))
          * (n.primeFactors.prod
            (fun p => (Real.sqrt p) ^ (n.factorization p))) := by
          rw [← Finset.prod_mul_distrib]
    _ = (n.divisors.card : ℝ) * Real.sqrt n := by
          rw [hsqrtProd]
          exact_mod_cast hdiv.symm

theorem cmAllNCoefficient_abs_le_nat_mul_sqrt
    (n : ℕ) :
    |(cmAllNCoefficient n : ℝ)|
      ≤ (n : ℝ) * Real.sqrt n := by
  by_cases hn0 : n = 0
  · subst n
    simp
  by_cases hnodd : Odd n
  · calc
      |(cmAllNCoefficient n : ℝ)|
        ≤ (n.divisors.card : ℝ) * Real.sqrt n :=
          cmAllNCoefficient_abs_le_divisors_mul_sqrt_of_odd hn0 hnodd
      _ ≤ (n : ℝ) * Real.sqrt n := by
        gcongr
        exact_mod_cast Nat.card_divisors_le_self n
  · rw [cmAllNCoefficient_eq_zero_of_not_odd hnodd]
    simp
    positivity

theorem cmAllNCoefficient_abs_le_rpow_three_halves
    (n : ℕ) :
    |(cmAllNCoefficient n : ℝ)|
      ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := by
  have h := cmAllNCoefficient_abs_le_nat_mul_sqrt n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  rw [Real.sqrt_eq_rpow] at h
  calc
    |(cmAllNCoefficient n : ℝ)|
      ≤ (n : ℝ) * (n : ℝ) ^ ((1 : ℝ)/2) := h
    _ = (n : ℝ) ^ ((3 : ℝ)/2) := by
      rw [show (n : ℝ) = (n : ℝ)^((1 : ℝ)) by rw [Real.rpow_one],
        ← Real.rpow_add (by positivity)]
      congr 2
      ring

theorem cmLSeriesSummable_hasse_global
    {s : ℂ} (hs : (5 : ℝ)/2 < s.re) :
    LSeriesSummable ((↑) ∘ cmAllNCoefficient) s := by
  apply LSeriesSummable_of_le_const_mul_rpow (x := (5 : ℝ)/2) hs
  refine ⟨1, ?_⟩
  intro n hn
  rw [Function.comp_apply, Complex.norm_intCast, one_mul]
  have h := cmAllNCoefficient_abs_le_rpow_three_halves n
  exact_mod_cast h

theorem cmLSeries_abscissaOfAbsConv_le_five_halves :
    LSeries.abscissaOfAbsConv ((↑) ∘ cmAllNCoefficient) ≤ (5 : ℝ)/2 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact cmLSeriesSummable_hasse_global (s := (y : ℂ)) (by simpa using hy)

theorem cmLSeries_analyticOn_hasse_halfPlane :
    AnalyticOn ℂ cmLSeries {s : ℂ | (5 : ℝ)/2 < s.re} := by
  unfold cmLSeries WeierstrassCurve.LSeries
  exact (LSeries.LSeries_analyticOn ((↑) ∘ cmAllNCoefficient)).mono (by
    intro s hs
    exact lt_of_le_of_lt cmLSeries_abscissaOfAbsConv_le_five_halves hs)

theorem cmLSeries_differentiableOn_hasse_halfPlane :
    DifferentiableOn ℂ cmLSeries {s : ℂ | (5 : ℝ)/2 < s.re} :=
  cmLSeries_analyticOn_hasse_halfPlane.differentiableOn

end Synthesis.Millennium.BSD
