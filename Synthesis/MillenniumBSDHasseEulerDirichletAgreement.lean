import Synthesis.MillenniumBSDHasseGlobalCoefficientBound
import Synthesis.MillenniumBSDHasseEulerConvergence
import Synthesis.MillenniumBSDOddEulerDirichletAgreement
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Tactic

/-!
# Hasse-strength Dirichlet / Euler agreement for the literal global L-function

The Hasse/Chebyshev global bound makes the literal L-series absolutely
convergent for Re(s)>5/2.  The local reciprocal-series identity only needs
Re(s)>0, while Hasse gives denominator nonvanishing already for Re(s)>3/2.

Therefore mathlib's general Euler-product theorem identifies the literal
global cmLSeries with the actual all-prime Euler product throughout
Re(s)>5/2.
-/

namespace Synthesis.Millennium.BSD

open ArithmeticFunction

theorem cmOddDirichletArithmeticFunction_eq_LSeriesTerm
    (s : ℂ) (n : ℕ) :
    cmOddDirichletArithmeticFunction s n =
      LSeries.term ((↑) ∘ cmAllNCoefficient) s n := by
  rw [cmOddDirichletArithmeticFunction_apply]
  rw [cmOddDirichletSummand_eq_LSeriesTerm]
  apply LSeries.term_congr
  intro m hm
  simpa [Function.comp_apply] using cmOddCoefficient_eq_globalCoefficient m

theorem cmOddDirichletArithmeticFunction_norm_summable_hasse
    {s : ℂ} (hs : (5 : ℝ)/2 < s.re) :
    Summable fun n : ℕ => ‖cmOddDirichletArithmeticFunction s n‖ := by
  have hsum := cmLSeriesSummable_hasse_global hs
  rw [LSeriesSummable, ← summable_norm_iff] at hsum
  exact hsum.congr (fun n => by
    rw [cmOddDirichletArithmeticFunction_eq_LSeriesTerm])

theorem oddPrimePowerTsum_eq_localDenominator_inv_hasse
    {p : ℕ} [Fact hp : p.Prime]
    (hp2 : p ≠ 2) {s : ℂ} (hs : (3 : ℝ)/2 < s.re) :
    (∑' k : ℕ,
      cmOddDirichletArithmeticFunction s (p ^ k))
      = (cmGlobalLocalDenominator ⟨p, hp.out⟩ s)⁻¹ := by
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  have hterm (k : ℕ) :
      cmOddDirichletArithmeticFunction s (p ^ k)
        = (explicitPrimePowerCoefficient p k : ℂ)
            * ((p : ℂ) ^ (-s)) ^ k := by
    rw [cmOddDirichletArithmeticFunction_apply]
    have hpPowOdd : Odd (p^k) := hpodd.pow
    rw [cmOddDirichletSummand, if_pos hpPowOdd]
    rw [cmAllNCoefficient_odd_primePower hp2 k]
    rw [← Complex.natCast_cpow_natCast_mul p k (-s)]
    congr 1
    ring
  have hsum := explicitPrimePowerSeries_hasSum_at_cpow
    (p := p) (s := s) (by linarith : 0 < s.re)
  have hden := explicitPrimePowerSeries_eval_mul_denominator
    (p := p) hp2 (s := s) (by linarith : 0 < s.re)
  have hne := explicitEulerDenominator_ne_zero_hasse
    (p := ⟨p, hp.out⟩) hs
  rw [← cmGlobalLocalDenominator_eq_explicit ⟨p, hp.out⟩ s]
  rw [show (∑' k : ℕ, cmOddDirichletArithmeticFunction s (p^k))
      = ∑' k : ℕ,
        (explicitPrimePowerCoefficient p k : ℂ)
          * ((p : ℂ)^(-s))^k by
        apply tsum_congr
        intro k
        exact hterm k]
  rw [hsum.tsum_eq]
  exact (eq_inv_of_mul_eq_one_left hne hden).symm

theorem primePowerTsum_global_eq_actualLocalDenominator_inv_hasse
    (p : Nat.Primes) {s : ℂ} (hs : (3 : ℝ)/2 < s.re) :
    (∑' k : ℕ, cmOddDirichletArithmeticFunction s (p.1 ^ k))
      = (cmActualGlobalLocalDenominator p s)⁻¹ := by
  rw [cmActualGlobalLocalDenominator_eq_cmGlobalLocalDenominator]
  by_cases hp2 : p.1 = 2
  · have hpEq : p = ⟨2, Nat.prime_two⟩ := by
      apply Subtype.ext
      exact hp2
    subst p
    simp [twoPowerTsum_oddPart_eq_one, cmGlobalLocalDenominator]
  · letI : Fact p.1.Prime := ⟨p.2⟩
    exact oddPrimePowerTsum_eq_localDenominator_inv_hasse hp2 hs

theorem cmLSeries_eq_actualGlobalEulerProduct_hasse
    {s : ℂ} (hs : (5 : ℝ)/2 < s.re) :
    cmLSeries s = cmActualGlobalAnalyticEulerProduct s := by
  have heuler :
      (∏' p : Nat.Primes,
        ∑' k : ℕ, cmOddDirichletArithmeticFunction s (p.1 ^ k))
        = ∑' n : ℕ, cmOddDirichletArithmeticFunction s n :=
    (cmOddDirichletArithmeticFunction_isMultiplicative s).eulerProduct_tprod
      (cmOddDirichletArithmeticFunction_norm_summable_hasse hs)
  have hlocal :
      (fun p : Nat.Primes =>
        ∑' k : ℕ, cmOddDirichletArithmeticFunction s (p.1 ^ k))
        = fun p : Nat.Primes => (cmActualGlobalLocalDenominator p s)⁻¹ := by
    funext p
    exact primePowerTsum_global_eq_actualLocalDenominator_inv_hasse p
      (by linarith)
  rw [hlocal, tprod_inv] at heuler
  change (cmActualGlobalEulerDenominatorProduct s)⁻¹
      = ∑' n : ℕ, cmOddDirichletArithmeticFunction s n at heuler
  have hsumEq :
      (∑' n : ℕ, cmOddDirichletArithmeticFunction s n) = cmLSeries s := by
    rw [← cmLSeries_eq_cmOddLSeries s]
    rfl
  rw [hsumEq] at heuler
  exact heuler.symm

theorem cmLSeries_ne_zero_hasse
    {s : ℂ} (hs : (5 : ℝ)/2 < s.re) :
    cmLSeries s ≠ 0 := by
  rw [cmLSeries_eq_actualGlobalEulerProduct_hasse hs]
  exact cmActualGlobalAnalyticEulerProduct_ne_zero_hasse (by linarith)

end Synthesis.Millennium.BSD
