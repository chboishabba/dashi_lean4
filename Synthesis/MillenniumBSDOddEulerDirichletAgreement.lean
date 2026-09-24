import Synthesis.MillenniumBSDOddDirichletConvergence
import Synthesis.MillenniumBSDGlobalAnalyticEulerWeld
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Tactic

/-!
# Prime-to-2 Dirichlet series = actual global Euler product

For Re(s)>3 the odd-part coefficient Dirichlet series is absolutely
convergent.  At every odd prime, evaluate the already-proved formal reciprocal
power series at z=p^{-s}; this identifies the prime-power sum with the inverse
of the actual height-one local polynomial.  The p=2 local sum is 1 because
the odd-part arithmetic function vanishes on positive powers of 2.

Mathlib's general Euler-product theorem then gives a genuine analytic
Dirichlet/Euler agreement for the literal global curve, prime to 2.
-/

namespace Synthesis.Millennium.BSD

open ArithmeticFunction
open PowerSeries

noncomputable def cmOddDirichletArithmeticFunction
    (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨cmOddDirichletSummand s, by
    simp [cmOddDirichletSummand]⟩

theorem cmOddDirichletArithmeticFunction_apply
    (s : ℂ) (n : ℕ) :
    cmOddDirichletArithmeticFunction s n =
      cmOddDirichletSummand s n := rfl

theorem cmOddDirichletArithmeticFunction_isMultiplicative
    (s : ℂ) :
    ArithmeticFunction.IsMultiplicative
      (cmOddDirichletArithmeticFunction s) := by
  constructor
  · simp [cmOddDirichletArithmeticFunction, cmOddDirichletSummand,
      cmAllNCoefficient_one]
  · intro m n hmn
    by_cases hm : Odd m
    · by_cases hn : Odd n
      · have hmnodd : Odd (m*n) := hm.mul hn
        rw [cmOddDirichletArithmeticFunction_apply,
          cmOddDirichletArithmeticFunction_apply,
          cmOddDirichletArithmeticFunction_apply]
        simp only [cmOddDirichletSummand, if_pos hm, if_pos hn, if_pos hmnodd]
        rw [cmAllNCoefficient_coprime_mul hmn]
        push_cast
        rw [Complex.natCast_mul_natCast_cpow]
        ring
      · have hmnnot : ¬ Odd (m*n) := by
          simpa [Nat.odd_mul] using not_and_of_not_right (Odd m) hn
        simp [cmOddDirichletArithmeticFunction, cmOddDirichletSummand,
          hm, hn, hmnnot]
    · have hmnnot : ¬ Odd (m*n) := by
        simpa [Nat.odd_mul] using not_and_of_not_left (Odd n) hm
      simp [cmOddDirichletArithmeticFunction, cmOddDirichletSummand,
        hm, hmnnot]

theorem cmOddDirichletArithmeticFunction_norm_summable
    {s : ℂ} (hs : 3 < s.re) :
    Summable fun n : ℕ =>
      ‖cmOddDirichletArithmeticFunction s n‖ := by
  have hmaj : Summable (fun n : ℕ => (n : ℝ) ^ (2 - s.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact hmaj.of_nonneg_of_le
    (fun n => norm_nonneg (cmOddDirichletArithmeticFunction s n))
    (fun n => by
      simpa [cmOddDirichletArithmeticFunction_apply] using
        cmOddDirichletSummand_norm_le hs n)

theorem norm_prime_cpow_neg_lt_one
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_natCast_cpow_of_pos hp.pos (-s)]
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  simpa using Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith : -s.re < 0)

theorem primeCpowNeg_hasEval
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    PowerSeries.HasEval ((p : ℂ) ^ (-s)) := by
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (norm_prime_cpow_neg_lt_one hp hs)

theorem explicitPrimePowerSeries_hasSum_at_cpow
    {p : ℕ} [Fact hp : p.Prime]
    {s : ℂ} (hs : 0 < s.re) :
    HasSum
      (fun k : ℕ =>
        (explicitPrimePowerCoefficient p k : ℂ)
          * ((p : ℂ) ^ (-s)) ^ k)
      (PowerSeries.eval₂ (Int.castRingHom ℂ)
        ((p : ℂ) ^ (-s)) (explicitPrimePowerSeries p)) := by
  simpa [explicitPrimePowerSeries_coeff] using
    PowerSeries.hasSum_eval₂
      (φ := Int.castRingHom ℂ)
      (a := (p : ℂ) ^ (-s))
      (by fun_prop)
      (primeCpowNeg_hasEval hp.out hs)
      (explicitPrimePowerSeries p)

theorem explicitPrimePowerSeries_eval_mul_denominator
    {p : ℕ} [Fact hp : p.Prime]
    (hp2 : p ≠ 2) {s : ℂ} (hs : 0 < s.re) :
    explicitEulerDenominator ⟨p, hp.out⟩ s
      * PowerSeries.eval₂ (Int.castRingHom ℂ)
          ((p : ℂ) ^ (-s)) (explicitPrimePowerSeries p)
      = 1 := by
  let z : ℂ := (p : ℂ) ^ (-s)
  have hz : PowerSeries.HasEval z :=
    primeCpowNeg_hasEval hp.out (by linarith)
  let ev : ℤ⟦X⟧ →+* ℂ :=
    PowerSeries.eval₂Hom
      (φ := Int.castRingHom ℂ) (a := z)
      (by fun_prop) hz
  have hid := congrArg ev
    (explicitGoodLocalDenominator_mul_series p)
  change ev (explicitGoodLocalDenominatorSeries p)
      * ev (explicitPrimePowerSeries p) = ev 1 at hid
  have hden :
      ev (explicitGoodLocalDenominatorSeries p)
        = explicitEulerDenominator ⟨p, hp.out⟩ s := by
    rw [explicitGoodLocalDenominatorSeries_eq_coe]
    change Polynomial.eval₂ (Int.castRingHom ℂ) z
      (explicitGoodLocalPolynomial p)
      = explicitEulerDenominator ⟨p, hp.out⟩ s
    rw [explicitEulerDenominator_eq_pointCountFactor ⟨p, hp.out⟩ s hp2]
    simp [explicitGoodLocalPolynomial, z]
    ring
  have hseries :
      ev (explicitPrimePowerSeries p)
        = PowerSeries.eval₂ (Int.castRingHom ℂ) z
          (explicitPrimePowerSeries p) := by
    rfl
  simpa [hden, hseries, map_one] using hid

theorem oddPrimePowerTsum_eq_localDenominator_inv
    {p : ℕ} [Fact hp : p.Prime]
    (hp2 : p ≠ 2) {s : ℂ} (hs : 3 < s.re) :
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
    (p := p) hp2 (s := s) (by linarith : 2 < s.re)
  have hne := explicitEulerDenominator_ne_zero
    (p := ⟨p, hp.out⟩) (by linarith : 2 < s.re)
  rw [← cmGlobalLocalDenominator_eq_explicit ⟨p, hp.out⟩ s]
  rw [show (∑' k : ℕ, cmOddDirichletArithmeticFunction s (p^k))
      = ∑' k : ℕ,
        (explicitPrimePowerCoefficient p k : ℂ)
          * ((p : ℂ)^(-s))^k by
        apply tsum_congr; intro k; exact hterm k]
  rw [hsum.tsum_eq]
  exact (eq_inv_of_mul_eq_one_left hne hden).symm

theorem twoPowerTsum_oddPart_eq_one
    (s : ℂ) :
    (∑' k : ℕ, cmOddDirichletArithmeticFunction s (2 ^ k)) = 1 := by
  have hterm :
      (fun k : ℕ => cmOddDirichletArithmeticFunction s (2^k))
        = Function.update (fun _ : ℕ => (0 : ℂ)) 0 1 := by
    funext k
    cases k with
    | zero => simp [cmOddDirichletArithmeticFunction, cmOddDirichletSummand,
        cmAllNCoefficient_one]
    | succ k =>
        have hnot : ¬ Odd (2 ^ (k+1)) := by
          exact Nat.not_odd_iff_even.mpr
            (Even.pow (by decide : Even 2) (Nat.succ_ne_zero k))
        simp [cmOddDirichletArithmeticFunction, cmOddDirichletSummand, hnot]
  rw [hterm]
  simp

theorem primePowerTsum_oddPart_eq_localDenominator_inv
    (p : Nat.Primes) {s : ℂ} (hs : 3 < s.re) :
    (∑' k : ℕ, cmOddDirichletArithmeticFunction s (p.1 ^ k))
      = (cmGlobalLocalDenominator p s)⁻¹ := by
  by_cases hp2 : p.1 = 2
  · subst p
    simp [twoPowerTsum_oddPart_eq_one, cmGlobalLocalDenominator]
  · letI : Fact p.1.Prime := ⟨p.2⟩
    exact oddPrimePowerTsum_eq_localDenominator_inv hp2 hs

theorem cmOddLSeries_eq_primeToTwoAnalyticEulerProduct
    {s : ℂ} (hs : 3 < s.re) :
    cmOddLSeries s = cmPrimeToTwoAnalyticEulerProduct s := by
  have heuler :
      (∏' p : Nat.Primes,
        ∑' k : ℕ, cmOddDirichletArithmeticFunction s (p.1 ^ k))
        = ∑' n : ℕ, cmOddDirichletArithmeticFunction s n :=
    (cmOddDirichletArithmeticFunction_isMultiplicative s).eulerProduct_tprod
      (cmOddDirichletArithmeticFunction_norm_summable hs)
  have hlocal :
      (fun p : Nat.Primes =>
        ∑' k : ℕ, cmOddDirichletArithmeticFunction s (p.1 ^ k))
        = fun p : Nat.Primes => (cmGlobalLocalDenominator p s)⁻¹ := by
    funext p
    exact primePowerTsum_oddPart_eq_localDenominator_inv p hs
  rw [hlocal, tprod_inv] at heuler
  change (cmPrimeToTwoEulerDenominatorProduct s)⁻¹
      = cmOddLSeries s at heuler
  exact heuler.symm

theorem cmOddLSeries_ne_zero
    {s : ℂ} (hs : 3 < s.re) :
    cmOddLSeries s ≠ 0 := by
  rw [cmOddLSeries_eq_primeToTwoAnalyticEulerProduct hs]
  exact cmPrimeToTwoAnalyticEulerProduct_ne_zero (by linarith)

end Synthesis.Millennium.BSD
