import Synthesis.MillenniumBSDGlobalCompletionReductionWeld
import Synthesis.MillenniumBSDLocalEulerFactorSameObject
import Mathlib.Tactic

/-!
# Actual global-completion local factors equal the explicit factors

This is the globalization theorem for the odd-prime local factors used by
mathlib's WeierstrassCurve.LFunction.  Unlike the earlier Q_p theorem, the
left-hand side here is formed on the exact height-one completion and integer
ring appearing in the global Euler product.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open Polynomial
open PowerSeries
open IsLocalRing

theorem cmGlobalPrime_localPolynomial_eq_explicit
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (cmGlobalPrimeCurve p).localPolynomial (RationalPrimeIntegers p)
      = explicitGoodLocalPolynomial p := by
  letI : WeierstrassCurve.HasGoodReduction (RationalPrimeIntegers p)
      (cmGlobalChosenMinimal p) :=
    cmGlobalChosenMinimal_hasGoodReduction hp2
  rw [WeierstrassCurve.localPolynomial]
  dsimp only [cmGlobalChosenMinimal]
  rw [if_pos (by infer_instance :
    WeierstrassCurve.HasGoodReduction (RationalPrimeIntegers p)
      (cmGlobalChosenMinimal p))]
  rw [rationalPrimeResidueField_natCard]
  rw [cmGlobalChosenReduction_point_card_eq_projectivePointCount hp2]
  unfold explicitGoodLocalPolynomial frobeniusCoefficient
  congr 1 <;> norm_num

theorem cmGlobalPrime_localPowerSeries_eq_explicit
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (cmGlobalPrimeCurve p).localPowerSeries (RationalPrimeIntegers p)
      = explicitPrimePowerSeries p := by
  unfold WeierstrassCurve.localPowerSeries
  rw [cmGlobalPrime_localPolynomial_eq_explicit hp2]
  exact (explicitPrimePowerSeries_eq_invOfUnit p).symm

theorem cmGlobalPrime_localPowerSeries_coeff_eq_explicit
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (k : ℕ) :
    PowerSeries.coeff k
      ((cmGlobalPrimeCurve p).localPowerSeries (RationalPrimeIntegers p))
      = explicitPrimePowerCoefficient p k := by
  rw [cmGlobalPrime_localPowerSeries_eq_explicit hp2]
  simp

theorem cmGlobalPrime_localEulerFactor_primePower
    {p : ℕ} [Fact hp : p.Prime] (hp2 : p ≠ 2) (k : ℕ) :
    (cmGlobalPrimeCurve p).localEulerFactor (RationalPrimeIntegers p) (p ^ k)
      = explicitPrimePowerCoefficient p k := by
  unfold WeierstrassCurve.localEulerFactor
  rw [rationalPrimeResidueField_natCard]
  rw [ArithmeticFunction.ofPowerSeries_apply_pow hp.out.one_lt]
  exact cmGlobalPrime_localPowerSeries_coeff_eq_explicit hp2 k

theorem globalHeightOne_localPolynomial_eq_explicit
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (cmWeierstrass.baseChange ((rationalPrimePlace p).adicCompletion ℚ)).localPolynomial
      ((rationalPrimePlace p).adicCompletionIntegers ℚ)
      = explicitGoodLocalPolynomial p := by
  exact cmGlobalPrime_localPolynomial_eq_explicit hp2

theorem globalHeightOne_localEulerFactor_primePower
    {p : ℕ} [Fact hp : p.Prime] (hp2 : p ≠ 2) (k : ℕ) :
    (cmWeierstrass.baseChange ((rationalPrimePlace p).adicCompletion ℚ)).localEulerFactor
      ((rationalPrimePlace p).adicCompletionIntegers ℚ) (p ^ k)
      = explicitPrimePowerCoefficient p k := by
  exact cmGlobalPrime_localEulerFactor_primePower hp2 k

theorem globalHeightOne_localPolynomial_eq_padic
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (cmWeierstrass.baseChange ((rationalPrimePlace p).adicCompletion ℚ)).localPolynomial
      ((rationalPrimePlace p).adicCompletionIntegers ℚ)
      = (cmPadicWeierstrass p).localPolynomial ℤ_[p] := by
  rw [globalHeightOne_localPolynomial_eq_explicit hp2,
    cmPadic_localPolynomial_eq_explicit hp2]

theorem globalHeightOne_localPowerSeries_eq_padic
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (cmWeierstrass.baseChange ((rationalPrimePlace p).adicCompletion ℚ)).localPowerSeries
      ((rationalPrimePlace p).adicCompletionIntegers ℚ)
      = (cmPadicWeierstrass p).localPowerSeries ℤ_[p] := by
  rw [cmGlobalPrime_localPowerSeries_eq_explicit hp2,
    cmPadic_localPowerSeries_eq_explicit hp2]

end Synthesis.Millennium.BSD
