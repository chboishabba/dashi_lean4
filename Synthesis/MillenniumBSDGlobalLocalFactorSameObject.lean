import Synthesis.MillenniumBSDGlobalCompletionReductionWeld
import Synthesis.MillenniumBSDGlobalBadPrimeTwo
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

/-- The actual local polynomial at every rational prime, including the bad prime 2. -/
theorem globalHeightOne_localPolynomial_all_primes
    {p : ℕ} [Fact hp : p.Prime] :
    (cmWeierstrass.baseChange ((rationalPrimePlace p).adicCompletion ℚ)).localPolynomial
      ((rationalPrimePlace p).adicCompletionIntegers ℚ)
      =
    if p = 2 then 1 else explicitGoodLocalPolynomial p := by
  by_cases hp2 : p = 2
  · subst p
    simp [globalHeightOne_localPolynomial_two_eq_one]
  · simp [hp2, globalHeightOne_localPolynomial_eq_explicit hp2]

/-- Full prime-power coefficient for the actual local factor.
At p=2 the additive local factor is 1, hence only k=0 survives. -/
noncomputable def explicitAllPrimePowerCoefficient
    (p : ℕ) [Fact p.Prime] (k : ℕ) : ℤ :=
  if p = 2 then
    if k = 0 then 1 else 0
  else explicitPrimePowerCoefficient p k

theorem globalHeightOne_localEulerFactor_all_primePower
    {p : ℕ} [Fact hp : p.Prime] (k : ℕ) :
    (cmWeierstrass.baseChange ((rationalPrimePlace p).adicCompletion ℚ)).localEulerFactor
      ((rationalPrimePlace p).adicCompletionIntegers ℚ) (p ^ k)
      = explicitAllPrimePowerCoefficient p k := by
  by_cases hp2 : p = 2
  · subst p
    unfold WeierstrassCurve.localEulerFactor
    rw [rationalPrimeResidueField_natCard]
    rw [show rationalHeightOneNorm (rationalPrimePlace 2) = 2 by
      simp [rationalHeightOneNorm, rationalPrimePlace]]
    unfold WeierstrassCurve.localPowerSeries
    rw [globalHeightOne_localPolynomial_two_eq_one]
    simp [explicitAllPrimePowerCoefficient]
  · rw [globalHeightOne_localEulerFactor_primePower hp2 k]
    simp [explicitAllPrimePowerCoefficient, hp2]

theorem explicitAllPrimePowerCoefficient_two
    (k : ℕ) :
    @explicitAllPrimePowerCoefficient 2 ⟨Nat.prime_two⟩ k
      = if k = 0 then 1 else 0 := by
  simp [explicitAllPrimePowerCoefficient]

theorem explicitAllPrimePowerCoefficient_odd
    {p : ℕ} [Fact hp : p.Prime] (hp2 : p ≠ 2) (k : ℕ) :
    explicitAllPrimePowerCoefficient p k = explicitPrimePowerCoefficient p k := by
  simp [explicitAllPrimePowerCoefficient, hp2]


end Synthesis.Millennium.BSD
