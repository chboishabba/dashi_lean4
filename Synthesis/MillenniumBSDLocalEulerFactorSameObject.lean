import Synthesis.MillenniumBSDLocalPolynomialSameObject
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic

/-!
# Explicit prime-power recurrence = coefficients of the actual local reciprocal series

For every prime p, let

  S_p(X) = Σ A_p(n) X^n

where A_p is the already-defined second-order recurrence associated to

  P_p(X) = 1 - a_p X + p X².

We prove coefficientwise that P_p * S_p = 1.  Since P_p has constant
coefficient one, mathlib's `invOfUnit` is also a right inverse, and
cancellation identifies S_p with that canonical reciprocal series.

For odd p, the previously proved same-object theorem
`cmPadic_localPolynomial_eq_explicit` then transports this equality to
mathlib's actual `localPowerSeries`, and `ofPowerSeries_apply_pow` turns
the coefficient identity into an equality with `localEulerFactor (p^k)`.
-/

namespace Synthesis.Millennium.BSD

open Polynomial
open PowerSeries
open WeierstrassCurve
open IsLocalRing

def explicitPrimePowerSeries
    (p : ℕ) [Fact p.Prime] :
    ℤ⟦X⟧ :=
  PowerSeries.mk (explicitPrimePowerCoefficient p)

@[simp] theorem explicitPrimePowerSeries_coeff
    (p : ℕ) [Fact p.Prime]
    (n : ℕ) :
    PowerSeries.coeff n (explicitPrimePowerSeries p)
      =
    explicitPrimePowerCoefficient p n := by
  simp [explicitPrimePowerSeries]

def explicitGoodLocalDenominatorSeries
    (p : ℕ) [Fact p.Prime] :
    ℤ⟦X⟧ :=
  1
    - PowerSeries.C (frobeniusCoefficient p) * PowerSeries.X
    + PowerSeries.C (p : ℤ) * PowerSeries.X ^ 2

theorem explicitGoodLocalDenominatorSeries_eq_coe
    (p : ℕ) [Fact p.Prime] :
    explicitGoodLocalDenominatorSeries p
      =
    (explicitGoodLocalPolynomial p : ℤ⟦X⟧) := by
  simp [explicitGoodLocalDenominatorSeries,
    explicitGoodLocalPolynomial]

theorem explicitGoodLocalDenominator_mul_series
    (p : ℕ) [Fact p.Prime] :
    explicitGoodLocalDenominatorSeries p
      * explicitPrimePowerSeries p
      =
    1 := by
  rw [PowerSeries.ext_iff]
  intro n
  rcases n with (_ | _ | n)
  · simp [explicitGoodLocalDenominatorSeries,
      explicitPrimePowerSeries]
  · simp [explicitGoodLocalDenominatorSeries,
      explicitPrimePowerSeries]
  · simp only [explicitGoodLocalDenominatorSeries,
      add_mul, sub_mul, one_mul, PowerSeries.coeff_add,
      PowerSeries.coeff_sub]
    simp [PowerSeries.coeff_X_pow_mul',
      explicitPrimePowerSeries_coeff,
      explicitPrimePowerCoefficient_recurrence]
    ring

theorem explicitPrimePowerSeries_eq_invOfUnit
    (p : ℕ) [Fact p.Prime] :
    explicitPrimePowerSeries p
      =
    PowerSeries.invOfUnit
      (explicitGoodLocalPolynomial p : ℤ⟦X⟧)
      1 := by
  let P : ℤ⟦X⟧ :=
    (explicitGoodLocalPolynomial p : ℤ⟦X⟧)
  have hP0 : P ≠ 0 := by
    intro h
    have h0 := congrArg (PowerSeries.coeff 0) h
    simpa [P, explicitGoodLocalPolynomial] using h0
  have hleft :
      P * explicitPrimePowerSeries p = 1 := by
    rw [← explicitGoodLocalDenominatorSeries_eq_coe p]
    exact explicitGoodLocalDenominator_mul_series p
  have hinv :
      P * PowerSeries.invOfUnit P 1 = 1 := by
    apply PowerSeries.mul_invOfUnit
    simp [P, explicitGoodLocalPolynomial]
  exact mul_left_cancel₀ hP0 (hleft.trans hinv.symm)

theorem explicitPrimePowerCoefficient_eq_reciprocal_coeff
    (p : ℕ) [Fact p.Prime]
    (k : ℕ) :
    explicitPrimePowerCoefficient p k
      =
    PowerSeries.coeff k
      (PowerSeries.invOfUnit
        (explicitGoodLocalPolynomial p : ℤ⟦X⟧)
        1) := by
  rw [← explicitPrimePowerSeries_eq_invOfUnit p]
  simp

theorem cmPadic_localPowerSeries_eq_explicit
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (cmPadicWeierstrass p).localPowerSeries ℤ_[p]
      =
    explicitPrimePowerSeries p := by
  unfold WeierstrassCurve.localPowerSeries
  rw [cmPadic_localPolynomial_eq_explicit hp2]
  exact (explicitPrimePowerSeries_eq_invOfUnit p).symm

theorem cmPadic_localPowerSeries_coeff_eq_explicit
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (k : ℕ) :
    PowerSeries.coeff k
      ((cmPadicWeierstrass p).localPowerSeries ℤ_[p])
      =
    explicitPrimePowerCoefficient p k := by
  rw [cmPadic_localPowerSeries_eq_explicit hp2]
  simp

theorem cmPadic_localEulerFactor_primePower
    {p : ℕ} [Fact hp : p.Prime]
    (hp2 : p ≠ 2)
    (k : ℕ) :
    (cmPadicWeierstrass p).localEulerFactor ℤ_[p] (p ^ k)
      =
    explicitPrimePowerCoefficient p k := by
  unfold WeierstrassCurve.localEulerFactor
  rw [padicResidueField_natCard]
  rw [ArithmeticFunction.ofPowerSeries_apply_pow hp.out.one_lt]
  exact cmPadic_localPowerSeries_coeff_eq_explicit hp2 k

theorem inert_cmPadic_localEulerFactor_even
    {p : ℕ} [Fact p.Prime]
    (hmod : p % 4 = 3)
    (k : ℕ) :
    (cmPadicWeierstrass p).localEulerFactor ℤ_[p] (p ^ (2 * k))
      =
    (-(p : ℤ)) ^ k := by
  have hp2 : p ≠ 2 := by
    intro hp
    subst p
    norm_num at hmod
  rw [cmPadic_localEulerFactor_primePower hp2]
  exact inert_primePowerCoefficient_even hmod k

theorem inert_cmPadic_localEulerFactor_odd
    {p : ℕ} [Fact p.Prime]
    (hmod : p % 4 = 3)
    (k : ℕ) :
    (cmPadicWeierstrass p).localEulerFactor ℤ_[p] (p ^ (2 * k + 1))
      =
    0 := by
  have hp2 : p ≠ 2 := by
    intro hp
    subst p
    norm_num at hmod
  rw [cmPadic_localEulerFactor_primePower hp2]
  exact inert_primePowerCoefficient_odd hmod k

end Synthesis.Millennium.BSD
