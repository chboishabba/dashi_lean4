import Synthesis.MillenniumBSDGlobalCoefficientReconstruction
import Synthesis.MillenniumBSDExplicitEulerConvergence
import Mathlib.Tactic

/-!
# Analytic Euler product welded to the actual global local polynomials

The explicit convergence theorem was initially stated using the point-count
denominators.  The height-one completion weld now lets us replace those
denominators, prime by prime away from 2, by the actual localPolynomial used
inside mathlib's global WeierstrassCurve.LFunction.

We deliberately set the 2-factor to 1 in the prime-to-2 product until the
remaining additive-reduction classification at 2 is proved.
-/

namespace Synthesis.Millennium.BSD

open Polynomial

noncomputable def cmGlobalLocalDenominator
    (p : Nat.Primes) (s : ℂ) : ℂ :=
  if hp2 : p.1 = 2 then 1
  else
    letI : Fact p.1.Prime := ⟨p.2⟩
    Polynomial.eval₂ (Int.castRingHom ℂ)
      ((p.1 : ℂ) ^ (-s))
      ((cmWeierstrass.baseChange
        ((rationalPrimePlace p.1).adicCompletion ℚ)).localPolynomial
        ((rationalPrimePlace p.1).adicCompletionIntegers ℚ))

theorem cmGlobalLocalDenominator_eq_explicit
    (p : Nat.Primes) (s : ℂ) :
    cmGlobalLocalDenominator p s = explicitEulerDenominator p s := by
  by_cases hp2 : p.1 = 2
  · simp [cmGlobalLocalDenominator, explicitEulerDenominator,
      explicitEulerPerturbation, hp2]
  · letI : Fact p.1.Prime := ⟨p.2⟩
    rw [cmGlobalLocalDenominator, dif_neg hp2]
    rw [globalHeightOne_localPolynomial_eq_explicit hp2]
    rw [explicitEulerDenominator_eq_pointCountFactor p s hp2]
    simp [explicitGoodLocalPolynomial, Polynomial.eval₂_add,
      Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
    ring

theorem cmGlobalLocalDenominator_norm_perturbation_bound
    {s : ℂ} (hs : 2 < s.re) (p : Nat.Primes) :
    ‖cmGlobalLocalDenominator p s - 1‖
      ≤ (p.1 : ℝ) ^ (1 - s.re)
        + (p.1 : ℝ) ^ (1 - 2 * s.re) := by
  rw [cmGlobalLocalDenominator_eq_explicit]
  simpa [explicitEulerDenominator] using
    explicitEulerPerturbation_norm_le_majorant hs p

theorem cmGlobalLocalDenominator_ne_zero
    {s : ℂ} (hs : 2 < s.re) (p : Nat.Primes) :
    cmGlobalLocalDenominator p s ≠ 0 := by
  rw [cmGlobalLocalDenominator_eq_explicit]
  exact explicitEulerDenominator_ne_zero hs p

theorem cmGlobalLocalDenominators_multipliable
    {s : ℂ} (hs : 2 < s.re) :
    Multipliable fun p : Nat.Primes => cmGlobalLocalDenominator p s := by
  simpa only [cmGlobalLocalDenominator_eq_explicit] using
    explicitEulerDenominators_multipliable hs

noncomputable def cmPrimeToTwoEulerDenominatorProduct
    (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, cmGlobalLocalDenominator p s

theorem cmPrimeToTwoEulerDenominatorProduct_eq_explicit
    (s : ℂ) :
    cmPrimeToTwoEulerDenominatorProduct s =
      explicitEulerDenominatorProduct s := by
  apply tprod_congr
  intro p
  exact cmGlobalLocalDenominator_eq_explicit p s

theorem cmPrimeToTwoEulerDenominatorProduct_ne_zero
    {s : ℂ} (hs : 2 < s.re) :
    cmPrimeToTwoEulerDenominatorProduct s ≠ 0 := by
  rw [cmPrimeToTwoEulerDenominatorProduct_eq_explicit]
  exact explicitEulerDenominatorProduct_ne_zero hs

noncomputable def cmPrimeToTwoAnalyticEulerProduct
    (s : ℂ) : ℂ :=
  (cmPrimeToTwoEulerDenominatorProduct s)⁻¹

theorem cmPrimeToTwoAnalyticEulerProduct_eq_explicit
    (s : ℂ) :
    cmPrimeToTwoAnalyticEulerProduct s =
      explicitAnalyticEulerProduct s := by
  simp [cmPrimeToTwoAnalyticEulerProduct,
    explicitAnalyticEulerProduct,
    cmPrimeToTwoEulerDenominatorProduct_eq_explicit]

theorem cmPrimeToTwoAnalyticEulerProduct_ne_zero
    {s : ℂ} (hs : 2 < s.re) :
    cmPrimeToTwoAnalyticEulerProduct s ≠ 0 := by
  rw [cmPrimeToTwoAnalyticEulerProduct_eq_explicit]
  exact explicitAnalyticEulerProduct_ne_zero hs

theorem cmPrimeToTwoAnalyticEulerProduct_mul_denominator
    {s : ℂ} (hs : 2 < s.re) :
    cmPrimeToTwoAnalyticEulerProduct s
      * cmPrimeToTwoEulerDenominatorProduct s = 1 := by
  exact inv_mul_cancel₀
    (cmPrimeToTwoEulerDenominatorProduct_ne_zero hs)

end Synthesis.Millennium.BSD
