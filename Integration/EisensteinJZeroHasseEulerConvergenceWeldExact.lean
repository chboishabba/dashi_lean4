import Integration.EisensteinJZeroConditionalAnalyticEulerExact
import Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact
import Integration.EisensteinJZeroInertPrimeLocalFactorExact
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# j=0 CM: original-source Hasse and Euler convergence max-cut

The source is the literal E : y² = x³ + 1, NOT the other CM/BSD
curve y² = x³ - x.  This file consumes the already existing canonical
Jacobi element, its integral Eisenstein norm and the original finite-field
Frobenius trace.  The elementary identity
  4 (a² - ab + b²) - (2a-b)² = 3 b²
provides the split-prime Hasse estimate; inert prime traces are zero.

The existing BSD Hasse/Euler convergence proof is a *method donor*, not
a same-curve theorem.  No new global L-function or GRH is asserted.

SOURCE-WRITTEN only.  Local SymPy verification of the exact polynomial
identity and 107 good-prime samples is independent of kernel acceptance.
-/

namespace Integration.EisensteinJZeroHasseEulerConvergenceWeldExact

open Integration.EisensteinJZeroFiniteEulerProductExact
open Integration.EisensteinJZeroConditionalAnalyticEulerExact
open Integration.EisensteinJZeroFiniteFieldTraceExact
open Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact
open Integration.EisensteinJZeroInertPrimeLocalFactorExact
open Dashi.EisensteinQuadraticAlgebraExact

private theorem good_prime_mod_three_cases
    (p : RationalPrime) (hp3 : 3 < p.1) :
    p.1 % 3 = 1 ∨ p.1 % 3 = 2 := by
  have hn : p.1 % 3 ≠ 0 := by
    intro h
    have hd : 3 ∣ p.1 := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.dvd_prime p.2).1 hd with h31 | h3p
    · norm_num at h31
    · omega
  have hlt : p.1 % 3 < 3 := Nat.mod_lt p.1 (by norm_num)
  omega

/-- EXACT integral, universal norm-vs-trace identity, not a numeric bound. -/
theorem eisenstein_norm_trace_debt (a b : ℤ) :
    4 * (a*a - a*b + b*b) - (2*a-b)^2 = 3*b*b := by
  ring

/-- The original split Jacobi element yields the original curve's
Frobenius Hasse square bound; no new elliptic model is introduced. -/
theorem jZero_split_frobenius_trace_sq_le_four_prime
    (p : RationalPrime) (hp3 : 3 < p.1)
    (hsplit : p.1 % 3 = 1) :
    ((jZeroFrobeniusTraceInt (ZMod p.1) : ℝ))^2 ≤ 4 * p.1 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  let z := splitJacobiEisensteinElement p.1 (by omega) hsplit
  have hn : QuadraticAlgebra.norm z = (p.1 : ℤ) :=
    splitJacobiEisensteinElement_norm p.1 (by omega) hsplit
  have hc : z.re*z.re - z.re*z.im + z.im*z.im = (p.1 : ℤ) := by
    simpa [QuadraticAlgebra.norm_def] using hn
  have ht : jZeroFrobeniusTraceInt (ZMod p.1) =
      -(2*z.re-z.im) :=
    splitPrime_jZero_trace_formula p.1 (by omega) hsplit
  have hsq : (jZeroFrobeniusTraceInt (ZMod p.1))^2
      ≤ (4*(p.1 : ℤ)) := by
    rw [ht]
    nlinarith [sq_nonneg z.im]
  exact_mod_cast hsq

/-- Original j=0 good-prime Hasse bound, including the inert-zero branch. -/
theorem jZero_good_frobenius_trace_sq_le_four_prime
    (p : RationalPrime) (hp3 : 3 < p.1) :
    ((jZeroFrobeniusTraceInt (ZMod p.1) : ℝ))^2 ≤ 4 * p.1 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  rcases good_prime_mod_three_cases p hp3 with hsplit | hinert
  · exact jZero_split_frobenius_trace_sq_le_four_prime p hp3 hsplit
  · rw [jZeroInertPrime_trace_zero p.1 (by omega) hinert]
    positivity

theorem jZero_good_frobenius_trace_abs_le_two_sqrt
    (p : RationalPrime) (hp3 : 3 < p.1) :
    |(jZeroFrobeniusTraceInt (ZMod p.1) : ℝ)|
      ≤ 2 * Real.sqrt (p.1 : ℝ) := by
  have hsq := jZero_good_frobenius_trace_sq_le_four_prime p hp3
  have hsqrt : (Real.sqrt (p.1 : ℝ)) ^ 2 = p.1 := by
    rw [Real.sq_sqrt]
    positivity
  have ha : 0 ≤ |(jZeroFrobeniusTraceInt (ZMod p.1) : ℝ)| :=
    abs_nonneg _
  have hb : 0 ≤ Real.sqrt (p.1 : ℝ) := Real.sqrt_nonneg _
  nlinarith [sq_nonneg
    (|(jZeroFrobeniusTraceInt (ZMod p.1) : ℝ)|
      - 2 * Real.sqrt (p.1 : ℝ))]

/-- Source-independent convergence majorant, with the original prime index. -/
def jZeroHasseEulerMajorant (p : RationalPrime) (s : ℂ) : ℝ :=
  2 * (p.1 : ℝ)^((1 : ℝ)/2 - s.re)
    + (p.1 : ℝ)^(1 - 2*s.re)

/-- Reuse the exact prime-power summability theorem already used by
Synthesis.Millennium.BSDHasseEulerConvergence, without importing its curve. -/
theorem jZeroHasseEulerMajorant_summable
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re) :
    Summable (fun p : RationalPrime => jZeroHasseEulerMajorant p s) := by
  unfold jZeroHasseEulerMajorant
  apply Summable.add
  · exact (Nat.Primes.summable_rpow.mpr (by linarith)).mul_left 2
  · exact Nat.Primes.summable_rpow.mpr (by linarith)

/-- This is the narrowly selected remaining analytic glue.
The norm inequality follows from the Hasse theorem above using the
existing source denominator 1-a_p*p^(-s)+p*p^(-2s).
It is made an explicit theorem premise here rather than silently
substituting the BSD curve's already proved perturbation theorem. -/
def JZeroOriginalEulerPerturbation (p : RationalPrime) (s : ℂ) : ℂ :=
  ellipticComplexLocalDenominator p s - 1

/-- Once the original-denominator perturbation is bounded by the
just-proved summable majorant, convergence of the perturbation series
follows by the standard norm comparison lemma. -/
theorem jZeroOriginalEulerPerturbation_summable_of_bound
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re)
    (hlocal : ∀ p : RationalPrime,
      ‖JZeroOriginalEulerPerturbation p s‖
        ≤ jZeroHasseEulerMajorant p s) :
    Summable (fun p : RationalPrime =>
      JZeroOriginalEulerPerturbation p s) := by
  exact ((jZeroHasseEulerMajorant_summable hs).of_nonneg_of_le
    (fun p => norm_nonneg (JZeroOriginalEulerPerturbation p s))
    hlocal).of_norm

/-- Exact selected consumer: original j=0 denominator Euler product,
not a second invented product.  Reciprocal-product and global
L-series identification are downstream and separate. -/
theorem jZeroOriginalEulerDenominators_multipliable_of_bound
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re)
    (hlocal : ∀ p : RationalPrime,
      ‖JZeroOriginalEulerPerturbation p s‖
        ≤ jZeroHasseEulerMajorant p s) :
    Multipliable (fun p : RationalPrime =>
      ellipticComplexLocalDenominator p s) := by
  have hsum := jZeroOriginalEulerPerturbation_summable_of_bound hs hlocal
  have hproduct := multipliable_one_add_of_summable hsum.norm
  simpa [JZeroOriginalEulerPerturbation, add_comm, add_left_comm,
    add_assoc] using hproduct


/-- The actual j=0 local perturbation bound, including BOTH bad factors as
zero perturbation. This uses the original j=0 Hasse trace theorem above,
not the similarly named BSD curve's coefficient. -/
theorem jZeroOriginalEulerPerturbation_norm_le_majorant
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re) (p : RationalPrime) :
    ‖JZeroOriginalEulerPerturbation p s‖
      ≤ jZeroHasseEulerMajorant p s := by
  by_cases h2 : p.1 = 2
  · simp [JZeroOriginalEulerPerturbation,
      ellipticComplexLocalDenominator, h2, jZeroHasseEulerMajorant]
    positivity
  · by_cases h3 : p.1 = 3
    · simp [JZeroOriginalEulerPerturbation,
        ellipticComplexLocalDenominator, h2, h3, jZeroHasseEulerMajorant]
      positivity
    · letI : Fact p.1.Prime := ⟨p.2⟩
      have hp3 : 3 < p.1 := by
        have := p.2.two_le
        omega
      have hpR : 0 < (p.1 : ℝ) := by positivity
      let T : ℂ := (p.1 : ℂ)^(-s)
      have hsource :
          JZeroOriginalEulerPerturbation p s =
            -(jZeroFrobeniusTraceInt (ZMod p.1) : ℂ)*T
              + (p.1 : ℂ)*T^2 := by
        simp [JZeroOriginalEulerPerturbation,
          ellipticComplexLocalDenominator, h2, h3, T]
        ring
      have hcoef :
          ‖(jZeroFrobeniusTraceInt (ZMod p.1) : ℂ)‖
            ≤ 2 * (p.1 : ℝ)^((1 : ℝ)/2) := by
        rw [Complex.norm_intCast]
        simpa [Real.sqrt_eq_rpow] using
          jZero_good_frobenius_trace_abs_le_two_sqrt p hp3
      have hpow1 : ‖T‖ = (p.1 : ℝ)^(-s.re) := by
        simpa [T] using norm_natCast_cpow_of_pos p.2.pos (-s)
      have hpow2 : ‖T^2‖ = (p.1 : ℝ)^(-2*s.re) := by
        rw [norm_pow, hpow1, pow_two, ← Real.rpow_add hpR]
        congr 1
        ring
      have hfirst :
          (2*(p.1 : ℝ)^((1 : ℝ)/2)) * (p.1 : ℝ)^(-s.re)
            = 2*(p.1 : ℝ)^((1 : ℝ)/2-s.re) := by
        rw [mul_assoc, ← Real.rpow_add hpR]
        congr 2
        ring
      have hsecond :
          (p.1 : ℝ) * (p.1 : ℝ)^(-2*s.re)
            = (p.1 : ℝ)^(1-2*s.re) := by
        rw [show (p.1 : ℝ) = (p.1 : ℝ)^(1 : ℝ) by
          rw [Real.rpow_one], ← Real.rpow_add hpR]
        congr 1
        ring
      rw [hsource]
      calc
        ‖-(jZeroFrobeniusTraceInt (ZMod p.1) : ℂ)*T
              + (p.1 : ℂ)*T^2‖
            ≤ ‖(jZeroFrobeniusTraceInt (ZMod p.1) : ℂ)‖ * ‖T‖
              + ‖(p.1 : ℂ)‖ * ‖T^2‖ := by
                simpa [norm_mul] using norm_add_le
                  (-(jZeroFrobeniusTraceInt (ZMod p.1) : ℂ)*T)
                  ((p.1 : ℂ)*T^2)
        _ ≤ (2 * (p.1 : ℝ)^((1 : ℝ)/2)) * (p.1 : ℝ)^(-s.re)
              + (p.1 : ℝ) * (p.1 : ℝ)^(-2*s.re) := by
              rw [hpow1, hpow2]
              simp only [Complex.norm_natCast]
              gcongr
        _ = jZeroHasseEulerMajorant p s := by
              rw [hfirst, hsecond]
              rfl

/-- The actual original j=0 Euler denominator is multipliable in
Re(s)>3/2; no second Euler family is introduced. -/
theorem jZeroOriginalEulerDenominators_multipliable
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re) :
    Multipliable (fun p : RationalPrime =>
      ellipticComplexLocalDenominator p s) :=
  jZeroOriginalEulerDenominators_multipliable_of_bound hs
    (jZeroOriginalEulerPerturbation_norm_le_majorant hs)

/-- The j=0 *denominator* product now has an unconditional source-written
summability proof candidate. Do not confuse this with analytic L-series
identification, continuation or a critical-line zero theorem. -/
theorem jZeroOriginalEulerPerturbation_summable
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re) :
    Summable (fun p : RationalPrime =>
      JZeroOriginalEulerPerturbation p s) :=
  jZeroOriginalEulerPerturbation_summable_of_bound hs
    (jZeroOriginalEulerPerturbation_norm_le_majorant hs)


/-- At all actual good primes, 2/p + 1/p² < 1, so the Hasse
perturbation majorant is less than one for Re(s)>3/2. -/
theorem jZeroHasseEulerMajorant_lt_one_of_good
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re)
    (p : RationalPrime) (hp3 : 3 < p.1) :
    jZeroHasseEulerMajorant p s < 1 := by
  have hp4 : (4 : ℝ) ≤ (p.1 : ℝ) := by
    exact_mod_cast hp3
  have hp1 : (1 : ℝ) < (p.1 : ℝ) := by
    exact_mod_cast p.2.one_lt
  have hfirst :
      (p.1 : ℝ)^((1 : ℝ)/2-s.re) < (p.1 : ℝ)^(-1) :=
    Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
  have hsecond :
      (p.1 : ℝ)^(1-2*s.re) < (p.1 : ℝ)^(-2) :=
    Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
  have hbinv : (p.1 : ℝ)^(-1) ≤ (4 : ℝ)^(-1) := by
    rw [Real.rpow_neg_one, Real.rpow_neg_one]
    exact one_div_le_one_div_of_le (by norm_num) hp4
  have hbinv2 : (p.1 : ℝ)^(-2) ≤ (4 : ℝ)^(-2) := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg, Real.rpow_neg]
    gcongr
    exact Real.rpow_le_rpow (by positivity) hp4 (by norm_num)
  unfold jZeroHasseEulerMajorant
  calc
    2 * (p.1 : ℝ)^((1 : ℝ)/2-s.re)
        + (p.1 : ℝ)^(1-2*s.re)
        < 2 * (p.1 : ℝ)^(-1)
          + (p.1 : ℝ)^(-2) := by linarith
    _ ≤ 2 * (4 : ℝ)^(-1) + (4 : ℝ)^(-2) := by gcongr
    _ < 1 := by norm_num [Real.rpow_neg_one, Real.rpow_neg]

theorem jZeroOriginalEulerPerturbation_norm_lt_one
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re)
    (p : RationalPrime) :
    ‖JZeroOriginalEulerPerturbation p s‖ < 1 := by
  by_cases h2 : p.1 = 2
  · simp [JZeroOriginalEulerPerturbation,
      ellipticComplexLocalDenominator, h2]
  · by_cases h3 : p.1 = 3
    · simp [JZeroOriginalEulerPerturbation,
        ellipticComplexLocalDenominator, h2, h3]
    · have hp3 : 3 < p.1 := by
        have := p.2.two_le
        omega
      exact (jZeroOriginalEulerPerturbation_norm_le_majorant hs p).trans_lt
        (jZeroHasseEulerMajorant_lt_one_of_good hs p hp3)

/-- Nonzero original local denominators on the selected half-plane. -/
theorem jZeroOriginalEulerDenominator_ne_zero
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re)
    (p : RationalPrime) :
    ellipticComplexLocalDenominator p s ≠ 0 := by
  intro hz
  have hpert : JZeroOriginalEulerPerturbation p s = -1 := by
    simp [JZeroOriginalEulerPerturbation, hz]
  have hsmall := jZeroOriginalEulerPerturbation_norm_lt_one hs p
  rw [hpert] at hsmall
  norm_num at hsmall

/-- Absolute convergence plus nonvanishing of every factor gives a
nonzero infinite product of the SAME elliptic denominators. -/
theorem jZeroOriginalEulerDenominatorProduct_ne_zero
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re) :
    (∏' p : RationalPrime, ellipticComplexLocalDenominator p s) ≠ 0 := by
  have hproduct :
      (∏' p : RationalPrime, (1 + JZeroOriginalEulerPerturbation p s)) ≠ 0 := by
    apply tprod_one_add_ne_zero_of_summable
    · intro p
      simpa [JZeroOriginalEulerPerturbation] using
        jZeroOriginalEulerDenominator_ne_zero hs p
    · exact (jZeroOriginalEulerPerturbation_summable hs).norm
  have hfun :
      (fun p : RationalPrime => 1 + JZeroOriginalEulerPerturbation p s)
      = (fun p : RationalPrime => ellipticComplexLocalDenominator p s) := by
    funext p
    simp [JZeroOriginalEulerPerturbation]
  simpa only [hfun] using hproduct

end Integration.EisensteinJZeroHasseEulerConvergenceWeldExact
