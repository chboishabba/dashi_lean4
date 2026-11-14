import Integration.EisensteinJZeroFiniteEulerProductExact
import Integration.EisensteinJZeroIntegralJacobiExact
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Conditional analytic Euler-product agreement

The branch now owns exact local elliptic/Hecke equality at every rational prime
and equality of every finite Euler truncation.  This owner moves that equality
into the complex analytic variable while keeping convergence explicit.

For a rational prime p and complex s set T=p^{-s}.  The elliptic denominator is

  1                         at p=2,3,
  1-a_p*T+p*T^2            otherwise.

The Hecke denominator is assembled from the actual conductor-normalized ideal
character values:

  (1-psi(P)T)(1-psi(Pbar)T)   at split p,
  1-psi((p))*T^2              at inert p,
  1                           at p=2,3.

The already-proved norm/trace and prime-value theorems identify these terms.
Consequently the reciprocal Euler terms are pointwise equal.  We then prove
that IF the elliptic family is `Multipliable` at s, the Hecke family is the
same multipliable family and the two genuine `tprod`s agree.

No convergence half-plane, analytic continuation, functional equation, or
completed L-function is manufactured here.  Those are now the only analytic
payments separating this Euler-product identity from a full L-series theorem.
-/

namespace Integration.EisensteinJZeroConditionalAnalyticEulerExact

open scoped BigOperators ComplexConjugate
open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroFiniteEulerProductExact
open Integration.EisensteinJZeroFiniteFieldTraceExact
open Integration.EisensteinJZeroIntegralJacobiExact
open Integration.EisensteinJZeroSplitEulerFactorExact
open Integration.EisensteinJZeroHeckeLocalAgreementExact

private abbrev E := EisensteinQA

/-- Standard Euler parameter `p^{-s}`. -/
noncomputable def primeEulerParameter (p : RationalPrime) (s : ℂ) : ℂ :=
  (p.1 : ℂ) ^ (-s)

private def goodPrime_gt_three (p : RationalPrime)
    (h2 : p.1 ≠ 2) (h3 : p.1 ≠ 3) : 3 < p.1 := by
  have hp2 := p.2.two_le
  omega

private theorem goodPrime_mod_three_cases
    (p : RationalPrime) (hp3 : 3 < p.1) :
    p.1 % 3 = 1 ∨ p.1 % 3 = 2 := by
  have hnot0 : p.1 % 3 ≠ 0 := by
    intro h0
    have h3dvd : 3 ∣ p.1 := Nat.dvd_of_mod_eq_zero h0
    rcases (Nat.dvd_prime p.2).1 h3dvd with h31 | h3p
    · norm_num at h31
    · omega
  have hlt := Nat.mod_lt p.1 (by norm_num : 0 < 3)
  omega

/-- Same elliptic local denominator evaluated at `p^{-s}`. -/
noncomputable def ellipticComplexLocalDenominator
    (p : RationalPrime) (s : ℂ) : ℂ := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  if h2 : p.1 = 2 then
    exact 1
  else if h3 : p.1 = 3 then
    exact 1
  else
    let T := primeEulerParameter p s
    exact 1 - (jZeroFrobeniusTraceInt (ZMod p.1) : ℂ) * T +
      (p.1 : ℂ) * T ^ 2

/-- Hecke-side denominator evaluated at the same rational-prime parameter. -/
noncomputable def heckeComplexLocalDenominator
    (p : RationalPrime) (s : ℂ) : ℂ := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  if h2 : p.1 = 2 then
    exact 1
  else if h3 : p.1 = 3 then
    exact 1
  else
    let hp3 := goodPrime_gt_three p h2 h3
    let T := primeEulerParameter p s
    rcases goodPrime_mod_three_cases p hp3 with hsplit | hinert
    · let π := jacobiFrobeniusPrime p.1 hsplit
      exact (1 - eisensteinToComplex π * T) *
        (1 - eisensteinToComplex (star π) * T)
    · exact 1 - eisensteinToComplex (inertHeckeFactor p.1) * T ^ 2

private theorem split_complex_denominator
    (p : RationalPrime) (hp3 : 3 < p.1)
    (hmod : p.1 % 3 = 1) (s : ℂ) :
    letI : Fact p.1.Prime := ⟨p.2⟩
    let T := primeEulerParameter p s
    (1 - eisensteinToComplex (jacobiFrobeniusPrime p.1 hmod) * T) *
        (1 - eisensteinToComplex (star (jacobiFrobeniusPrime p.1 hmod)) * T) =
      1 - (jZeroFrobeniusTraceInt (ZMod p.1) : ℂ) * T +
        (p.1 : ℂ) * T ^ 2 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  let π := jacobiFrobeniusPrime p.1 hmod
  let T := primeEulerParameter p s
  have htr : algebraMap Int E (QuadraticAlgebra.trace π) = π + star π :=
    QuadraticAlgebra.algebraMap_trace_eq_add_star π
  have hnorm : algebraMap Int E (QuadraticAlgebra.norm π) = π * star π :=
    QuadraticAlgebra.algebraMap_norm_eq_mul_star π
  rw [jacobiFrobeniusPrime_trace p.1 hmod] at htr
  rw [jacobiFrobeniusPrime_norm p.1 hmod] at hnorm
  have htrC := congrArg eisensteinToComplex htr
  have hnormC := congrArg eisensteinToComplex hnorm
  simp only [map_add, map_mul, eisensteinToComplex_star] at htrC hnormC
  change (1 - eisensteinToComplex π * T) *
      (1 - eisensteinToComplex (star π) * T) = _
  have hcastTr :
      eisensteinToComplex (algebraMap Int E (jZeroFrobeniusTraceInt (ZMod p.1))) =
        (jZeroFrobeniusTraceInt (ZMod p.1) : ℂ) := by
    simp [eisensteinToComplex]
  have hcastP : eisensteinToComplex (algebraMap Int E (p.1 : Int)) = (p.1 : ℂ) := by
    simp [eisensteinToComplex]
  rw [hcastTr] at htrC
  rw [hcastP] at hnormC
  linear_combination T * htrC + T ^ 2 * hnormC

private theorem inert_complex_denominator
    (p : RationalPrime) (hp3 : 3 < p.1)
    (hmod : p.1 % 3 = 2) (s : ℂ) :
    letI : Fact p.1.Prime := ⟨p.2⟩
    let T := primeEulerParameter p s
    1 - eisensteinToComplex (inertHeckeFactor p.1) * T ^ 2 =
      1 - (jZeroFrobeniusTraceInt (ZMod p.1) : ℂ) * T +
        (p.1 : ℂ) * T ^ 2 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  let T := primeEulerParameter p s
  have htrace := Integration.EisensteinJZeroInertPrimeLocalFactorExact.jZeroInertPrime_trace_zero
    p.1 (by omega) hmod
  rw [htrace]
  simp [inertHeckeFactor, eisensteinToComplex]
  ring

/-- Exact complex local denominator agreement at every rational prime. -/
theorem elliptic_hecke_complexLocal_agreement
    (p : RationalPrime) (s : ℂ) :
    ellipticComplexLocalDenominator p s = heckeComplexLocalDenominator p s := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  unfold ellipticComplexLocalDenominator heckeComplexLocalDenominator
  by_cases h2 : p.1 = 2
  · simp [h2]
  · by_cases h3 : p.1 = 3
    · simp [h2, h3]
    · simp only [h2, h3, ↓reduceIte]
      let hp3 := goodPrime_gt_three p h2 h3
      rcases goodPrime_mod_three_cases p hp3 with hsplit | hinert
      · simpa [hp3] using (split_complex_denominator p hp3 hsplit s).symm
      · simpa [hp3] using (inert_complex_denominator p hp3 hinert s).symm

/-- Reciprocal Euler term. -/
noncomputable def ellipticEulerTerm (p : RationalPrime) (s : ℂ) : ℂ :=
  (ellipticComplexLocalDenominator p s)⁻¹

/-- Same reciprocal term assembled from the Hecke ideal character. -/
noncomputable def heckeEulerTerm (p : RationalPrime) (s : ℂ) : ℂ :=
  (heckeComplexLocalDenominator p s)⁻¹

/-- Primewise reciprocal factors are identical. -/
theorem elliptic_hecke_EulerTerm_agreement
    (p : RationalPrime) (s : ℂ) :
    ellipticEulerTerm p s = heckeEulerTerm p s := by
  rw [ellipticEulerTerm, heckeEulerTerm,
    elliptic_hecke_complexLocal_agreement p s]

/-- Multipliability is therefore exactly the same condition on either side. -/
theorem ellipticEuler_multipliable_iff_hecke
    (s : ℂ) :
    Multipliable (fun p : RationalPrime => ellipticEulerTerm p s) ↔
      Multipliable (fun p : RationalPrime => heckeEulerTerm p s) := by
  simp_rw [elliptic_hecke_EulerTerm_agreement]

/-- Genuine infinite-product equality, conditional on convergence/multipliability.
The hypothesis is deliberately retained as the analytic frontier. -/
theorem conditionalAnalyticEulerProduct_agreement
    (s : ℂ)
    (h : Multipliable (fun p : RationalPrime => ellipticEulerTerm p s)) :
    (∏' p : RationalPrime, ellipticEulerTerm p s) =
      ∏' p : RationalPrime, heckeEulerTerm p s := by
  apply tprod_congr
  intro p
  exact elliptic_hecke_EulerTerm_agreement p s

structure ConditionalAnalyticEulerBoundary where
  complexPrimewiseAgreementPaid : Bool := true
  reciprocalEulerTermAgreementPaid : Bool := true
  multipliabilityEquivalencePaid : Bool := true
  infiniteProductEqualityGivenConvergencePaid : Bool := true
  explicitConvergenceHalfPlanePaid : Bool := false
  heckeLSeriesDefinitionPaid : Bool := false
  ellipticLSeriesDefinitionPaid : Bool := false
  analyticContinuationPaid : Bool := false
  globalLFunctionIdentityPaid : Bool := false

/-- Only convergence/L-series semantics remain; algebraic and conditional Euler
product equality are paid. -/
def canonicalBoundary : ConditionalAnalyticEulerBoundary := {}

end Integration.EisensteinJZeroConditionalAnalyticEulerExact
