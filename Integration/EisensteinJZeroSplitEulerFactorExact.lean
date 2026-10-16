import Integration.EisensteinJZeroIntegralJacobiExact

/-!
# Split-prime local Euler factor over the literal Eisenstein carrier

The integral Jacobi owner constructs `J_p ∈ Z[ω]` with

  N(J_p)  = p,
  Tr(J_p) = -a_p.

Therefore `π_p := -J_p` has norm `p` and trace `a_p`, and the same curve's
split-prime Euler polynomial factors algebraically as

  1 - a_p T + p T² = (1 - π_p T)(1 - conjugate(π_p) T).

This pays the local split-prime factorization.  It does not yet identify the
chosen factor with a conductor-normalized global Hecke/Groessencharacter, nor
claim multiplicative compatibility across prime ideals or a global elliptic
L-series identity.
-/

namespace Integration.EisensteinJZeroSplitEulerFactorExact

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroFiniteFieldTraceExact
open Integration.EisensteinJZeroIntegralJacobiExact

/-- The Jacobi-normalized Eisenstein factor carrying the actual Frobenius
trace. -/
noncomputable def jacobiFrobeniusPrime
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) : EisensteinQA :=
  -eisensteinMixedJacobi p hmod

/-- Its Eisenstein norm is the same rational prime. -/
theorem jacobiFrobeniusPrime_norm
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    QuadraticAlgebra.norm (jacobiFrobeniusPrime p hmod) = p := by
  rw [jacobiFrobeniusPrime, map_neg, QuadraticAlgebra.norm_neg,
    eisensteinMixedJacobi_norm p hmod]

/-- Its algebraic trace is exactly the same curve's Frobenius trace. -/
theorem jacobiFrobeniusPrime_trace
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    QuadraticAlgebra.trace (jacobiFrobeniusPrime p hmod) =
      jZeroFrobeniusTraceInt (ZMod p) := by
  rw [jacobiFrobeniusPrime, map_neg,
    eisensteinMixedJacobi_trace p hmod]
  simp

/-- The split-prime local Euler polynomial factors over `Z[ω]` into the
Jacobi/Frobenius factor and its conjugate. -/
theorem splitPrimeEulerFactor_factorization
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) (T : EisensteinQA) :
    (1 - jacobiFrobeniusPrime p hmod * T) *
        (1 - star (jacobiFrobeniusPrime p hmod) * T) =
      1 - algebraMap Int EisensteinQA
          (jZeroFrobeniusTraceInt (ZMod p)) * T +
        algebraMap Int EisensteinQA p * T ^ 2 := by
  let π := jacobiFrobeniusPrime p hmod
  have htr : algebraMap Int EisensteinQA (QuadraticAlgebra.trace π) = π + star π :=
    QuadraticAlgebra.algebraMap_trace_eq_add_star π
  have hnorm : algebraMap Int EisensteinQA (QuadraticAlgebra.norm π) = π * star π :=
    QuadraticAlgebra.algebraMap_norm_eq_mul_star π
  rw [jacobiFrobeniusPrime_trace p hmod] at htr
  rw [jacobiFrobeniusPrime_norm p hmod] at hnorm
  change (1 - π * T) * (1 - star π * T) = _
  rw [← htr, ← hnorm]
  ring

/-- Coefficient package for the split local factor. -/
structure SplitPrimeEulerData where
  prime : Nat
  trace : Int
  factor : EisensteinQA
  norm_eq_prime : QuadraticAlgebra.norm factor = prime
  trace_eq_frobenius : QuadraticAlgebra.trace factor = trace

/-- Canonical same-object split-prime Euler data. -/
noncomputable def splitPrimeEulerData
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) : SplitPrimeEulerData where
  prime := p
  trace := jZeroFrobeniusTraceInt (ZMod p)
  factor := jacobiFrobeniusPrime p hmod
  norm_eq_prime := jacobiFrobeniusPrime_norm p hmod
  trace_eq_frobenius := jacobiFrobeniusPrime_trace p hmod

structure SplitEulerFactorBoundary where
  integralFrobeniusFactorPaid : Bool := true
  factorNormPaid : Bool := true
  factorTracePaid : Bool := true
  splitLocalEulerFactorizationPaid : Bool := true
  conductorPrimaryNormalizationPaid : Bool := false
  globalPrimeIdealMultiplicativityPaid : Bool := false
  heckeCharacterPaid : Bool := false
  ellipticHeckeLSeriesPaid : Bool := false

/-- The split-prime local Euler factor is paid.  The remaining global task is
compatibility of these local factors with a conductor-normalized Hecke
character, not their local trace/norm. -/
def canonicalBoundary : SplitEulerFactorBoundary := {}

end Integration.EisensteinJZeroSplitEulerFactorExact
