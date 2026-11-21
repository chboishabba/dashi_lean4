import Integration.EisensteinJZeroSplitPrimeConjugateEulerFactorExact
import Integration.EisensteinJZeroSplitPrimeUnitNormalizationExact

/-!
# Source-selected Eisenstein ray-congruence candidate: modulus 2√(-3)

Reuses original EisensteinQA, original six-unit norm-fibre orbit and
original exact split Jacobi element. No global Hecke character is made.

At good split primes the source Jacobi convention is a_p=-Tr(J_p);
for a Hecke-shape Euler factor written as (1-α_p T)(1-ᾱ_p T),
the *candidate* must be α_p=-J_p, not J_p.

Ray modulus f=2(1+2ω), norm(f)=12. The CM j=0 curve y²=x³+1
has expected conductor 36=3*12, but neither minimal conductor nor the
actual elliptic character is proved here.

A local hypothesis J_p≡-1 (mod f) suffices to normalize α_p≡1
(mod f). Ten numerical split-prime tests satisfy this, but the
ALL-primes congruence and ideal-theoretic multiplicativity are OPEN.
This is a conditional algebra lemma, no kernel/axiom check.
-/

namespace Integration.EisensteinJZeroRayModulusLocalCandidateExact

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroSplitPrimeConjugateEulerFactorExact
open Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact
open Polynomial

/-- The concrete Eisenstein ray modulus generator 2√(-3) = 2+4ω. -/
def proposedRayModulus : EisensteinQA :=
  asQuadraticAlgebra 2 4

/-- Norm 12 is exact integer arithmetic in the original algebra. -/
theorem proposedRayModulus_norm :
    QuadraticAlgebra.norm proposedRayModulus = 12 := by
  simp [proposedRayModulus, norm_asQuadraticAlgebra, eisensteinNorm]
  norm_num

/-- On the literal original Eisenstein carrier, being 1 mod (f). -/
def OneModProposedRay (z : EisensteinQA) : Prop :=
  ∃ w : EisensteinQA, z - 1 = proposedRayModulus * w

/-- The original Jacobi sign convention demands minus the source J. -/
noncomputable def candidatePrimeIdealValue
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) (hmod : p % 3 = 1) :
    EisensteinQA :=
  -(originalSplitElement p hp3 hmod)

/-- Algebraic sign normalization: if original J is -1 modulo f,
then -J is 1 modulo f.  This is the precise unpaid local premise,
not a theorem asserting it for every split prime. -/
theorem ray_one_of_jacobi_negative_one
    (z : EisensteinQA)
    (h : ∃ w : EisensteinQA, z + 1 = proposedRayModulus * w) :
    OneModProposedRay (-z) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨-w, ?_⟩
  rw [mul_neg, ← hw]
  ring

/-- Conditional original split prime ray normalization. -/
theorem original_split_ray_one_if_minus_one
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) (hmod : p % 3 = 1)
    (h : ∃ w : EisensteinQA,
       originalSplitElement p hp3 hmod + 1 =
         proposedRayModulus * w) :
    OneModProposedRay (candidatePrimeIdealValue p hp3 hmod) :=
  ray_one_of_jacobi_negative_one (originalSplitElement p hp3 hmod) h

/-- The normalized -J retains the original source norm p. -/
theorem candidate_prime_norm
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) (hmod : p % 3 = 1) :
    QuadraticAlgebra.norm (candidatePrimeIdealValue p hp3 hmod) = p := by
  simpa [candidatePrimeIdealValue] using
    source_split_norm_is_prime p hp3 hmod

/-- Local normalized Euler factors have the genuine elliptic sign.
No ideal-factor choice independence, conductors, or L-series implied. -/
theorem candidate_normalized_pair_is_original_pair (z : EisensteinQA) :
    (1 - C (-z) * X) * (1 - C (star (-z)) * X) =
    (1 + C z * X) * (1 + C (star z) * X) := by
  simp only [map_neg, neg_mul, sub_neg_eq_add]

#print axioms proposedRayModulus_norm
#print axioms ray_one_of_jacobi_negative_one
#print axioms original_split_ray_one_if_minus_one
#print axioms candidate_prime_norm
#print axioms candidate_normalized_pair_is_original_pair

end Integration.EisensteinJZeroRayModulusLocalCandidateExact
