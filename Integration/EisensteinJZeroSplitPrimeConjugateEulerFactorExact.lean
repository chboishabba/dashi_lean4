import Integration.EisensteinJZeroAllGoodPrimeLocalExact
import Mathlib.Algebra.Polynomial.Basic

/-!
# Same-source j=0 split Euler factorisation into a conjugate Eisenstein pair

The original source `splitJacobiEisensteinElement` is the actual norm-p
element of `EisensteinQA`, not a second invented character or complex root.
This file performs only the LOCAL polynomial conjugate-factor step. A
global Hecke character requires choice compatibility at all primes,
conductor/infinity type, bad-prime data and genuine analytic L-series.

The source sign convention for y²=x³+1 is
  a_p = -(2*z.re-z.im).
Therefore the two local factors are (1+z*T)(1+star z*T);
using the opposite sign would give the wrong curve Euler factor.

Source written; Lean kernel/axiom check pending. No CI.
-/

namespace Integration.EisensteinJZeroSplitPrimeConjugateEulerFactorExact

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroAllGoodPrimeLocalExact
open Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact
open Polynomial

/-- Original source-selected split Eisenstein Jacobi element. -/
noncomputable def originalSplitElement
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) (hmod : p % 3 = 1) :
    EisensteinQA :=
  splitJacobiEisensteinElement p (by omega) hmod

/-- The two candidate LOCAL CM Euler factors, without claiming
they are evaluations of a globally constructed Hecke character. -/
noncomputable def localConjugateFactors
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) (hmod : p % 3 = 1) :
    Polynomial EisensteinQA × Polynomial EisensteinQA :=
  (1 + C (originalSplitElement p hp3 hmod) * X,
   1 + C (star (originalSplitElement p hp3 hmod)) * X)

/-- The coefficient-level algebraic identity belongs to the original
Eisenstein quadratic algebra. It is valid for every z, not just
a selected prime or an assumed Hecke eigencharacter. -/
theorem conjugate_local_factor_expansion (z : EisensteinQA) :
    (1 + C z * X) * (1 + C (star z) * X) =
      1 + C (z + star z) * X + C (z * star z) * X ^ 2 := by
  ring

/-- Source Jacobi norm determines the coefficient of T² at every
original split good prime. -/
theorem source_split_norm_is_prime
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) (hmod : p % 3 = 1) :
    QuadraticAlgebra.norm (originalSplitElement p hp3 hmod) = p :=
  splitJacobiEisensteinElement_norm p (by omega) hmod

/-- Source trace determines the INTEGER coefficient of T:
the polynomial's linear coefficient is -a_p. -/
theorem source_split_trace_is_negative_of_coefficient
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) (hmod : p % 3 = 1) :
    jZeroFrobeniusTraceInt (ZMod p) =
      -(2 * (originalSplitElement p hp3 hmod).re -
          (originalSplitElement p hp3 hmod).im) :=
  splitPrime_jZero_trace_formula p (by omega) hmod

/-- This expansion is the concrete local Hecke-shape candidate.
No global compatibility/Artin/Dirichlet character equality is asserted. -/
theorem source_split_pair_expansion
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) (hmod : p % 3 = 1) :
    (localConjugateFactors p hp3 hmod).1 *
      (localConjugateFactors p hp3 hmod).2 =
      1 + C (originalSplitElement p hp3 hmod +
             star (originalSplitElement p hp3 hmod)) * X +
        C (originalSplitElement p hp3 hmod *
           star (originalSplitElement p hp3 hmod)) * X ^ 2 := by
  simpa [localConjugateFactors] using
    conjugate_local_factor_expansion (originalSplitElement p hp3 hmod)

#print axioms conjugate_local_factor_expansion
#print axioms source_split_norm_is_prime
#print axioms source_split_trace_is_negative_of_coefficient
#print axioms source_split_pair_expansion

/-- General all-good-prime negative control: the elliptic Euler polynomial
has T² coefficient p, while the quadratic Dirichlet/Dedekind inverse
Euler polynomial has T² coefficient χ_(-3)(p) ∈ {+1,-1}.
Their L-functions cannot be identified coefficientwise at any p>3,
regardless of the successful Jacobi local trace correspondence.
This does not assume or construct a global Hecke character. -/
theorem elliptic_vs_quadratic_dirichlet_t2_coefficient_ne
    (p : Nat) (hp3 : 3 < p) (chi : Int)
    (hchi : chi = 1 ∨ chi = -1) :
    (p : Int) ≠ chi := by
  rcases hchi with h | h <;> omega

/-- At a split good prime χ_(-3)(p)=+1; these quadratic
Dirichlet and elliptic local second coefficients differ. -/
theorem split_quadratic_dedekind_not_elliptic
    (p : Nat) (hp3 : 3 < p) :
    (p : Int) ≠ 1 :=
  elliptic_vs_quadratic_dirichlet_t2_coefficient_ne p hp3 1 (Or.inl rfl)

/-- At an inert good prime χ_(-3)(p)=-1; likewise. -/
theorem inert_quadratic_dedekind_not_elliptic
    (p : Nat) (hp3 : 3 < p) :
    (p : Int) ≠ -1 :=
  elliptic_vs_quadratic_dirichlet_t2_coefficient_ne p hp3 (-1) (Or.inr rfl)

#print axioms elliptic_vs_quadratic_dirichlet_t2_coefficient_ne
#print axioms split_quadratic_dedekind_not_elliptic
#print axioms inert_quadratic_dedekind_not_elliptic

end Integration.EisensteinJZeroSplitPrimeConjugateEulerFactorExact
