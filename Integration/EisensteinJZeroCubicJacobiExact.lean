import Integration.EisensteinJZeroFiniteFieldTraceExact
import Mathlib.NumberTheory.JacobiSum.Basic

/-!
# Cubic-character / Jacobi-sum compiler for the split j=0 branch

This owner narrows the split-prime frontier without pretending that Mathlib
already supplies a canonical cubic character or a Hecke character.

A `CubicCharacterCertificate F` contains exactly the finite-field producer
needed downstream: a multiplicative character `psi : F -> C` and a certified
reindexing of sums through the cube map with fibre weight

    1 + psi(t) + psi(t)^2.

Given that producer, the concrete j=0 trace

    a_q = - sum_x chi_2(x^3+1)

compiles to a pair of genuine Mathlib Jacobi sums:

    a_q = -[ psi(-1) J(psi,chi_2)
             + psi^2(-1) J(psi^2,chi_2) ].

This is finite-field character theory only.  Selecting/evaluating the cubic
character in terms of an Eisenstein prime, constructing a Hecke character, and
globalising to the elliptic L-function remain separate payments.
-/

namespace Integration.EisensteinJZeroCubicJacobiExact

open scoped BigOperators
open Finset
open Integration.EisensteinJZeroFiniteFieldTraceExact

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Quadratic character embedded into the complex numbers. -/
noncomputable def quadraticCharComplex : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

@[simp] theorem quadraticCharComplex_apply (x : F) :
    quadraticCharComplex x = (quadraticChar F x : ℂ) := rfl

/-- Exact finite-field producer required for the split/cubic branch.

The `cubeWeightedReindex` field is the proof-relevant statement that the
selected character really records the cube fibres; merely having an order-3
phase-valued function is not enough. -/
structure CubicCharacterCertificate (F : Type*) [Field F] [Fintype F] [DecidableEq F] where
  character : MulChar F ℂ
  nontrivial : character ≠ 1
  squareNontrivial : character * character ≠ 1
  cubeWeightedReindex :
    ∀ f : F → ℂ,
      (∑ x : F, f (x ^ 3)) =
        ∑ t : F, (1 + character t + (character * character) t) * f t

namespace CubicCharacterCertificate

variable (cert : CubicCharacterCertificate F)

abbrev ψ : MulChar F ℂ := cert.character
abbrev ψ2 : MulChar F ℂ := cert.character * cert.character

end CubicCharacterCertificate

private lemma translation_add_one_bijective :
    Function.Bijective (fun x : F => x + 1) := by
  constructor
  · intro x y h
    exact add_right_cancel h
  · intro y
    refine ⟨y - 1, ?_⟩
    ring

private theorem quadraticCharComplex_sum_zero
    (hchar : ringChar F ≠ 2) :
    ∑ x : F, quadraticCharComplex x = 0 := by
  have h := quadraticChar_sum_zero (F := F) hchar
  have hc := congrArg (fun z : Int => (z : ℂ)) h
  simpa [quadraticCharComplex, map_sum] using hc

private theorem quadraticCharComplex_shift_sum_zero
    (hchar : ringChar F ≠ 2) :
    ∑ t : F, quadraticCharComplex (t + 1) = 0 := by
  calc
    (∑ t : F, quadraticCharComplex (t + 1))
        = ∑ u : F, quadraticCharComplex u := by
          simpa using (translation_add_one_bijective (F := F)).sum_comp quadraticCharComplex
    _ = 0 := quadraticCharComplex_sum_zero (F := F) hchar

private theorem jacobi_shift_identity (ψ : MulChar F ℂ) :
    (∑ t : F, ψ t * quadraticCharComplex (t + 1)) =
      ψ (-1) * jacobiSum ψ quadraticCharComplex := by
  rw [jacobiSum]
  have hneg := (Equiv.neg F).sum_comp
    (fun u : F => ψ u * quadraticCharComplex (1 - u))
  calc
    (∑ t : F, ψ t * quadraticCharComplex (t + 1))
        = ∑ u : F, ψ (-u) * quadraticCharComplex (1 - u) := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg.symm
    _ = ∑ u : F, (ψ (-1) * ψ u) * quadraticCharComplex (1 - u) := by
          apply Finset.sum_congr rfl
          intro u hu
          congr 2
          rw [show -u = (-1 : F) * u by ring, map_mul]
    _ = ψ (-1) * ∑ u : F, ψ u * quadraticCharComplex (1 - u) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u hu
          ring

/-- Complex cast of the general finite-field trace formula. -/
theorem jZeroTrace_cast_eq_neg_quadraticCharComplexSum
    (hchar : ringChar F ≠ 2) :
    ((jZeroFrobeniusTraceInt F : Int) : ℂ) =
      - ∑ x : F, quadraticCharComplex (x ^ 3 + 1) := by
  rw [jZeroFrobeniusTrace_eq_neg_quadraticCharSum (F := F) hchar]
  simp only [Int.cast_neg, Int.cast_sum, quadraticCharComplex_apply]

/-- Jacobi-sum expression compiled from a certified cubic character. -/
noncomputable def cubicJacobiTrace (cert : CubicCharacterCertificate F) : ℂ :=
  - (cert.character (-1) * jacobiSum cert.character quadraticCharComplex
      + (cert.character * cert.character) (-1) *
          jacobiSum (cert.character * cert.character) quadraticCharComplex)

/-- The concrete j=0 Frobenius trace is exactly the two Jacobi terms once the
cube-fibre character certificate is supplied. -/
theorem jZeroTrace_cast_eq_cubicJacobiTrace
    (hchar : ringChar F ≠ 2)
    (cert : CubicCharacterCertificate F) :
    ((jZeroFrobeniusTraceInt F : Int) : ℂ) = cubicJacobiTrace cert := by
  rw [jZeroTrace_cast_eq_neg_quadraticCharComplexSum (F := F) hchar]
  have hreindex := cert.cubeWeightedReindex
    (fun t : F => quadraticCharComplex (t + 1))
  change
    -(∑ x : F, quadraticCharComplex (x ^ 3 + 1)) = cubicJacobiTrace cert
  rw [hreindex]
  unfold cubicJacobiTrace
  have hzero := quadraticCharComplex_shift_sum_zero (F := F) hchar
  have hψ := jacobi_shift_identity (F := F) cert.character
  have hψ2 := jacobi_shift_identity (F := F) (cert.character * cert.character)
  calc
    -(∑ t : F,
        (1 + cert.character t + (cert.character * cert.character) t) *
          quadraticCharComplex (t + 1))
      = -((∑ t : F, quadraticCharComplex (t + 1))
          + (∑ t : F, cert.character t * quadraticCharComplex (t + 1))
          + (∑ t : F, (cert.character * cert.character) t *
              quadraticCharComplex (t + 1))) := by
            congr 1
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro t ht
            ring
    _ = -(cert.character (-1) * jacobiSum cert.character quadraticCharComplex
          + (cert.character * cert.character) (-1) *
              jacobiSum (cert.character * cert.character) quadraticCharComplex) := by
            rw [hzero, zero_add, hψ, hψ2]

/-- Status helpers used by regression/terminal surfaces. -/
def finiteFieldCubicCharacterPaid (_cert : CubicCharacterCertificate F) : Bool := true

def heckeCharacterManufactured (_cert : CubicCharacterCertificate F) : Bool := false

def eisensteinPrimeJacobiEvaluationPaid (_cert : CubicCharacterCertificate F) : Bool := false

structure CubicJacobiBoundary (cert : CubicCharacterCertificate F) : Prop where
  finiteFieldCubicCharacterCertificatePaid : finiteFieldCubicCharacterPaid cert = true
  jZeroJacobiTraceCompilerPaid : True
  canonicalSplitPrimeCharacterConstructedHere : False
  jacobiSumEvaluatedAsEisensteinPrimeHere : False
  heckeCharacterManufacturedHere : heckeCharacterManufactured cert = false
  globalEllipticLFunctionPaidHere : False

end Integration.EisensteinJZeroCubicJacobiExact
