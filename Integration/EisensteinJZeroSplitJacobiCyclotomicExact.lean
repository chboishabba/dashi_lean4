import Integration.EisensteinJZeroCanonicalCubicCharacterExact
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Mathlib.Analysis.Complex.Basic

/-!
# Split j=0 Jacobi sum as a cyclotomic norm-p object

The canonical cubic-character certificate now lets the split-prime trace be
expressed by genuine Mathlib Jacobi sums.  This file pushes that same-prime
branch one stage farther without silently identifying isomorphic integral
carriers.

For a prime `p > 2`, `p ≡ 1 (mod 3)`, let `psi` be the canonical cubic
character from `EisensteinJZeroCanonicalCubicCharacterExact` and let `chi_2`
be the complex-valued quadratic character.  We source-write:

* `J(psi,chi_2)` belongs to the complex sixth-cyclotomic order `Z[zeta_6]`;
* complex conjugation sends it to `J(psi^-1,chi_2^-1)`;
* Mathlib's Jacobi product theorem therefore gives

      J(psi,chi_2) * conj(J(psi,chi_2)) = p,

  hence `Complex.normSq J = p`.

This is exactly the norm-p statement needed before selecting an Eisenstein
prime above `p`, but it is NOT yet an equality/associate theorem with the
repo's `EisensteinQA` witness.  The carrier equivalence
`Z[zeta_6] ≃ Z[omega] ≃ EisensteinQA` and the corresponding associate/unit
selection are left explicit for the next tranche.

Attribution: Mathlib owns the generic Jacobi-sum, multiplicative-character,
quadratic-character, root-of-unity, conjugation and complex-norm machinery.
DASHI/Lean owns this specialization and same-prime composition only.
-/

namespace Integration.EisensteinJZeroSplitJacobiCyclotomicExact

open scoped BigOperators ComplexConjugate
open Finset
open Integration.EisensteinJZeroCubicJacobiExact
open Integration.EisensteinJZeroCanonicalCubicCharacterExact

/-- The standard primitive sixth root of unity used for the integral target. -/
noncomputable def sixthRoot : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 6)

/-- The selected sixth root is primitive. -/
theorem sixthRoot_isPrimitive : IsPrimitiveRoot sixthRoot 6 := by
  simpa [sixthRoot] using Complex.isPrimitiveRoot_exp 6 (by norm_num)

/-- Canonical split-prime cubic certificate. -/
noncomputable def splitCertificate
    (p : Nat) [Fact p.Prime] (hp3 : p % 3 = 1) :
    CubicCharacterCertificate (ZMod p) :=
  splitPrimeCubicCharacterCertificate p hp3

/-- Cubic character attached to the selected split-prime certificate. -/
noncomputable def splitCubicCharacter
    (p : Nat) [Fact p.Prime] (hp3 : p % 3 = 1) :
    MulChar (ZMod p) ℂ :=
  (splitCertificate p hp3).character

/-- The Jacobi sum on the canonical cubic character and the quadratic
character. -/
noncomputable def splitJacobiSum
    (p : Nat) [Fact p.Prime] (hp3 : p % 3 = 1) : ℂ :=
  jacobiSum (splitCubicCharacter p hp3)
    (quadraticCharComplex : MulChar (ZMod p) ℂ)

------------------------------------------------------------------------
-- Character powers and nontriviality.
------------------------------------------------------------------------

private theorem splitCubicCharacter_pow_three
    (p : Nat) [Fact p.Prime] (hp3 : p % 3 = 1) :
    splitCubicCharacter p hp3 ^ 3 = 1 := by
  change canonicalCubicCharacter
      (F := ZMod p) (by simpa [ZMod.card] using hp3) ^ 3 = 1
  exact canonicalCubicCharacter_pow_three
    (F := ZMod p) (by simpa [ZMod.card] using hp3)

private theorem splitCubicCharacter_pow_six
    (p : Nat) [Fact p.Prime] (hp3 : p % 3 = 1) :
    splitCubicCharacter p hp3 ^ 6 = 1 := by
  rw [show 6 = 3 * 2 by norm_num, pow_mul,
    splitCubicCharacter_pow_three p hp3, one_pow]

private theorem quadraticCharComplex_pow_two
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) :
    (quadraticCharComplex : MulChar F ℂ) ^ 2 = 1 := by
  ext u
  have hu0 : (u : F) ≠ 0 := Units.ne_zero u
  have hs := quadraticChar_sq_one (F := F) hu0
  have hsc := congrArg (fun z : Int => (z : ℂ)) hs
  simpa [MulChar.pow_apply_coe, quadraticCharComplex_apply,
    MulChar.one_apply_coe] using hsc

private theorem quadraticCharComplex_pow_six
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) :
    (quadraticCharComplex : MulChar F ℂ) ^ 6 = 1 := by
  rw [show 6 = 2 * 3 by norm_num, pow_mul,
    quadraticCharComplex_pow_two (F := F) hchar, one_pow]

private theorem quadraticCharComplex_ne_one
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) :
    (quadraticCharComplex : MulChar F ℂ) ≠ 1 := by
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := F) hchar
  have ha0 : a ≠ 0 := by
    intro h0
    subst a
    simpa using ha
  intro htriv
  have hev := congrArg (fun χ : MulChar F ℂ => χ a) htriv
  have hunit : IsUnit a := isUnit_iff_ne_zero.mpr ha0
  simpa [quadraticCharComplex_apply, ha,
    MulChar.one_apply hunit] using hev

private theorem splitCubicCharacter_ne_one
    (p : Nat) [Fact p.Prime] (hp3 : p % 3 = 1) :
    splitCubicCharacter p hp3 ≠ 1 :=
  (splitCertificate p hp3).nontrivial

private theorem splitCubicCharacter_sq_ne_one
    (p : Nat) [Fact p.Prime] (hp3 : p % 3 = 1) :
    splitCubicCharacter p hp3 * splitCubicCharacter p hp3 ≠ 1 :=
  (splitCertificate p hp3).squareNontrivial

private theorem splitCubic_mul_quadratic_ne_one
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    splitCubicCharacter p hp3 *
      (quadraticCharComplex : MulChar (ZMod p) ℂ) ≠ 1 := by
  let ψ := splitCubicCharacter p hp3
  let χ := (quadraticCharComplex : MulChar (ZMod p) ℂ)
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hχ2 : χ ^ 2 = 1 := quadraticCharComplex_pow_two (F := ZMod p) hchar
  intro h
  have hsquare := congrArg (fun c : MulChar (ZMod p) ℂ => c ^ 2) h
  have hψ2 : ψ ^ 2 = 1 := by
    calc
      ψ ^ 2 = ψ ^ 2 * χ ^ 2 := by rw [hχ2, mul_one]
      _ = (ψ * χ) ^ 2 := by rw [mul_pow]
      _ = 1 := by rw [h]; simp
  exact splitCubicCharacter_sq_ne_one p hp3 <| by
    simpa [ψ, pow_two] using hψ2

------------------------------------------------------------------------
-- Cyclotomic-integrality receipt.
------------------------------------------------------------------------

/-- The canonical split Jacobi sum is an algebraic integer in the sixth
cyclotomic order.  Sixth roots are used because the two characters have orders
3 and 2 respectively. -/
theorem splitJacobiSum_mem_sixthCyclotomicOrder
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    splitJacobiSum p hp3 ∈ Algebra.adjoin ℤ ({sixthRoot : ℂ} : Set ℂ) := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hψ6 := splitCubicCharacter_pow_six p hp3
  have hχ6 := quadraticCharComplex_pow_six (F := ZMod p) hchar
  simpa [splitJacobiSum, sixthRoot] using
    (jacobiSum_mem_algebraAdjoin_of_pow_eq_one
      (F := ZMod p) (R := ℂ) hψ6 hχ6 sixthRoot_isPrimitive)

------------------------------------------------------------------------
-- Conjugation and norm-p theorem.
------------------------------------------------------------------------

/-- Complex conjugation acts on a Jacobi sum by inverting both characters. -/
theorem conj_jacobiSum_eq_inv
    {F : Type*} [Field F] [Fintype F]
    (χ φ : MulChar F ℂ) :
    Complex.conj (jacobiSum χ φ) = jacobiSum χ⁻¹ φ⁻¹ := by
  classical
  rw [jacobiSum]
  simp_rw [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← RCLike.star_def, MulChar.star_apply', MulChar.star_apply']

/-- The canonical split Jacobi sum times its conjugate is exactly the same
rational prime `p`. -/
theorem splitJacobiSum_mul_conj
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    splitJacobiSum p hp3 * Complex.conj (splitJacobiSum p hp3) = (p : ℂ) := by
  let ψ := splitCubicCharacter p hp3
  let χ := (quadraticCharComplex : MulChar (ZMod p) ℂ)
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hψ : ψ ≠ 1 := splitCubicCharacter_ne_one p hp3
  have hχ : χ ≠ 1 := quadraticCharComplex_ne_one (F := ZMod p) hchar
  have hψχ : ψ * χ ≠ 1 := splitCubic_mul_quadratic_ne_one p hp2 hp3
  have hring : ringChar ℂ ≠ ringChar (ZMod p) :=
    AddChar.ringChar_ne (ZMod p)
  have hprod := jacobiSum_mul_jacobiSum_inv
    (F := ZMod p) (F' := ℂ) hring hψ hχ hψχ
  change jacobiSum ψ χ * Complex.conj (jacobiSum ψ χ) = (p : ℂ)
  rw [conj_jacobiSum_eq_inv ψ χ]
  simpa [ZMod.card] using hprod

/-- Equivalently, the canonical split Jacobi sum has complex norm-square `p`. -/
theorem splitJacobiSum_normSq
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    Complex.normSq (splitJacobiSum p hp3) = p := by
  have h := splitJacobiSum_mul_conj p hp2 hp3
  rw [Complex.mul_conj] at h
  exact_mod_cast h

------------------------------------------------------------------------
-- Honest boundary.
------------------------------------------------------------------------

structure SplitJacobiCyclotomicBoundary where
  sixthCyclotomicIntegralityPaid : Bool := true
  conjugateIsInverseCharacterJacobiPaid : Bool := true
  samePrimeNormSquarePaid : Bool := true
  sixthCyclotomicOrderIdentifiedWithEisensteinQACarrier : Bool := false
  jacobiSumAssociatedToRepoSplitPrimeWitness : Bool := false
  canonicalUnitNormalizationPaid : Bool := false
  splitPrimeFrobeniusClosedFormPaid : Bool := false
  heckeCharacterPaid : Bool := false

/-- Downstream machine-readable boundary. -/
def canonicalBoundary : SplitJacobiCyclotomicBoundary := {}

end Integration.EisensteinJZeroSplitJacobiCyclotomicExact
