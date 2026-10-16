import Integration.EisensteinJZeroCubicCharacterCertificateExact
import Mathlib.NumberTheory.JacobiSum.Basic

/-!
# Split-prime mixed Jacobi norm and real-trace bridge

This owner advances the already-paid cubic/Jacobi compiler without importing a
CM/Hecke theorem.  For the canonical split-prime cubic character `ψ` and the
quadratic character `η`, it proves:

* `J(ψ²,η)` is the complex conjugate of `J(ψ,η)`;
* `J(ψ,η) * conj(J(ψ,η)) = p`;
* the j=0 Frobenius coefficient is `-2 Re J(ψ,η)`.

Mathlib owns the generic character-conjugation and Jacobi norm theorem.
DASHI/Lean owns this specialization and same-prime composition.  No claim is
made here that the Jacobi sum has already been lifted to a particular
Eisenstein integer, that its primary congruence is paid, or that a Hecke
character/global elliptic L-series identity has been constructed.
-/

namespace Integration.EisensteinJZeroMixedJacobiNormExact

open scoped BigOperators ComplexConjugate
open Finset
open Integration.EisensteinJZeroFiniteFieldTraceExact
open Integration.EisensteinJZeroCubicJacobiExact
open Integration.EisensteinJZeroCanonicalCubicCharacterExact
open Integration.EisensteinJZeroCubicCharacterCertificateExact

/-- The first mixed cubic/quadratic Jacobi sum on the canonical split-prime
certificate. -/
noncomputable def splitPrimeMixedJacobi
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) : ℂ :=
  jacobiSum
    (splitPrimeCubicCharacterCertificate p hmod).character
    quadraticCharComplex

private theorem splitPrime_character_order
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    orderOf (splitPrimeCubicCharacterCertificate p hmod).character = 3 := by
  change orderOf
    (canonicalCubicCharacter (F := ZMod p) (by simpa [ZMod.card] using hmod)) = 3
  exact canonicalCubicCharacter_order
    (F := ZMod p) (by simpa [ZMod.card] using hmod)

private theorem splitPrime_character_sq_eq_inv
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    (splitPrimeCubicCharacterCertificate p hmod).character *
        (splitPrimeCubicCharacterCertificate p hmod).character =
      (splitPrimeCubicCharacterCertificate p hmod).character⁻¹ := by
  let ψ := (splitPrimeCubicCharacterCertificate p hmod).character
  have hp3 : ψ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one ψ
    simpa [splitPrime_character_order p hmod] using h
  apply mul_left_cancel (a := ψ)
  calc
    ψ * (ψ * ψ) = ψ ^ 3 := by ring
    _ = 1 := hp3
    _ = ψ * ψ⁻¹ := by simp

private theorem quadraticCharComplex_isQuadratic
    (p : Nat) [Fact p.Prime] :
    (quadraticCharComplex : MulChar (ZMod p) ℂ).IsQuadratic := by
  exact (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

private theorem quadraticCharComplex_inv
    (p : Nat) [Fact p.Prime] :
    (quadraticCharComplex : MulChar (ZMod p) ℂ)⁻¹ = quadraticCharComplex :=
  (quadraticCharComplex_isQuadratic p).inv

private theorem star_jacobiSum
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ φ : MulChar F ℂ) :
    star (jacobiSum χ φ) = jacobiSum χ⁻¹ φ⁻¹ := by
  classical
  rw [jacobiSum, jacobiSum]
  simp_rw [map_sum, map_mul, MulChar.star_apply', map_sub, map_one]

/-- The second mixed Jacobi term in the compiler is literally the complex
conjugate of the first. -/
theorem splitPrimeMixedJacobi_conj
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    star (splitPrimeMixedJacobi p hmod) =
      jacobiSum
        ((splitPrimeCubicCharacterCertificate p hmod).character *
          (splitPrimeCubicCharacterCertificate p hmod).character)
        quadraticCharComplex := by
  rw [splitPrimeMixedJacobi, star_jacobiSum,
    ← splitPrime_character_sq_eq_inv p hmod,
    quadraticCharComplex_inv p]

private theorem splitPrime_character_ne_one
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    (splitPrimeCubicCharacterCertificate p hmod).character ≠ 1 := by
  intro h
  have ho := splitPrime_character_order p hmod
  rw [h, orderOf_one] at ho
  norm_num at ho

private theorem splitPrime_quadratic_ne_one
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    (quadraticCharComplex : MulChar (ZMod p) ℂ) ≠ 1 := by
  have hp2 : p ≠ 2 := by
    intro hp
    subst p
    norm_num at hmod
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have h0 := quadraticChar_ne_one (F := ZMod p) hchar
  exact (MulChar.ringHomComp_ne_one_iff Int.cast_injective).2 h0

private theorem splitPrime_product_ne_one
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    (splitPrimeCubicCharacterCertificate p hmod).character *
        (quadraticCharComplex : MulChar (ZMod p) ℂ) ≠ 1 := by
  let ψ := (splitPrimeCubicCharacterCertificate p hmod).character
  let η := (quadraticCharComplex : MulChar (ZMod p) ℂ)
  intro hprod
  have hηinv : η⁻¹ = η := quadraticCharComplex_inv p
  have hψη : ψ = η := by
    calc
      ψ = ψ * η * η⁻¹ := by simp
      _ = 1 * η⁻¹ := by rw [hprod]
      _ = η⁻¹ := by simp
      _ = η := hηinv
  have hψsq : ψ ^ 2 = 1 := by
    rw [hψη]
    exact (quadraticCharComplex_isQuadratic p).sq_eq_one
  have hd := orderOf_dvd_of_pow_eq_one hψsq
  rw [splitPrime_character_order p hmod] at hd
  norm_num at hd

private theorem splitPrime_ringChar_ne
    (p : Nat) [Fact p.Prime] :
    ringChar ℂ ≠ ringChar (ZMod p) := by
  rw [ZMod.ringChar_zmod_n]
  simp [Fact.out.ne_zero]

/-- The mixed Jacobi sum has exact norm `p`.  This is a direct specialization
of Mathlib's generic Jacobi-sum inverse-product theorem. -/
theorem splitPrimeMixedJacobi_normSq
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    splitPrimeMixedJacobi p hmod * star (splitPrimeMixedJacobi p hmod) = (p : ℂ) := by
  let ψ := (splitPrimeCubicCharacterCertificate p hmod).character
  let η := (quadraticCharComplex : MulChar (ZMod p) ℂ)
  have hJ := jacobiSum_mul_jacobiSum_inv
    (F := ZMod p) (F' := ℂ)
    (splitPrime_ringChar_ne p)
    (splitPrime_character_ne_one p hmod)
    (splitPrime_quadratic_ne_one p hmod)
    (splitPrime_product_ne_one p hmod)
  change splitPrimeMixedJacobi p hmod * star (splitPrimeMixedJacobi p hmod) = (p : ℂ)
  rw [splitPrimeMixedJacobi_conj p hmod]
  simpa [ψ, η, splitPrime_character_sq_eq_inv p hmod,
    quadraticCharComplex_inv p, ZMod.card] using hJ

/-- The previously-paid unweighted Jacobi pair is twice the real part of one
mixed Jacobi sum.  Hence the same j=0 Frobenius coefficient is `-2 Re J`. -/
theorem splitPrimeFrobeniusTrace_eq_neg_two_re_mixedJacobi
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    ((jZeroFrobeniusTraceInt (ZMod p) : Int) : ℂ) =
      -(2 : ℂ) * (splitPrimeMixedJacobi p hmod).re := by
  have htrace := splitPrime_jZeroTrace_eq_unweightedJacobiPair p hmod
  rw [splitPrimeMixedJacobi_conj p hmod] at htrace
  rw [htrace]
  simp only [Complex.star_def, Complex.add_conj]
  push_cast
  ring

/-- Equivalent real-coordinate form. -/
theorem splitPrimeFrobeniusTraceInt_eq_neg_two_re
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    (jZeroFrobeniusTraceInt (ZMod p) : ℝ) =
      -2 * (splitPrimeMixedJacobi p hmod).re := by
  have h := splitPrimeFrobeniusTrace_eq_neg_two_re_mixedJacobi p hmod
  exact Complex.ofReal_injective <| by simpa using congrArg Complex.re h

structure MixedJacobiNormBoundary where
  conjugatePairIdentified : Bool := true
  mixedJacobiNormEqualsPrime : Bool := true
  frobeniusEqualsNegativeJacobiTrace : Bool := true
  jacobiEisensteinLatticeLiftPaid : Bool := false
  jacobiPrimaryCongruencePaid : Bool := false
  heckeCharacterPaid : Bool := false
  globalEllipticLSeriesPaid : Bool := false

/-- The remaining local split-prime problem is no longer a magnitude/norm
statement.  It is the integral Eisenstein-lattice lift and primary congruence
identifying this norm-p Jacobi sum with the selected arithmetic factor. -/
def canonicalBoundary : MixedJacobiNormBoundary := {}

end Integration.EisensteinJZeroMixedJacobiNormExact
