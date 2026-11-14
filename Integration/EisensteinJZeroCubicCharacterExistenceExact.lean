import Integration.EisensteinJZeroCubicJacobiExact
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Split-prime cubic character existence and orientation-independent Jacobi pair

Mathlib owns the generic theorem `MulChar.exists_mulChar_orderOf` and the
primitive complex roots of unity used below.  This file only specializes those
library results to split primes `p ≡ 1 (mod 3)` and simplifies the repository's
already-paid cubic/Jacobi compiler.

No cubic Jacobi-sum evaluation, Eisenstein-prime identification, Hecke
character, or global elliptic L-function identity is claimed here.
-/

namespace Integration.EisensteinJZeroCubicCharacterExistenceExact

open Integration.EisensteinJZeroCubicJacobiExact

/-- Every split prime admits a genuine complex-valued multiplicative character
of exact order three.  This is a direct specialization of Mathlib's generic
finite-field character-existence theorem. -/
theorem splitPrime_exists_orderThreeCharacter
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    ∃ ψ : MulChar (ZMod p) ℂ, orderOf ψ = 3 := by
  let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (3 : ℂ))
  have hζ : IsPrimitiveRoot ζ 3 := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp 3 (by norm_num)
  have hpdiv : 3 ∣ p - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hcard : 3 ∣ Fintype.card (ZMod p) - 1 := by
    simpa [ZMod.card] using hpdiv
  exact MulChar.exists_mulChar_orderOf (ZMod p) hcard hζ

/-- An order-three multiplicative character necessarily takes the value `1` at
`-1`.  The reason is intrinsic and does not depend on choosing an orientation:
`ψ(-1)` has order dividing both two and three. -/
theorem orderThreeCharacter_negOne
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : MulChar F ℂ) (hψ : orderOf ψ = 3) :
    ψ (-1) = 1 := by
  have hpow : ψ ^ 3 = 1 := by
    rw [← hψ]
    exact pow_orderOf_eq_one ψ
  have hcube : ψ (-1) ^ 3 = 1 := by
    have h := congrArg (fun χ : MulChar F ℂ => χ (-1)) hpow
    simpa using h
  have hsquare : ψ (-1) ^ 2 = 1 := by
    rw [← map_pow]
    norm_num
  have hcube_eq : ψ (-1) ^ 3 = ψ (-1) := by
    rw [pow_three, hsquare, one_mul]
  exact hcube_eq.symm.trans hcube

/-- Once the selected cubic character has exact order three, the `ψ(-1)` phase
factors in the generic compiler disappear.  The resulting pair is invariant
under swapping the two nontrivial cubic orientations. -/
theorem cubicJacobiTrace_eq_neg_unweightedPair
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (cert : CubicCharacterCertificate F)
    (horder : orderOf cert.character = 3) :
    cubicJacobiTrace cert =
      -(jacobiSum cert.character quadraticCharComplex
        + jacobiSum (cert.character * cert.character) quadraticCharComplex) := by
  have hneg := orderThreeCharacter_negOne cert.character horder
  unfold cubicJacobiTrace
  simp [hneg]

/-- Combined specialization of the existing Jacobi compiler after the
order-three phase factors have been removed. -/
theorem jZeroTrace_cast_eq_neg_unweightedJacobiPair
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2)
    (cert : CubicCharacterCertificate F)
    (horder : orderOf cert.character = 3) :
    ((Integration.EisensteinJZeroFiniteFieldTraceExact.jZeroFrobeniusTraceInt F : Int) : ℂ) =
      -(jacobiSum cert.character quadraticCharComplex
        + jacobiSum (cert.character * cert.character) quadraticCharComplex) := by
  rw [jZeroTrace_cast_eq_cubicJacobiTrace (F := F) hchar cert,
    cubicJacobiTrace_eq_neg_unweightedPair cert horder]

structure CubicCharacterExistenceBoundary : Prop where
  splitPrimeOrderThreeCharacterExists : True
  minusOnePhaseEliminated : True
  orientationIndependentJacobiPairExposed : True
  cubeFibreCertificateConstructedHere : False
  cubicJacobiEvaluationPaidHere : False
  heckeCharacterPaidHere : False

/-- Exact boundary after paying the generic split-prime character existence
and removing the spurious orientation dependence from the finite-field
compiler. -/
def canonicalBoundary : CubicCharacterExistenceBoundary :=
  ⟨trivial, trivial, trivial, id, id, id⟩

end Integration.EisensteinJZeroCubicCharacterExistenceExact
