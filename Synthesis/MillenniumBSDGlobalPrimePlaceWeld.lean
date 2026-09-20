import Synthesis.MillenniumBSDLocalEulerFactorSameObject
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Tactic

/-!
# Rational prime places and the actual global elliptic curve completion

Mathlib's global elliptic L-function is indexed by height-one primes of O_Q.
The padic height-one-spectrum file provides a canonical equivalence

  HeightOneSpectrum(O_Q) ≃ Nat.Primes

and canonical algebra isomorphisms from the corresponding adic completion and
its valuation ring to Q_p and Z_p.

This file pins an ordinary rational prime p to that exact global index and
proves that transporting the global curve y²=x³-x along the canonical
completion equivalence gives the literal p-adic curve used by the explicit
local-factor computation.

This pays the global indexing / same-curve layer.  What remains for the global
Euler-factor weld is invariance of `localPolynomial` (hence
`localEulerFactor`) under the paired completion/integer-ring isomorphisms.
-/

namespace Synthesis.Millennium.BSD

open NumberField
open IsDedekindDomain
open Rat.HeightOneSpectrum

noncomputable def rationalPrimePlace
    (p : ℕ) [Fact hp : p.Prime] :
    HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
    ⟨p, hp.out⟩

@[simp] theorem rationalPrimePlace_primesEquiv
    (p : ℕ) [Fact hp : p.Prime] :
    Rat.HeightOneSpectrum.primesEquiv
      (rationalPrimePlace p)
      =
    (⟨p, hp.out⟩ : Nat.Primes) := by
  simp [rationalPrimePlace]

noncomputable def rationalPrimeCompletionEquiv
    (p : ℕ) [Fact p.Prime] :
    (rationalPrimePlace p).adicCompletion ℚ ≃A[ℚ] ℚ_[p] := by
  simpa [rationalPrimePlace] using
    Rat.HeightOneSpectrum.adicCompletion.padicEquiv
      (rationalPrimePlace p)

noncomputable def rationalPrimeIntegerEquiv
    (p : ℕ) [Fact p.Prime] :
    (rationalPrimePlace p).adicCompletionIntegers ℚ
      ≃A[ℤ] ℤ_[p] := by
  simpa [rationalPrimePlace] using
    Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv
      (rationalPrimePlace p)

theorem rationalPrimeCompletionEquiv_on_integers
    (p : ℕ) [Fact p.Prime]
    (x : (rationalPrimePlace p).adicCompletionIntegers ℚ) :
    rationalPrimeCompletionEquiv p x =
      rationalPrimeIntegerEquiv p x := by
  rfl

theorem globalCurve_completion_transport
    (p : ℕ) [Fact p.Prime] :
    (cmWeierstrass.baseChange
      ((rationalPrimePlace p).adicCompletion ℚ)).map
        (rationalPrimeCompletionEquiv p).toRingEquiv.toRingHom
      =
    cmPadicWeierstrass p := by
  ext <;>
    simp [cmPadicWeierstrass, cmWeierstrass,
      rationalPrimeCompletionEquiv]

theorem globalCurve_completion_isElliptic
    (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve.IsElliptic
      (cmWeierstrass.baseChange
        ((rationalPrimePlace p).adicCompletion ℚ)) := by
  infer_instance


noncomputable def rationalPrimeResidueFieldEquiv
    (p : ℕ) [Fact p.Prime] :
    IsLocalRing.ResidueField
        ((rationalPrimePlace p).adicCompletionIntegers ℚ)
      ≃+*
    IsLocalRing.ResidueField ℤ_[p] :=
  IsLocalRing.ResidueField.mapEquiv
    (rationalPrimeIntegerEquiv p).toRingEquiv

noncomputable def rationalPrimeResidueFieldEquivZMod
    (p : ℕ) [Fact p.Prime] :
    IsLocalRing.ResidueField
        ((rationalPrimePlace p).adicCompletionIntegers ℚ)
      ≃+*
    ZMod p :=
  (rationalPrimeResidueFieldEquiv p).trans
    (padicResidueEquivZMod p)

theorem rationalPrimeResidueField_natCard
    (p : ℕ) [Fact p.Prime] :
    Nat.card
      (IsLocalRing.ResidueField
        ((rationalPrimePlace p).adicCompletionIntegers ℚ))
      =
    p := by
  rw [Nat.card_congr
    (rationalPrimeResidueFieldEquivZMod p).toEquiv]
  simp

end Synthesis.Millennium.BSD
