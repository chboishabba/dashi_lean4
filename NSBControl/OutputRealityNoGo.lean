import NSBControl.OutputPairingCollapse

namespace NSBControl
namespace OutputRealityNoGo

section

variable {V : Type*}
variable (conjugate : V → V)
variable (pairing : V → V → ℝ)

theorem simultaneousReality_preservesPairing
    (pairConjugateBoth :
      ∀ u v, pairing (conjugate u) (conjugate v) = pairing u v)
    (mixed self : V)
    (mixedNeg : V)
    (selfNeg : V)
    (hMixed : mixedNeg = conjugate mixed)
    (hSelf : selfNeg = conjugate self) :
    pairing mixedNeg selfNeg = pairing mixed self := by
  rw [hMixed, hSelf]
  exact pairConjugateBoth mixed self

theorem realityOrbit_doesNotCreateAntisymmetry
    (pairConjugateBoth :
      ∀ u v, pairing (conjugate u) (conjugate v) = pairing u v)
    (mixed self mixedNeg selfNeg : V)
    (hMixed : mixedNeg = conjugate mixed)
    (hSelf : selfNeg = conjugate self) :
    pairing mixedNeg selfNeg + pairing mixed self =
      2 * pairing mixed self := by
  rw [simultaneousReality_preservesPairing
    conjugate pairing pairConjugateBoth
    mixed self mixedNeg selfNeg hMixed hSelf]
  ring

end

end OutputRealityNoGo
end NSBControl
