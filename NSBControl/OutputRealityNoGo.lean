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


theorem outputPairing_even
    (pairConjugateBoth :
      ∀ u v, pairing (conjugate u) (conjugate v) = pairing u v)
    (mixedFold selfFold : Mode → V)
    (mixedReality : ∀ k, mixedFold (-k) = conjugate (mixedFold k))
    (selfReality : ∀ k, selfFold (-k) = conjugate (selfFold k))
    (k : Mode) :
    pairing (mixedFold (-k)) (selfFold (-k)) =
      pairing (mixedFold k) (selfFold k) := by
  exact simultaneousReality_preservesPairing
    conjugate pairing pairConjugateBoth
    (mixedFold k) (selfFold k)
    (mixedFold (-k)) (selfFold (-k))
    (mixedReality k) (selfReality k)

theorem outputRealityPair_doubles
    (pairConjugateBoth :
      ∀ u v, pairing (conjugate u) (conjugate v) = pairing u v)
    (mixedFold selfFold : Mode → V)
    (mixedReality : ∀ k, mixedFold (-k) = conjugate (mixedFold k))
    (selfReality : ∀ k, selfFold (-k) = conjugate (selfFold k))
    (k : Mode) :
    pairing (mixedFold (-k)) (selfFold (-k)) +
      pairing (mixedFold k) (selfFold k) =
      2 * pairing (mixedFold k) (selfFold k) := by
  rw [outputPairing_even
    conjugate pairing pairConjugateBoth
    mixedFold selfFold mixedReality selfReality k]
  ring

end

end OutputRealityNoGo
end NSBControl
