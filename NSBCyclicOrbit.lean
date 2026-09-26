import NSBControl.CyclicHelicalVectorTransform
import NSBControl.SelfOrbitCommutatorCarrier
import NSBControl.SingleSelfCommutatorOrbit
import NSBControl.SpectatorFibreLegTransport
import NSBControl.CompleteSelfOrbitCollapse
import NSBControl.OutputPairingCollapse
import NSBControl.OutputRealityNoGo
import NSBControl.SelectedSelfResolvedRecombination
import NSBControl.CombinedSpacetimePayment
import NSBControl.CombinedPaymentToWeightedWork
import NSBControl.CombinedCurrentEndgame
import NSBControl.DirectCombinedCut
import NSBControl.SharedWeightedCut

namespace NSBCyclicOrbit

open NSBControl.CyclicHelicalVectorTransform

example (a b : ℝ) : (-b) - a = -(a + b) := by
  exact plusMinusCoefficient a b

example (a b : ℝ) : b - (-a) = a + b := by
  exact minusPlusCoefficient a b

example (a b : ℝ) : (-b) - (-a) = a - b := by
  exact minusMinusCoefficient a b


example
    (modeNorm : Mode → ℝ)
    (τ : Triad)
    (signP signQ signK : HelicitySign) :
    baseCoefficient modeNorm τ signP signQ -
      pLegCoefficient modeNorm τ signK signQ +
      qLegCoefficient modeNorm τ signK signP = 0 := by
  exact orientedCyclicCoefficient_zero modeNorm τ signP signQ signK

end NSBCyclicOrbit
