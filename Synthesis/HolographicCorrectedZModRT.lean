import Synthesis.HolographicZModCarrierFactorization
import Synthesis.HolographicMaxEntangledCutRT

namespace Synthesis.HolographicCorrectedZModRT

open Synthesis.HolographicZModCarrierFactorization
open Synthesis.HolographicMaxEntangledCutRT

/-- Balanced binary split of the upstream carrier type:

  ZMod (2^(k+k)) ≃ Fin (2^k) × Fin (2^k).

The equivalence is purely finite-carrier algebra; geometric subtree/minimal-cut
semantics remain separate. -/
noncomputable def balancedZModFactorEquiv (k : ℕ) :
    ZMod (2 ^ (k + k)) ≃ (Fin (2 ^ k) × Fin (2 ^ k)) :=
  zmodBinaryFactorEquiv k k

/-- Pull the corrected maximally-entangled Schmidt density kernel back to the
same **carrier type** used by the inspected upstream holographic source.

This proves that a corrected entangled state can live on a `ZMod (2^n)` carrier
(for the balanced `n=2k` split).  It deliberately does not claim that the
upstream `holographicState` or `holographicContract` produces this kernel. -/
noncomputable def correctedZModDensity (k : ℕ) :
    Matrix (ZMod (2 ^ (k + k))) (ZMod (2 ^ (k + k))) ℝ :=
  fun x y =>
    maxEntangledSchmidtDensity k
      (balancedZModFactorEquiv k x)
      (balancedZModFactorEquiv k y)

/-- Exact same-carrier pullback law. -/
theorem correctedZModDensity_pullback
    (k : ℕ)
    (x y : Fin (2 ^ k) × Fin (2 ^ k)) :
    correctedZModDensity k
      ((balancedZModFactorEquiv k).symm x)
      ((balancedZModFactorEquiv k).symm y)
      = maxEntangledSchmidtDensity k x y := by
  simp [correctedZModDensity]

/-- The reduced entropy attached to the corrected ZMod-carrier state is the
same reduced entropy already proved for the Schmidt model, because the carrier
change is an explicit equivalence rather than a change of state data. -/
noncomputable def correctedZModReducedEntropy (k : ℕ) : ℝ :=
  reducedVonNeumannEntropy k

/-- Corrected RT entropy on the ZMod carrier, for the balanced split. -/
theorem correctedZModRTEntropy (k : ℕ) :
    correctedZModReducedEntropy k = correctedCutEntropy k := by
  exact (correctedRTSameObjectEntropy k).symm

/-- Status boundary. -/
def correctedEntangledStateOnZModCarrierOwned : Bool := true

def balancedZModCarrierRTEntropyOwned : Bool := true

def upstreamTreeContractionStillMustBeReplacedOrProvedEquivalent : Bool := true

def upstreamNamedStateStillNotThisCorrectedState : Bool := true

def geometricSubtreeIdentificationStillRequired : Bool := true

def minimalCutIdentificationStillRequired : Bool := true

def genericUnbalancedDepthSplitStillRequiredIfNeeded : Bool := true

def physicalAdSCFTStillRequired : Bool := true

end Synthesis.HolographicCorrectedZModRT
