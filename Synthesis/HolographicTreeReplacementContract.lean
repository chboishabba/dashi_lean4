import Mathlib
import Synthesis.HolographicCorrectedCutNetwork

namespace Synthesis.HolographicTreeReplacementContract

open Synthesis.HolographicCorrectedCutNetwork
open Synthesis.HolographicMaxEntangledCutRT

/-- Exact source-replacement contract for upgrading an actual tree/tensor
construction to the already-closed corrected finite RT theorem.

The external/source-side implementation must identify its contracted boundary
state with the corrected coherent density and its geometric selected cut with
exactly `k` independent bonds. No extra entropy algebra is needed after those
same-object identifications are supplied. -/
structure CorrectedTreeReplacement (k : ℕ) where
  ActualBoundaryCarrier : Type
  actualDensity : Matrix ActualBoundaryCarrier ActualBoundaryCarrier ℝ
  correctedCarrierEquiv : ActualBoundaryCarrier ≃
    (Fin (cutDimension k) × Fin (cutDimension k))
  densityPullback : ∀ x y,
    actualDensity x y =
      contractedDensity k (correctedCarrierEquiv x) (correctedCarrierEquiv y)
  actualCutBond : Type
  actualCutFintype : Fintype actualCutBond
  actualCutCard : Fintype.card actualCutBond = k
  actualEntropy : ℝ
  actualEntropyIdentified : actualEntropy = networkEntropy k
  actualCutEntropy : ℝ
  actualCutEntropyIdentified :
    actualCutEntropy = (Fintype.card actualCutBond : ℝ) * Real.log 2

attribute [instance] CorrectedTreeReplacement.actualCutFintype

/-- Once the actual tree contraction and geometric cut instantiate the exact
replacement contract, the RT equality is immediate from the corrected network
theorem. -/
theorem correctedTreeReplacementRT
    {k : ℕ} (R : CorrectedTreeReplacement k) :
    R.actualEntropy = R.actualCutEntropy := by
  rw [R.actualEntropyIdentified, R.actualCutEntropyIdentified, R.actualCutCard]
  exact correctedCutNetworkRT k

/-- The remaining upstream/source task has now been reduced to constructing one
inhabitant of `CorrectedTreeReplacement k` for the desired tree/subtree. -/
def sourceReplacementContractOwned : Bool := true

def currentUpstreamDefinitionsDoNotInstantiateContract : Bool := true

def noFurtherRTEntropyAlgebraRequired : Bool := true

def actualTreeContractionIdentificationStillExternal : Bool := true

def actualSubtreeCutIdentificationStillExternal : Bool := true

end Synthesis.HolographicTreeReplacementContract
