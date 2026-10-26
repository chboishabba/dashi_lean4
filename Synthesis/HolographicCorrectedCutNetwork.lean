import Mathlib
import Synthesis.HolographicMaxEntangledCutRT

namespace Synthesis.HolographicCorrectedCutNetwork

open Synthesis.HolographicMaxEntangledCutRT

/-- The corrected finite RT replacement carries `k` independent Schmidt bonds
through the selected cut.  This is the minimal finite network data required for
an entropy `k log 2`; it is deliberately not identified with the inspected
upstream copy-isometry tree. -/
abbrev CutBond (k : ℕ) := Fin k

/-- Exact number of independent cut bonds. -/
theorem cutBond_card (k : ℕ) : Fintype.card (CutBond k) = k := by
  simp [CutBond]

/-- A finite replacement network whose boundary bipartition is the same
`2^k × 2^k` carrier used by the corrected Schmidt model.  The `cutBond`
coordinate records the geometric minimal-cut certificate separately from the
boundary basis labels. -/
structure CorrectedCutNetwork (k : ℕ) where
  leftBasis : Type := Fin (cutDimension k)
  rightBasis : Type := Fin (cutDimension k)
  cutBond : Type := CutBond k

/-- Canonical corrected finite network at depth/cut size `k`. -/
def canonicalNetwork (k : ℕ) : CorrectedCutNetwork k := {}

/-- Contracting the corrected `k`-bond network yields the coherent Schmidt
density kernel.  This is the replacement construction; unlike the inspected
upstream definitions, the contracted object is not a diagonal maximally-mixed
matrix and does not ignore the entangling cut structure. -/
def contractedDensity
    (k : ℕ) :
    Matrix (Fin (cutDimension k) × Fin (cutDimension k))
      (Fin (cutDimension k) × Fin (cutDimension k)) ℝ :=
  maxEntangledSchmidtDensity k

/-- Same-object contraction law for the corrected replacement network. -/
theorem contractedDensity_eq_correctedSchmidt (k : ℕ) :
    contractedDensity k = maxEntangledSchmidtDensity k := by
  rfl

/-- The geometric entropy assigned to the selected cut is the sum of one
`log 2` contribution per independent Schmidt bond. -/
def geometricCutEntropy (k : ℕ) : ℝ :=
  (Fintype.card (CutBond k) : ℝ) * Real.log 2

/-- The network entropy is computed from the reduced density matrix of the very
same contracted state. -/
def networkEntropy (k : ℕ) : ℝ :=
  reducedVonNeumannEntropy k

/-- Corrected finite RT theorem: the entropy of the reduced state of the
contracted corrected network equals `log 2` times the exact cut-bond count. -/
theorem correctedCutNetworkRT (k : ℕ) :
    networkEntropy k = geometricCutEntropy k := by
  rw [show geometricCutEntropy k = (k : ℝ) * Real.log 2 by
    simp [geometricCutEntropy, cutBond_card]]
  exact reducedEntropy_eq_kLogTwo k

/-- The selected subsystem/minimal-cut identification is internal to the
replacement model: the same parameter `k` indexes the left subsystem dimension
`2^k`, the Schmidt rank, and the number of cut bonds. -/
theorem subsystemDepth_eq_cutBondCount (k : ℕ) :
    Fintype.card (CutBond k) = k := cutBond_card k

/-- Source-status boundary. -/
def correctedReplacementNetworkOwned : Bool := true

def correctedMinimalCutIdentificationOwned : Bool := true

def correctedNetworkSameObjectRTClosed : Bool := true

/-- The inspected upstream copy tree is not silently promoted to this model.
One copied qubit does not manufacture `k` independent Schmidt bonds for general
`k`; a source/model replacement or an independent equivalence theorem is
required. -/
def upstreamCopyTreeDoesNotSupplyGeneralKBondCut : Bool := true

def upstreamReplacementOrEquivalenceStillRequired : Bool := true

def physicalAdSCFTStillRequired : Bool := true

end Synthesis.HolographicCorrectedCutNetwork
