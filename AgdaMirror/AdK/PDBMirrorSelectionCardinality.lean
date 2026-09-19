import Mathlib
import AgdaMirror.AdK.PDBMirrorSelectedFixture
import AgdaMirror.AdK.SourceSelections

/-!
# Exact selection cardinalities for transparent AdK mirror fixtures

These theorems force the retained 4AKE/1AKE A/B selected manifestations through
the same typed selection predicates used by the CV theorem lane.

The expected profile is not a scientific source claim.  It is a deterministic
property of the imported transparent mirror rows under the current DASHI
selection/evaluator conventions.

No parser/hash/transport identifier proves these equalities; the Lean terms
compute them from the actual retained atom rows.
-/

namespace AgdaMirror.AdK.PDBMirrorSelectionCardinality

open AgdaMirror.AdK.SourceSelections
open AgdaMirror.AdK.PDBMirrorSelectedFixture

structure SelectionCardinalityProfile where
  theta1Lid : Nat
  hinge : Nat
  core : Nat
  theta2Nmp : Nat
  dlnLidBackbone : Nat
  dlnNmpBackbone : Nat
  dlnLidHeavy : Nat
  dlnNmpHeavy : Nat
  deriving DecidableEq, Repr

def selectionCardinalityProfile
    (fixture : PDBMirrorSelectedFixture) : SelectionCardinalityProfile :=
  { theta1Lid := (selectedAtoms fixture.configuration AgdaMirror.AdK.SourceSelections.theta1Lid).length
    hinge := (selectedAtoms fixture.configuration AgdaMirror.AdK.SourceSelections.hinge).length
    core := (selectedAtoms fixture.configuration AgdaMirror.AdK.SourceSelections.core).length
    theta2Nmp := (selectedAtoms fixture.configuration AgdaMirror.AdK.SourceSelections.theta2Nmp).length
    dlnLidBackbone :=
      (selectedAtoms fixture.configuration (dlnLid .backbone)).length
    dlnNmpBackbone :=
      (selectedAtoms fixture.configuration (dlnNmp .backbone)).length
    dlnLidHeavy :=
      (selectedAtoms fixture.configuration (dlnLid .heavy)).length
    dlnNmpHeavy :=
      (selectedAtoms fixture.configuration (dlnNmp .heavy)).length }

def canonicalMirrorSelectionCardinality : SelectionCardinalityProfile :=
  { theta1Lid := 132
    hinge := 20
    core := 124
    theta2Nmp := 40
    dlnLidBackbone := 152
    dlnNmpBackbone := 120
    dlnLidHeavy := 302
    dlnNmpHeavy := 212 }

def fourAKEChainASelectionCardinality : SelectionCardinalityProfile :=
  selectionCardinalityProfile fourAKEChainA

def fourAKEChainBSelectionCardinality : SelectionCardinalityProfile :=
  selectionCardinalityProfile fourAKEChainB

def oneAKEChainASelectionCardinality : SelectionCardinalityProfile :=
  selectionCardinalityProfile oneAKEChainA

def oneAKEChainBSelectionCardinality : SelectionCardinalityProfile :=
  selectionCardinalityProfile oneAKEChainB

theorem fourAKEChainASelectionCardinalityExact :
    fourAKEChainASelectionCardinality = canonicalMirrorSelectionCardinality := by
  decide

theorem fourAKEChainBSelectionCardinalityExact :
    fourAKEChainBSelectionCardinality = canonicalMirrorSelectionCardinality := by
  decide

theorem oneAKEChainASelectionCardinalityExact :
    oneAKEChainASelectionCardinality = canonicalMirrorSelectionCardinality := by
  decide

theorem oneAKEChainBSelectionCardinalityExact :
    oneAKEChainBSelectionCardinality = canonicalMirrorSelectionCardinality := by
  decide

end AgdaMirror.AdK.PDBMirrorSelectionCardinality
