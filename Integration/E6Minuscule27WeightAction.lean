import Integration.E8ExceptionalBranchingBridge

/-!
# E6 minuscule-27 weight/action execution boundary

Lean mirror of the exact finite audit owned by the Agda repository script
`scripts/check_e6_minuscule27_weight_action.py`.

The audit starts from the standard 240-root E8 carrier, selects one mixed
27-root fibre in the `E6 x A2` branching, projects to the E6 subspace, and
checks the minuscule-27 finite geometry and Weyl action:

* 27 distinct projected weights;
* common squared norm `16/3` in doubled-coordinate normalization;
* pair inner products `4/3` (216 pairs) and `-8/3` (135 pairs);
* root-difference graph degree 16;
* every E6 root reflection preserves the selected fibre;
* projection intertwines all 72 root reflections;
* the action is transitive on the 27 weights;
* six independent reflection permutations generate 51840 elements.

This file records those exact-execution facts without pretending the Python run
is a Lean kernel proof.  The finite 27-weight orbit is also explicitly not the
27-dimensional Albert representation carrier.
-/

namespace Integration.E6Minuscule27WeightAction

structure ExecutionReceipt where
  e8RootCount : Nat
  e6RootCount : Nat
  a2RootCount : Nat
  mixedFibreCount : Nat
  rootsPerMixedFibre : Nat
  projectedWeightCount : Nat
  commonWeightNormNumeratorThirds : Nat
  highInnerProductPairCount : Nat
  lowInnerProductPairCount : Nat
  rootDifferenceDegree : Nat
  e6RootReflectionsPreserveSelectedFibre : Bool
  projectionIntertwinesAllE6RootReflections : Bool
  weightOrbitTransitive : Bool
  generatedPermutationGroupOrder : Nat
  exactPythonAuditPassed : Bool
  deriving Repr

def canonicalExecutionReceipt : ExecutionReceipt where
  e8RootCount := 240
  e6RootCount := 72
  a2RootCount := 6
  mixedFibreCount := 6
  rootsPerMixedFibre := 27
  projectedWeightCount := 27
  commonWeightNormNumeratorThirds := 16
  highInnerProductPairCount := 216
  lowInnerProductPairCount := 135
  rootDifferenceDegree := 16
  e6RootReflectionsPreserveSelectedFibre := true
  projectionIntertwinesAllE6RootReflections := true
  weightOrbitTransitive := true
  generatedPermutationGroupOrder := 51840
  exactPythonAuditPassed := true

structure Boundary where
  mixedRootFibreCountPaid : Bool
  minusculeWeightGeometryPaidAtExecutionGrade : Bool
  reflectionIntertwiningPaidAtExecutionGrade : Bool
  transitiveWeylActionPaidAtExecutionGrade : Bool
  order51840PaidAtExecutionGrade : Bool
  executionReceiptCountsAsLeanKernelProof : Bool
  weightOrbitIsAlbertCarrier : Bool
  fullE6RepresentationConstructedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  mixedRootFibreCountPaid := true
  minusculeWeightGeometryPaidAtExecutionGrade := true
  reflectionIntertwiningPaidAtExecutionGrade := true
  transitiveWeylActionPaidAtExecutionGrade := true
  order51840PaidAtExecutionGrade := true
  executionReceiptCountsAsLeanKernelProof := false
  weightOrbitIsAlbertCarrier := false
  fullE6RepresentationConstructedHere := false

/-- The older branching owner still records a literal 27-sized positive fibre. -/
theorem branching_positive_fibre_is_27 :
    Integration.E8ExceptionalBranchingBridge.canonicalE8E6A2RootSplitReceipt.positiveFibreCount = 27 :=
  rfl

end Integration.E6Minuscule27WeightAction
