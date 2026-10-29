namespace DASHI.Interop.SublinearTopicConductorCostExact

inductive TopicShape where
  | frontierBlocked (blockers : Nat)
  | sequential
  | parallelBySubEigen (dimension : Nat)
deriving Repr, DecidableEq

def workerWidth (cap : Nat) : TopicShape → Nat
  | .frontierBlocked blockers => Nat.min cap blockers
  | .sequential => if cap = 0 then 0 else 1
  | .parallelBySubEigen dimension => Nat.min cap dimension

structure DynamicConductorBoundary where
  costFormulaReference : String
  workerCapacityIsBudgetNotModeSelector : Bool
  frontierBlockedWidthUsesBlockerCount : Bool
  sequentialWidthIsOneWhenCapacityPositive : Bool
  parallelWidthUsesSubEigenDimension : Bool
  lowerAlphaSubtopicsRemainPreserved : Bool
  lowerAlphaSubtopicsBecomeSequencedInternalPackets : Bool
  rolledPacketsRemainEligibleForCrossPollination : Bool
  alphaCreatesTruth : Bool
  alphaCreatesProofAuthority : Bool
  workerAllocationCreatesSemanticAuthority : Bool
  parallelDispatchRequiresNoTypedMeet : Bool
  candidateOnly : Bool
deriving Repr, DecidableEq

def canonicalDynamicConductorBoundary : DynamicConductorBoundary :=
  {
    costFormulaReference :=
      "C(T_k,W)=alpha(T_k)*(UnblockedGoals/TotalGoals)*min(W_cap,dim(SubEigens),W)-TokenCost(W)"
    workerCapacityIsBudgetNotModeSelector := true
    frontierBlockedWidthUsesBlockerCount := true
    sequentialWidthIsOneWhenCapacityPositive := true
    parallelWidthUsesSubEigenDimension := true
    lowerAlphaSubtopicsRemainPreserved := true
    lowerAlphaSubtopicsBecomeSequencedInternalPackets := true
    rolledPacketsRemainEligibleForCrossPollination := true
    alphaCreatesTruth := false
    alphaCreatesProofAuthority := false
    workerAllocationCreatesSemanticAuthority := false
    parallelDispatchRequiresNoTypedMeet := true
    candidateOnly := true
  }

theorem frontierBlockedWidthLaw (cap blockers : Nat) :
    workerWidth cap (.frontierBlocked blockers) = Nat.min cap blockers := rfl

theorem sequentialWidthLaw (cap : Nat) :
    workerWidth (Nat.succ cap) .sequential = 1 := by
  simp [workerWidth]

theorem parallelSubEigenWidthLaw (cap dimension : Nat) :
    workerWidth cap (.parallelBySubEigen dimension) = Nat.min cap dimension := rfl

theorem fourBlockersWithTwentyWorkersUsesFour :
    workerWidth 20 (.frontierBlocked 4) = 4 := by decide

theorem sequentialWithTwentyWorkersUsesOne :
    workerWidth 20 .sequential = 1 := by decide

theorem fiveSubEigensWithTwentyWorkersUsesFive :
    workerWidth 20 (.parallelBySubEigen 5) = 5 := by decide

theorem capacityDoesNotSelectMode :
    canonicalDynamicConductorBoundary.workerCapacityIsBudgetNotModeSelector = true := rfl

theorem lowerAlphaWorkIsPreserved :
    canonicalDynamicConductorBoundary.lowerAlphaSubtopicsRemainPreserved = true := rfl

theorem alphaDoesNotCreateTruth :
    canonicalDynamicConductorBoundary.alphaCreatesTruth = false := rfl

theorem alphaDoesNotCreateProofAuthority :
    canonicalDynamicConductorBoundary.alphaCreatesProofAuthority = false := rfl

theorem allocationDoesNotCreateSemanticAuthority :
    canonicalDynamicConductorBoundary.workerAllocationCreatesSemanticAuthority = false := rfl

theorem parallelStillRequiresNoTypedMeet :
    canonicalDynamicConductorBoundary.parallelDispatchRequiresNoTypedMeet = true := rfl

end DASHI.Interop.SublinearTopicConductorCostExact
