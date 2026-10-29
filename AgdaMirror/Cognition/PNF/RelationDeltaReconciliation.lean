import Mathlib

/-!
# SensibLaw relation-delta reconciliation mirror

This file mirrors the executable laws owned by
`DASHI/Cognition/PNF/RelationDeltaReconciliationExact.agda`.

Agda remains the golden proof source. This Lean file is a cross-prover consumer.
It does not create a second semantic authority.
-/

namespace AgdaMirror.Cognition.PNF.RelationDeltaReconciliation

structure RelationDeltaReceipt where
  desiredRows : Nat
  currentRows : Nat
  addedRows : Nat
  removedRows : Nat
  replacedRows : Nat
  unchangedRowsSkipped : Nat
  physicalRowMutations : Nat
  desiredPartitionExact :
    desiredRows = addedRows + replacedRows + unchangedRowsSkipped
  currentPartitionExact :
    currentRows = removedRows + replacedRows + unchangedRowsSkipped
  physicalMutationExact :
    physicalRowMutations = addedRows + removedRows + 2 * replacedRows

structure RelationDeltaOwnerRouting where
  candidateMutationOwnerCount : Nat
  privateCandidateMutationBypassCount : Nat
  hotPathReconcilerOwnerCount : Nat
  reconciliationReceiptOwnerCount : Nat
  candidateMutationOwnerUnique : candidateMutationOwnerCount = 1
  privateCandidateMutationBypassZero : privateCandidateMutationBypassCount = 0
  hotPathReconcilerOwnerUnique : hotPathReconcilerOwnerCount = 1
  reconciliationReceiptOwnerMatchesHotPath :
    reconciliationReceiptOwnerCount = hotPathReconcilerOwnerCount

def singleCandidateRelationOwner : RelationDeltaOwnerRouting where
  candidateMutationOwnerCount := 1
  privateCandidateMutationBypassCount := 0
  hotPathReconcilerOwnerCount := 1
  reconciliationReceiptOwnerCount := 1
  candidateMutationOwnerUnique := rfl
  privateCandidateMutationBypassZero := rfl
  hotPathReconcilerOwnerUnique := rfl
  reconciliationReceiptOwnerMatchesHotPath := rfl

def noOpReceipt (retained : Nat) : RelationDeltaReceipt where
  desiredRows := retained
  currentRows := retained
  addedRows := 0
  removedRows := 0
  replacedRows := 0
  unchangedRowsSkipped := retained
  physicalRowMutations := 0
  desiredPartitionExact := by simp
  currentPartitionExact := by simp
  physicalMutationExact := by simp

theorem unchanged_relation_has_zero_physical_mutations (retained : Nat) :
    (noOpReceipt retained).physicalRowMutations = 0 := rfl

theorem candidate_mutation_owner_is_unique :
    singleCandidateRelationOwner.candidateMutationOwnerCount = 1 := rfl

theorem private_candidate_mutation_bypass_is_zero :
    singleCandidateRelationOwner.privateCandidateMutationBypassCount = 0 := rfl

theorem hot_path_reconciler_is_unique :
    singleCandidateRelationOwner.hotPathReconcilerOwnerCount = 1 := rfl

end AgdaMirror.Cognition.PNF.RelationDeltaReconciliation
