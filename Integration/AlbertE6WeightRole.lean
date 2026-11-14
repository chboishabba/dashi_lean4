import Integration.E6Minuscule27WeightAction

/-!
# Correct the three different "27" roles

The current cross-prover state contains three mathematically different uses of
27:

1. a finite ternary 27-point codebook;
2. the 27-dimensional rational Albert algebra, constructed/proved on the Agda
   branch;
3. a finite 27-element mixed-root fibre whose correct finite target is the
   27-weight orbit of the minuscule E6 representation.

Cardinality alone cannot identify (1) or (3) with the representation space (2).
The Agda branch source-writes the universal Albert Jordan and cubic
characteristic identities and constructs explicit C3, S3, C7 and C7 semidirect
C3 automorphism subgroups.  The commuting matrix-index S3 and octonion C21
finite actions give 126 distinct product action labels in the exact executable
audit.  This Lean tranche records that cross-prover grade without duplicating
the octonion/Albert algebra and without promoting the finite subgroup to full
F4 or E6.
-/

namespace Integration.AlbertE6WeightRole

structure Boundary where
  finiteTernaryCodebookHas27Points : Bool
  rationalAlbertRepresentationDimension27 : Bool
  e8MixedFibreHas27Roots : Bool
  finiteRootFibreIsAlbertRepresentationSpace : Bool
  finiteTernaryCarrierIsAlbertRepresentationSpace : Bool
  e8MixedFibreTargetsWeightOrbit : Bool
  ternary27TargetsFiniteCodebook : Bool
  e6WeightActionAuditAvailable : Bool
  agdaAlbertUniversalIdentitySourceWritten : Bool
  agdaAlbertCharacteristicIdentitySourceWritten : Bool
  agdaConcreteC3AutomorphismSubgroup : Bool
  agdaConcreteS3AutomorphismSubgroup : Bool
  agdaConcreteC7OctonionAlbertSubgroup : Bool
  agdaConcreteC21OctonionSubgroup : Bool
  agdaConcreteFinite126AlbertSubgroup : Bool
  agdaFinite126CountsAsLeanKernelProof : Bool
  agdaFullG2Constructed : Bool
  agdaFullF4Constructed : Bool
  agdaFullE6Constructed : Bool
  crossProverFactsCountAsLeanKernelProof : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  finiteTernaryCodebookHas27Points := true
  rationalAlbertRepresentationDimension27 := true
  e8MixedFibreHas27Roots := true
  finiteRootFibreIsAlbertRepresentationSpace := false
  finiteTernaryCarrierIsAlbertRepresentationSpace := false
  e8MixedFibreTargetsWeightOrbit := true
  ternary27TargetsFiniteCodebook := true
  e6WeightActionAuditAvailable := true
  agdaAlbertUniversalIdentitySourceWritten := true
  agdaAlbertCharacteristicIdentitySourceWritten := true
  agdaConcreteC3AutomorphismSubgroup := true
  agdaConcreteS3AutomorphismSubgroup := true
  agdaConcreteC7OctonionAlbertSubgroup := true
  agdaConcreteC21OctonionSubgroup := true
  agdaConcreteFinite126AlbertSubgroup := true
  agdaFinite126CountsAsLeanKernelProof := false
  agdaFullG2Constructed := false
  agdaFullF4Constructed := false
  agdaFullE6Constructed := false
  crossProverFactsCountAsLeanKernelProof := false

/-- The execution-grade E6 finite target really has 27 weights; this is still a
finite set of weights, not a 27-dimensional vector-space carrier. -/
theorem e6_weight_audit_count_is_27 :
    Integration.E6Minuscule27WeightAction.canonicalExecutionReceipt.projectedWeightCount = 27 :=
  rfl

end Integration.AlbertE6WeightRole
