import Integration.E8StructuredFullWeylRecognition
import Mathlib

/-!
# Rational Albert / F4 derivation cross-kernel receipt

Companion Agda now contains an actual rational Albert algebra

  H_3(O_Q) = Q^3 + O_Q^3

built from the repository's exact rational Cayley--Dickson octonions, with:

* coordinate dimension 27;
* distinguished identity and trace;
* cubic determinant/norm;
* explicit symmetrised Jordan product;
* source-written commutativity, unit and Jordan identity;
* explicit coordinate S3 automorphisms preserving product/norm;
* explicit signed-basis octonion automorphisms lifted diagonally to Albert.

The exact executable `scripts/albert_inner_derivation_rank.py` reconstructs the
same product structure constants after clearing denominators and computes all
nonzero inner commutators `[L_ei,L_ej]`.  It checks the derivation identity on
all 729 basis products, obtains exact Q-rank 52, and exhibits the exact triality
split

  52 = 28 + 8 + 8 + 8

with bracket pattern

  [so8,so8] <= so8
  [so8,Vi] <= Vi
  [Vi,Vi] <= so8
  [V1,V2] <= V3, [V2,V3] <= V1, [V3,V1] <= V2.

This Lean file is deliberately a cross-kernel receipt.  It does not promote
Agda source or the Python exact-linear-algebra producer into Lean theorem
authority.  Full F4 automorphism-group/group-scheme recognition remains
strictly stronger than the paid Jordan/derivation algebra layer.
-/

namespace Integration.AlbertRationalF4DerivationReceipt

structure Receipt where
  rationalAlbertCarrierSourceWritten : Bool
  rationalAlbertCoordinateDimension : Nat
  cubicNormSourceWritten : Bool
  jordanProductSourceWritten : Bool
  jordanIdentitySourceWritten : Bool
  explicitCoordinateS3AutomorphismsSourceWritten : Bool
  signedBasisOctonionAutomorphismsSourceWritten : Bool
  signedBasisAlbertLiftSourceWritten : Bool
  localSignedBasisOctonionClosureOrder : Nat
  localCombinedFiniteAlbertSubgroupOrder : Nat
  exactBasisProductsChecked : Nat
  exactNonzeroInnerCommutators : Nat
  exactInnerDerivationSpanRank : Nat
  exactTrialitySo8Dimension : Nat
  exactTrialityVectorDimension : Nat
  exactTrialitySpinPlusDimension : Nat
  exactTrialitySpinMinusDimension : Nat
  exactTrialityBracketPatternChecked : Bool
  sourceBackedDerivationTypeF4Recorded : Bool
  leanKernelReprovedAlbertJordanLaws : Bool
  leanKernelReprovedRank52 : Bool
  fullF4AutomorphismGroupConstructed : Bool
  deriving Repr

def canonicalReceipt : Receipt where
  rationalAlbertCarrierSourceWritten := true
  rationalAlbertCoordinateDimension := 27
  cubicNormSourceWritten := true
  jordanProductSourceWritten := true
  jordanIdentitySourceWritten := true
  explicitCoordinateS3AutomorphismsSourceWritten := true
  signedBasisOctonionAutomorphismsSourceWritten := true
  signedBasisAlbertLiftSourceWritten := true
  localSignedBasisOctonionClosureOrder := 1344
  localCombinedFiniteAlbertSubgroupOrder := 8064
  exactBasisProductsChecked := 729
  exactNonzeroInnerCommutators := 324
  exactInnerDerivationSpanRank := 52
  exactTrialitySo8Dimension := 28
  exactTrialityVectorDimension := 8
  exactTrialitySpinPlusDimension := 8
  exactTrialitySpinMinusDimension := 8
  exactTrialityBracketPatternChecked := true
  sourceBackedDerivationTypeF4Recorded := true
  leanKernelReprovedAlbertJordanLaws := false
  leanKernelReprovedRank52 := false
  fullF4AutomorphismGroupConstructed := false

theorem dimension_ledger :
    canonicalReceipt.exactInnerDerivationSpanRank =
      canonicalReceipt.exactTrialitySo8Dimension +
      canonicalReceipt.exactTrialityVectorDimension +
      canonicalReceipt.exactTrialitySpinPlusDimension +
      canonicalReceipt.exactTrialitySpinMinusDimension := by
  decide

inductive CrossKernelReceiptCreatesLeanProof : Prop
inductive LieAlgebraF4CreatesFullAutomorphismGroup : Prop

theorem receipt_does_not_create_lean_kernel_proof :
    ¬ CrossKernelReceiptCreatesLeanProof := by intro h; cases h

theorem derivation_type_does_not_create_full_f4_group :
    ¬ LieAlgebraF4CreatesFullAutomorphismGroup := by intro h; cases h

structure Boundary where
  rationalAlbertAlgebraAvailableCrossKernel : Bool
  exactDerivationDimension52AvailableCrossKernel : Bool
  exactTrialityDecompositionAvailableCrossKernel : Bool
  fullF4AutomorphismGroupPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  rationalAlbertAlgebraAvailableCrossKernel := true
  exactDerivationDimension52AvailableCrossKernel := true
  exactTrialityDecompositionAvailableCrossKernel := true
  fullF4AutomorphismGroupPaid := false

end Integration.AlbertRationalF4DerivationReceipt
