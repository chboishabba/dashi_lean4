import Integration.E8StructuredFullWeylRecognition
import Mathlib

/-!
# Monster 3B ATLAS symplectic-12 cross-kernel receipt

External source work has materially narrowed the previously generic Monster
normalizer wall.

ATLAS directly publishes an absolutely irreducible 12-dimensional GF(3)
representation of `2.Suz:2`.  Breuer--Magaard--Wilson Appendix 9.2 independently
uses the ATLAS 38-dimensional GF(3) representation of

  3^(1+12):6.Suz.2

and states that the same 12-dimensional irreducible `2.Suz.2` module preserves
a symplectic form and embeds in `Sp(12,3)`, the automorphism group of the
extraspecial `3_+^(1+12)`.

Companion Agda already owns the repository standard symplectic quotient

  X6 + X6*

and the finite Heisenberg central extension.  It now also owns a typed
source-to-repository symplectic-basis recognition interface plus the central
cocycle-correction condition needed to lift an Sp(12,3) quotient action to the
repository's asymmetric Heisenberg cocycle.

This file is only a cross-kernel/source receipt.  The actual published matrix
entries are not vendored here, so same-basis conjugation is deliberately not
promoted.
-/

namespace Integration.Monster3BAtlasSymplectic12Receipt

structure Receipt where
  directAtlasGroup : String
  directAtlasRepresentationId : String
  directFieldOrder : Nat
  directDimension : Nat
  directAbsolutelyIrreducible : Bool
  monsterNormalizerAtlasGroup : String
  monsterNormalizerAmbientDimension : Nat
  monsterNormalizerBlock24Plus14 : Bool
  sourceStatesSymplectic12Preserved : Bool
  sourceStatesEmbeddingInSp12_3 : Bool
  sourceStatesExtraspecialAutomorphismRole : Bool
  repositoryStandardX6PlusDualExists : Bool
  repositoryHeisenbergCentralExtensionExists : Bool
  sourceToRepositoryIntertwinerCompilerTypedOnAgda : Bool
  cocycleCentralCorrectionExposedOnAgda : Bool
  rawMatricesVendored : Bool
  concreteSymplecticBasisChangePaid : Bool
  concreteHeisenbergConjugationPaid : Bool
  deriving Repr

def canonicalReceipt : Receipt where
  directAtlasGroup := "2.Suz:2"
  directAtlasRepresentationId := "2Suzd2G1-f3r12aB0"
  directFieldOrder := 3
  directDimension := 12
  directAbsolutelyIrreducible := true
  monsterNormalizerAtlasGroup := "3^(1+12):6.Suz.2"
  monsterNormalizerAmbientDimension := 38
  monsterNormalizerBlock24Plus14 := true
  sourceStatesSymplectic12Preserved := true
  sourceStatesEmbeddingInSp12_3 := true
  sourceStatesExtraspecialAutomorphismRole := true
  repositoryStandardX6PlusDualExists := true
  repositoryHeisenbergCentralExtensionExists := true
  sourceToRepositoryIntertwinerCompilerTypedOnAgda := true
  cocycleCentralCorrectionExposedOnAgda := true
  rawMatricesVendored := false
  concreteSymplecticBasisChangePaid := false
  concreteHeisenbergConjugationPaid := false

inductive SourceExistenceCreatesSameBasisAction : Prop

theorem source_receipt_does_not_create_same_basis_action :
    ¬ SourceExistenceCreatesSameBasisAction := by intro h; cases h

structure Boundary where
  MonsterNormalizerSymplectic12SourcePaid : Bool
  repositoryHeisenbergHostPaidCrossKernel : Bool
  symplecticIntertwinerCompilerPaidCrossKernel : Bool
  actualAtlasMatrixImportPaid : Bool
  actualX6PlusDualSameActionPaid : Bool
  actualHeisenbergNormalizerConjugationPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  MonsterNormalizerSymplectic12SourcePaid := true
  repositoryHeisenbergHostPaidCrossKernel := true
  symplecticIntertwinerCompilerPaidCrossKernel := true
  actualAtlasMatrixImportPaid := false
  actualX6PlusDualSameActionPaid := false
  actualHeisenbergNormalizerConjugationPaid := false

end Integration.Monster3BAtlasSymplectic12Receipt
