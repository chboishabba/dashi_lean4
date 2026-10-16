import Synthesis.MonsterWholeCharacterModuleAdapterLive
import Synthesis.MonsterWholeCharacterModuleAdapterLiveRegression
import Synthesis.MonsterWholeCharacterSimpleSource
import Synthesis.MonsterWholeCharacterSimpleSourceRegression
import Synthesis.MonsterMaschkeAndCharacterDimension
import Synthesis.MonsterMaschkeAndCharacterDimensionRegression
import Synthesis.MonsterCharacterDeterminationLive
import Synthesis.MonsterCharacterDeterminationLiveRegression
import Synthesis.MonsterWholeCharacterIsotypicAssembly
import Synthesis.MonsterWholeCharacterIsotypicAssemblyRegression
import Synthesis.MonsterTwoIsotypicBlockAssembly
import Synthesis.MonsterTwoIsotypicBlockAssemblyRegression
import Synthesis.MonsterMultiplicitySchurCoordinates
import Synthesis.MonsterMultiplicitySchurCoordinatesRegression
import Synthesis.MonsterTensorEvaluationFiniteCopies
import Synthesis.MonsterTensorEvaluationFiniteCopiesRegression
import Synthesis.MonsterInvariantRestriction
import Synthesis.MonsterInvariantRestrictionRegression
import Synthesis.MonsterLinearEigenspaceRestriction
import Synthesis.MonsterLinearEigenspaceRestrictionRegression
import Synthesis.MonsterSchurFromSimpleFDRep
import Synthesis.MonsterSchurFromSimpleFDRepRegression

/-!
# Monster representation post-recognition generic tail

Focused rollup for reusable representation-theory machinery surrounding the
actual same-object Monster inputs.

Available in this tail:

* actual invariant subspace -> restricted linear representation + equivariant
  inclusion, including nested restrictions;
* linear central operator + commuting action -> literal invariant eigenspace,
  restricted representation and inclusion intertwiner;
* canonical FDRep <-> group-algebra same-action/submodule adapter;
* SAME whole-character identity `chi(V)=a chi(H)` -> every occurring simple
  source has H's type;
* Maschke semisimplicity and character-at-identity -> finrank ratio;
* simple FDRep -> scalar self-intertwiners by pinned mathlib Schur;
* one-simple-type isotypic assembly and post-recognition copy count;
* two-simple character `chi(V)=chi(T)+chi(S)` -> one-copy Hom multiplicities
  for T,S and zero for every other simple type;
* complementary two-isotypic-block assembly / post-recognition 12+78 counts;
* Schur multiplicity coordinates `Hom_G(H,H^n) ~= (Fin n -> k)` and exact
  coordinate evaluation/recovery;
* canonical tensor finite-copy equivalence
  `H tensor (Fin n -> k) ~= (Fin n -> H)`.

Consequently restriction linearity, Schur, Maschke semisimplicity, arbitrary
simple-type classifiers, the FDRep/module bridge, separate finrank-ratio data,
the abstract tensor finite-copy equivalence, and an abstract 12+78 decomposition
intertwiner are not independent Monster-specific leaves.  For both the H_zeta
isotypy and the later 12+78 multiplicity decomposition, the live scientific seam
is SAME-object transport of source/class character information onto the actual
linear representations.

Not produced here: the actual weight-two Monster representation, actual 196883
invariant subspace/direct summand, actual central linear operator and absolute
zeta orientation, actual W_zeta/H_zeta FDRep attachments and ninety-character
transport, or the actual 6.Suz/normalizer multiplicity action plus its selected-
phase 12+78 character transport.
-/

namespace Synthesis.MonsterRepresentationPostRecognitionEverything

structure Boundary where
  invariantRestrictionCompilerAvailable : Bool
  nestedRestrictionCompilerAvailable : Bool
  linearEigenspaceCompilerAvailable : Bool
  commutingActionEigenspaceInvarianceAvailable : Bool
  restrictionLinearityIsCompilerOutput : Bool
  fdrepModuleAdapterAvailable : Bool
  wholeCharacterSimpleSourceClassifierAvailable : Bool
  maschkeSemisimplicityAvailable : Bool
  characterCoefficientGivesDimensionRatio : Bool
  arbitrarySimpleTypeClassifierIsMonsterSpecificInput : Bool
  semisimplicityIsMonsterSpecificInput : Bool
  separateFinrankRatioIsMonsterSpecificInput : Bool
  simpleFDRepSchurRankOneAvailable : Bool
  irreducibleSelfIntertwinersScalarAvailable : Bool
  schurIsMonsterSpecificInput : Bool
  oneTypeIsotypicAssemblyAvailable : Bool
  postRecognitionCopyCountAvailable : Bool
  twoSimpleCharacterMultiplicityAvailable : Bool
  otherSimpleMultiplicityZeroAvailable : Bool
  twelveSeventyEightIntertwinerIsIndependentMonsterInput : Bool
  twoBlockAssemblyAvailable : Bool
  postRecognitionTwelveSeventyEightCountsAvailable : Bool
  schurMultiplicityCoordinatesAvailable : Bool
  ninetyMultiplicityCoordinatesAvailable : Bool
  coordinateEvaluationRecoveryAvailable : Bool
  tensorFiniteCopiesCompilerAvailable : Bool
  postIsotypyTensorEquivalenceAvailable : Bool
  tensorEquivalenceIsMonsterSpecificInput : Bool
  actualMonsterSameObjectInputsProducedHere : Bool
  actualMonsterInvariantSubspaceProducedHere : Bool
  actualCentralLinearOperatorProducedHere : Bool
  actualWholeCharacterTransportProducedHere : Bool
  actualSuzukiNormalizerActionProducedHere : Bool
  actualSuzukiMultiplicityCharacterTransportProducedHere : Bool
  absoluteZetaOrientationProducedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  invariantRestrictionCompilerAvailable := true
  nestedRestrictionCompilerAvailable := true
  linearEigenspaceCompilerAvailable := true
  commutingActionEigenspaceInvarianceAvailable := true
  restrictionLinearityIsCompilerOutput := true
  fdrepModuleAdapterAvailable := true
  wholeCharacterSimpleSourceClassifierAvailable := true
  maschkeSemisimplicityAvailable := true
  characterCoefficientGivesDimensionRatio := true
  arbitrarySimpleTypeClassifierIsMonsterSpecificInput := false
  semisimplicityIsMonsterSpecificInput := false
  separateFinrankRatioIsMonsterSpecificInput := false
  simpleFDRepSchurRankOneAvailable := true
  irreducibleSelfIntertwinersScalarAvailable := true
  schurIsMonsterSpecificInput := false
  oneTypeIsotypicAssemblyAvailable := true
  postRecognitionCopyCountAvailable := true
  twoSimpleCharacterMultiplicityAvailable := true
  otherSimpleMultiplicityZeroAvailable := true
  twelveSeventyEightIntertwinerIsIndependentMonsterInput := false
  twoBlockAssemblyAvailable := true
  postRecognitionTwelveSeventyEightCountsAvailable := true
  schurMultiplicityCoordinatesAvailable := true
  ninetyMultiplicityCoordinatesAvailable := true
  coordinateEvaluationRecoveryAvailable := true
  tensorFiniteCopiesCompilerAvailable := true
  postIsotypyTensorEquivalenceAvailable := true
  tensorEquivalenceIsMonsterSpecificInput := false
  actualMonsterSameObjectInputsProducedHere := false
  actualMonsterInvariantSubspaceProducedHere := false
  actualCentralLinearOperatorProducedHere := false
  actualWholeCharacterTransportProducedHere := false
  actualSuzukiNormalizerActionProducedHere := false
  actualSuzukiMultiplicityCharacterTransportProducedHere := false
  absoluteZetaOrientationProducedHere := false

end Synthesis.MonsterRepresentationPostRecognitionEverything
