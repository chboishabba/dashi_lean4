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
import Synthesis.MonsterNormalizerHomAction
import Synthesis.MonsterNormalizerHomActionRegression
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

* invariant-subspace and central-eigenspace restricted representations;
* FDRep <-> group-algebra same-action/submodule adapter;
* whole-character simple-source classification;
* Maschke semisimplicity and character-at-identity dimension ratios;
* Schur scalar self-intertwiners;
* one-simple isotypic assembly / copy count;
* two-simple character multiplicity determination and 12+78 assembly;
* `Hom_G(H,H^n) ~= k^n` coordinates with evaluation/recovery;
* `H tensor k^n ~= H^n` finite-copy tensor equivalence;
* canonical induced normalizer action on `Hom_E(H,W)` from actual normalizer
  lifts on H and W that implement the same conjugation action on E.

Consequently the multiplicity-space normalizer action itself is not independent
third-carrier data: after the actual normalizer lifts/conjugation laws on H and W
are supplied, the Hom action is canonical.  Projective cocycle laws, absolute
zeta orientation and same-object selected-phase character transport remain
actual Monster inputs.
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
  inducedHomNormalizerActionAvailable : Bool
  independentMultiplicityNormalizerActionIsMonsterSpecificInput : Bool
  actualMonsterSameObjectInputsProducedHere : Bool
  actualMonsterInvariantSubspaceProducedHere : Bool
  actualCentralLinearOperatorProducedHere : Bool
  actualWholeCharacterTransportProducedHere : Bool
  actualNormalizerLiftsOnHandWProducedHere : Bool
  actualProjectiveCocycleLawsProducedHere : Bool
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
  inducedHomNormalizerActionAvailable := true
  independentMultiplicityNormalizerActionIsMonsterSpecificInput := false
  actualMonsterSameObjectInputsProducedHere := false
  actualMonsterInvariantSubspaceProducedHere := false
  actualCentralLinearOperatorProducedHere := false
  actualWholeCharacterTransportProducedHere := false
  actualNormalizerLiftsOnHandWProducedHere := false
  actualProjectiveCocycleLawsProducedHere := false
  actualSuzukiMultiplicityCharacterTransportProducedHere := false
  absoluteZetaOrientationProducedHere := false

end Synthesis.MonsterRepresentationPostRecognitionEverything
