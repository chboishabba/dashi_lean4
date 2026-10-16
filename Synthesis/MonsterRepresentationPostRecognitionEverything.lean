import Synthesis.MonsterWholeCharacterModuleAdapterLive
import Synthesis.MonsterWholeCharacterModuleAdapterLiveRegression
import Synthesis.MonsterWholeCharacterSimpleSource
import Synthesis.MonsterWholeCharacterSimpleSourceRegression
import Synthesis.MonsterMaschkeAndCharacterDimension
import Synthesis.MonsterMaschkeAndCharacterDimensionRegression
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
* Maschke semisimplicity for the finite nonmodular group representation;
* whole-character identity evaluated at the identity -> corresponding finrank
  ratio, including coefficient 90;
* simple finite-dimensional representation over an algebraically closed field
  -> one-dimensional/scalar self-intertwiner space by pinned mathlib Schur;
* one-simple-type semisimple/isotypic assembly;
* post-recognition finite-copy count cancellation;
* complementary two-isotypic-block assembly and post-recognition 12+78 counts;
* proof-relevant Schur multiplicity coordinates
  `Hom_G(H,H^n) ~= (Fin n -> k)`;
* exact finite-copy coordinate evaluation/recovery;
* canonical tensor finite-copy equivalence
  `H tensor (Fin n -> k) ~= (Fin n -> H)`, hence a post-isotypy tensor
  equivalence with the recognized sector.

Consequently restriction linearity, Schur, Maschke semisimplicity, an arbitrary
simple-type classifier, the FDRep/module bridge, a separate finrank-ratio
witness, and the abstract tensor finite-copy equivalence are no longer
Monster-specific leaves.  The character/isotypy seam has collapsed to attaching
the actual W_zeta|E and H_zeta linear carriers to the same FDRep theory and
transporting the already-owned actual-kernel ninety-copy character identity onto
those SAME carriers.

Not produced here: the actual weight-two Monster representation, actual 196883
invariant subspace/direct summand, actual central linear operator and zeta
orientation, the actual same-object FDRep attachments/whole-character transport,
or the actual 6.Suz/normalizer action and 12+78 action orientation.
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
  absoluteZetaOrientationProducedHere := false

end Synthesis.MonsterRepresentationPostRecognitionEverything
