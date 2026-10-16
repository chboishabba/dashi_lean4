import Synthesis.MonsterWholeCharacterIsotypicAssembly
import Synthesis.MonsterWholeCharacterIsotypicAssemblyRegression
import Synthesis.MonsterTwoIsotypicBlockAssembly
import Synthesis.MonsterTwoIsotypicBlockAssemblyRegression
import Synthesis.MonsterMultiplicitySchurCoordinates
import Synthesis.MonsterMultiplicitySchurCoordinatesRegression
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
* simple finite-dimensional representation over an algebraically closed field
  -> one-dimensional/scalar self-intertwiner space by pinned mathlib Schur;
* one-simple-type semisimple/isotypic assembly;
* post-recognition finite-copy count cancellation (including the lawful 90);
* complementary two-isotypic-block assembly and post-recognition 12+78 counts;
* proof-relevant Schur multiplicity coordinates
  `Hom_G(H,H^n) ~= (Fin n -> k)`;
* exact finite-copy coordinate evaluation/recovery.

Thus constituent/zeta restriction linearity and the abstract Schur property are
not independent Monster source leaves after the actual invariant subspace /
central linear operator / simple FDRep attachment is paid.

Not produced here: the actual weight-two Monster representation, actual 196883
invariant subspace/direct summand, actual central linear operator and zeta
orientation/same-object attachment, actual simple-type classifier,
6.Suz/normalizer action, or a tensor same-object equivalence on the actual
Monster sector.
-/

namespace Synthesis.MonsterRepresentationPostRecognitionEverything

structure Boundary where
  invariantRestrictionCompilerAvailable : Bool
  nestedRestrictionCompilerAvailable : Bool
  linearEigenspaceCompilerAvailable : Bool
  commutingActionEigenspaceInvarianceAvailable : Bool
  restrictionLinearityIsCompilerOutput : Bool
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
  actualMonsterSameObjectInputsProducedHere : Bool
  actualMonsterInvariantSubspaceProducedHere : Bool
  actualCentralLinearOperatorProducedHere : Bool
  actualSuzukiNormalizerActionProducedHere : Bool
  absoluteZetaOrientationProducedHere : Bool
  actualTensorEvaluationEquivalenceProducedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  invariantRestrictionCompilerAvailable := true
  nestedRestrictionCompilerAvailable := true
  linearEigenspaceCompilerAvailable := true
  commutingActionEigenspaceInvarianceAvailable := true
  restrictionLinearityIsCompilerOutput := true
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
  actualMonsterSameObjectInputsProducedHere := false
  actualMonsterInvariantSubspaceProducedHere := false
  actualCentralLinearOperatorProducedHere := false
  actualSuzukiNormalizerActionProducedHere := false
  absoluteZetaOrientationProducedHere := false
  actualTensorEvaluationEquivalenceProducedHere := false

end Synthesis.MonsterRepresentationPostRecognitionEverything
