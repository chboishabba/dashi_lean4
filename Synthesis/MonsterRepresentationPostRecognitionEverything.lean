import Synthesis.MonsterWholeCharacterIsotypicAssembly
import Synthesis.MonsterWholeCharacterIsotypicAssemblyRegression
import Synthesis.MonsterTwoIsotypicBlockAssembly
import Synthesis.MonsterTwoIsotypicBlockAssemblyRegression
import Synthesis.MonsterMultiplicitySchurCoordinates
import Synthesis.MonsterMultiplicitySchurCoordinatesRegression

/-!
# Monster representation post-recognition generic tail

Focused rollup for the reusable representation-theory machinery that begins only
after actual same-object Monster representation inputs have been supplied.

Available in this tail:

* one-simple-type semisimple/isotypic assembly;
* post-recognition finite-copy count cancellation (including the lawful 90);
* complementary two-isotypic-block assembly and post-recognition 12+78 counts;
* proof-relevant Schur multiplicity coordinates
  `Hom_G(H,H^n) ~= (Fin n -> k)`;
* exact finite-copy coordinate evaluation/recovery.

Not produced here: the literal W_zeta/H_zeta attachment, actual simple-type
classifier, 6.Suz/normalizer action, absolute zeta orientation, or a tensor
same-object equivalence on the actual Monster sector.
-/

namespace Synthesis.MonsterRepresentationPostRecognitionEverything

structure Boundary where
  oneTypeIsotypicAssemblyAvailable : Bool
  postRecognitionCopyCountAvailable : Bool
  twoBlockAssemblyAvailable : Bool
  postRecognitionTwelveSeventyEightCountsAvailable : Bool
  schurMultiplicityCoordinatesAvailable : Bool
  ninetyMultiplicityCoordinatesAvailable : Bool
  coordinateEvaluationRecoveryAvailable : Bool
  actualMonsterSameObjectInputsProducedHere : Bool
  actualSuzukiNormalizerActionProducedHere : Bool
  absoluteZetaOrientationProducedHere : Bool
  actualTensorEvaluationEquivalenceProducedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  oneTypeIsotypicAssemblyAvailable := true
  postRecognitionCopyCountAvailable := true
  twoBlockAssemblyAvailable := true
  postRecognitionTwelveSeventyEightCountsAvailable := true
  schurMultiplicityCoordinatesAvailable := true
  ninetyMultiplicityCoordinatesAvailable := true
  coordinateEvaluationRecoveryAvailable := true
  actualMonsterSameObjectInputsProducedHere := false
  actualSuzukiNormalizerActionProducedHere := false
  absoluteZetaOrientationProducedHere := false
  actualTensorEvaluationEquivalenceProducedHere := false

end Synthesis.MonsterRepresentationPostRecognitionEverything
