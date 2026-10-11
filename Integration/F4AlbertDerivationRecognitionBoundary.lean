import Integration.F4RootWeylExact
import Integration.F4TrialityRootDatum
import Integration.AlbertRationalF4DerivationReceipt
import Mathlib

/-!
# Albert derivation algebra -> F4 recognition boundary

Companion Agda owns the actual rational Albert Jordan algebra `H_3(O_Q)`, its
arbitrary inner-derivation law, and a concrete linear Jordan-automorphism
carrier.  Exact companion computation on the literal 27-coordinate product now
supplies more than the earlier floating diagnostic:

* exact inner-derivation span rank `52`;
* exact triality basis `52 = 28 + 8_v + 8_s + 8_c`;
* exact triality bracket containment;
* four explicit commuting Cartan derivations;
* exact vector / two chiral half-spin roles;
* exact symbolic spectral projectors over `Q(i)` giving
  `4` zero-weight dimensions plus `48` one-dimensional nonzero root spaces,
  split `24 + 8 + 8 + 8`;
* no floating-point eigensolver in that upgraded root-space producer.

This branch independently owns standard F4 root data: `48` roots, standard
Cartan/Coxeter relations, and Weyl closure order `1152`.

What remains is not a root-count search.  It is the formal same-Lie-algebra /
classification theorem identifying the concrete rational Albert derivation
algebra with the appropriate rational form of the independently owned F4 root
datum, and then the stronger group statement `Aut(J)=F4`.
-/

namespace Integration.F4AlbertDerivationRecognitionBoundary

open Integration.F4RootWeylExact

structure AlbertDerivationProbeReceipt where
  albertCoordinateDimension : Nat
  basisPairCandidates : Nat
  nonzeroInnerCommutators : Nat
  innerDerivationSpanRank : Nat
  octonionDerivationSpanRank : Nat
  traceFormRank : Nat
  regularCentralizerDimension : Nat
  centerDimension : Nat
  allBasisDerivationChecksPassed : Bool
  negativeTraceFormPositiveDefinite : Bool
  exactTrialitySo8Dimension : Nat
  exactTrialityVectorDimension : Nat
  exactTrialitySpinPlusDimension : Nat
  exactTrialitySpinMinusDimension : Nat
  exactQIZeroWeightDimension : Nat
  exactQINonzeroRootSpaces : Nat
  exactQIRootSpacesOneDimensional : Bool
  exactQIFloatingPointUsed : Bool
  deriving Repr

def canonicalAlbertDerivationProbeReceipt : AlbertDerivationProbeReceipt where
  albertCoordinateDimension := 27
  basisPairCandidates := 351
  nonzeroInnerCommutators := 324
  innerDerivationSpanRank := 52
  octonionDerivationSpanRank := 14
  traceFormRank := 52
  regularCentralizerDimension := 4
  centerDimension := 0
  allBasisDerivationChecksPassed := true
  negativeTraceFormPositiveDefinite := true
  exactTrialitySo8Dimension := 28
  exactTrialityVectorDimension := 8
  exactTrialitySpinPlusDimension := 8
  exactTrialitySpinMinusDimension := 8
  exactQIZeroWeightDimension := 4
  exactQINonzeroRootSpaces := 48
  exactQIRootSpacesOneDimensional := true
  exactQIFloatingPointUsed := false

theorem f4_dimension_checksum :
    canonicalAlbertDerivationProbeReceipt.exactQIZeroWeightDimension +
      canonicalAlbertDerivationProbeReceipt.exactQINonzeroRootSpaces = 52 := by
  decide

theorem triality_dimension_checksum :
    canonicalAlbertDerivationProbeReceipt.exactTrialitySo8Dimension +
      canonicalAlbertDerivationProbeReceipt.exactTrialityVectorDimension +
      canonicalAlbertDerivationProbeReceipt.exactTrialitySpinPlusDimension +
      canonicalAlbertDerivationProbeReceipt.exactTrialitySpinMinusDimension = 52 := by
  decide

theorem independent_f4_root_datum_paid :
    F4RootWeylExact.canonicalBoundary.root48Paid = true ∧
    F4RootWeylExact.canonicalBoundary.standardCartanPaid = true := by
  decide

inductive AlbertDerivationSameLieAlgebraAsF4Paid : Prop
inductive AlbertAutomorphismGroupIdentifiedWithF4Paid : Prop
inductive RationalFormClassifiedHere : Prop

theorem exact_receipts_do_not_manufacture_same_lie_algebra :
    ¬ AlbertDerivationSameLieAlgebraAsF4Paid := by intro h; cases h

theorem exact_receipts_do_not_manufacture_full_automorphism_group :
    ¬ AlbertAutomorphismGroupIdentifiedWithF4Paid := by intro h; cases h

theorem split_root_datum_does_not_classify_rational_form :
    ¬ RationalFormClassifiedHere := by intro h; cases h

structure Boundary where
  independentRoot48Paid : Bool
  independentF4CartanPaid : Bool
  independentF4CoxeterActionPaid : Bool
  weylOrder1152Paid : Bool
  actualRationalAlbertDerivationOperatorOnAgda : Bool
  arbitraryInnerDerivationLawOnAgda : Bool
  exactAlbertDerivationRank52Checked : Bool
  exactTrialityTwentyEightEightEightEightChecked : Bool
  exactTrialityBracketPatternChecked : Bool
  exactCartanVectorSpinSpinChecked : Bool
  exactQIRootDecompositionFourPlusFortyEightChecked : Bool
  floatingRootExtractionSuperseded : Bool
  allConcreteClassificationHypothesesOwnedCrossKernel : Bool
  sameLieAlgebraIntertwinerPaid : Bool
  rationalFormClassificationPaid : Bool
  fullF4AutomorphismRecognitionPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  independentRoot48Paid := true
  independentF4CartanPaid := true
  independentF4CoxeterActionPaid := true
  weylOrder1152Paid := true
  actualRationalAlbertDerivationOperatorOnAgda := true
  arbitraryInnerDerivationLawOnAgda := true
  exactAlbertDerivationRank52Checked := true
  exactTrialityTwentyEightEightEightEightChecked := true
  exactTrialityBracketPatternChecked := true
  exactCartanVectorSpinSpinChecked := true
  exactQIRootDecompositionFourPlusFortyEightChecked := true
  floatingRootExtractionSuperseded := true
  allConcreteClassificationHypothesesOwnedCrossKernel := true
  sameLieAlgebraIntertwinerPaid := false
  rationalFormClassificationPaid := false
  fullF4AutomorphismRecognitionPaid := false

end Integration.F4AlbertDerivationRecognitionBoundary
