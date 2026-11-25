import Integration.F4RootWeylExact
import Integration.F4TrialityRootDatum
import Integration.F4AlbertDerivationRecognitionBoundary
import Integration.AlbertRationalF4DerivationReceipt
import Integration.E8StructuredFullWeylRecognition
import Mathlib

/-!
# F4 / Albert current max-cut

Companion Agda owns the actual rational Albert algebra `H_3(O_Q)`, arbitrary
inner-derivation law, a typed same-carrier linear Jordan-automorphism carrier,
explicit coordinate/signed-basis/Moufang-triality automorphisms, and the
classical E6/F4 source receipts.

The exact companion algebra has now passed the discovery stage completely:

* inner-derivation dimension `52`;
* triality split `28 + 8_v + 8_s + 8_c` with exact bracket pattern;
* four explicit commuting Cartan derivations;
* exact vector and two chiral half-spin roles;
* symbolic projector decomposition over `Q(i)` with zero-weight rank `4` and
  `48` one-dimensional nonzero root spaces, split `24 + 8 + 8 + 8`;
* exact root grading across all `1128` unordered root pairs:
  `408` root-sum nonzero brackets, `24` opposite-root Cartan brackets, and
  `696` forbidden-sum zero brackets;
* no floating-point eigensolver in these upgraded certificates.

This Lean branch independently owns the standard F4 root datum and reflection
image: `48` roots, rank four, standard Cartan/Coxeter relations, Weyl order
`1152`.

Therefore the active seam is no longer a local root-space or Lie-bracket search.
All concrete hypotheses for the classical characteristic-zero Albert
classification are present. What remains formal-open is the GENERAL theorem
(or formal import thereof) identifying the rational derivation Lie algebra and
`Aut(J)` with the appropriate form of type F4, and the cubic symmetry group with
type E6. No statement below infers that theorem merely from dimensions.
-/

namespace Integration.F4AlbertCurrentMaxCut

open Integration.F4RootWeylExact
open Integration.F4AlbertDerivationRecognitionBoundary

structure Boundary where
  structuredE8AlreadyPaid : Bool
  abstractF4Root48Paid : Bool
  abstractF4CartanPaid : Bool
  abstractF4CoxeterPaid : Bool
  abstractF4WeylOrder1152Paid : Bool
  AlbertJordanAlgebraOnCompanionAgda : Bool
  typedLinearJordanAutomorphismCarrierOnCompanionAgda : Bool
  arbitraryAlbertInnerDerivationLawOnCompanionAgda : Bool
  exactDerivationRank52Paid : Bool
  exactTrialityTwentyEightEightEightEightPaid : Bool
  exactTrialityBracketPatternPaid : Bool
  exactCartanVectorSpinSpinPaid : Bool
  exactQIRootSpacesFourPlusFortyEightPaid : Bool
  exactRootGradingAll1128PairsPaid : Bool
  floatingRootExtractionSuperseded : Bool
  allConcreteClassificationHypothesesOwned : Bool
  classificationReducedToGeneralExternalTheorem : Bool
  generalExceptionalClassificationFormalizedHere : Bool
  formalDerAlbertTypeF4InstantiationPaid : Bool
  fullAutAlbertEqualsF4Paid : Bool
  fullCubicSymmetryEqualsE6Paid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  structuredE8AlreadyPaid := true
  abstractF4Root48Paid := true
  abstractF4CartanPaid := true
  abstractF4CoxeterPaid := true
  abstractF4WeylOrder1152Paid := true
  AlbertJordanAlgebraOnCompanionAgda := true
  typedLinearJordanAutomorphismCarrierOnCompanionAgda := true
  arbitraryAlbertInnerDerivationLawOnCompanionAgda := true
  exactDerivationRank52Paid := true
  exactTrialityTwentyEightEightEightEightPaid := true
  exactTrialityBracketPatternPaid := true
  exactCartanVectorSpinSpinPaid := true
  exactQIRootSpacesFourPlusFortyEightPaid := true
  exactRootGradingAll1128PairsPaid := true
  floatingRootExtractionSuperseded := true
  allConcreteClassificationHypothesesOwned := true
  classificationReducedToGeneralExternalTheorem := true
  generalExceptionalClassificationFormalizedHere := false
  formalDerAlbertTypeF4InstantiationPaid := false
  fullAutAlbertEqualsF4Paid := false
  fullCubicSymmetryEqualsE6Paid := false

end Integration.F4AlbertCurrentMaxCut
