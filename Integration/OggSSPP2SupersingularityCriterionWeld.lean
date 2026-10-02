import Mathlib
import Integration.OggSSPP2ExplicitF2CurveCandidate

/-!
# Supersingularity criterion weld for the explicit p=2 curve candidate

External mathematical source:
John Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288,
Springer, 2021, Proposition 42.1.7 (citing Silverman, Arithmetic of Elliptic
Curves, V.3.1):

For an elliptic curve E over a field of characteristic p > 0,

  E is supersingular  <->  E[p](k^alg) = {0}.

This file does NOT define supersingularity to mean trivial geometric p-torsion.
Instead it exposes the source theorem as a semantic authority contract and
proves that the already-owned geometric two-torsion theorem discharges the
right-hand side for the explicit curve y^2 + y = x^3 over F2.

No authority contract is inhabited internally here.
-/

namespace Integration.OggSSPP2SupersingularityCriterionWeld

namespace Candidate := Integration.OggSSPP2ExplicitF2CurveCandidate

structure SourceSupersingularityMeaning where
  supersingular : Prop

structure SupersingularityCriterionAuthority
    (meaning : SourceSupersingularityMeaning) where
  criterion :
    meaning.supersingular ↔ Candidate.GeometricTwoTorsionTrivial

  sourceTitle : String
  sourceLocator : String

theorem explicit_candidate_satisfies_source_supersingularity
    {meaning : SourceSupersingularityMeaning}
    (authority : SupersingularityCriterionAuthority meaning) :
    meaning.supersingular :=
  authority.criterion.mpr Candidate.geometric_two_torsion_trivial

structure CandidateSupersingularityRecognition where
  meaning : SourceSupersingularityMeaning
  authority : SupersingularityCriterionAuthority meaning
  recognized : meaning.supersingular

def recognizeCandidate
    {meaning : SourceSupersingularityMeaning}
    (authority : SupersingularityCriterionAuthority meaning) :
    CandidateSupersingularityRecognition where
  meaning := meaning
  authority := authority
  recognized :=
    explicit_candidate_satisfies_source_supersingularity authority

structure Boundary where
  explicitCurveGeometricTwoTorsionTrivial : Bool
  externalCriterionRecorded : Bool
  criterionDefinedCircularlyInsideRepo : Bool
  authorityContractInhabitedInternally : Bool
  conditionalCandidateRecognitionPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  explicitCurveGeometricTwoTorsionTrivial := true
  externalCriterionRecorded := true
  criterionDefinedCircularlyInsideRepo := false
  authorityContractInhabitedInternally := false
  conditionalCandidateRecognitionPaid := true

end Integration.OggSSPP2SupersingularityCriterionWeld
