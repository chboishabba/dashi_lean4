import Mathlib
import Integration.OggSSPP2ExplicitF2CurveCandidate
import Integration.OggSSPP2SupersingularityCriterionWeld
import Integration.OggSSPP2WittPowerSeriesBase
import Integration.OggSSPP2WittPowerSeriesMixedAdicControl
import Integration.OggSSPP2SupersingularUniversalDeformationSource

/-!
# Concrete F₂ supersingular universal-deformation recognition

The previous source socket intentionally left the residue field, Witt base,
deformation base, and special fibre abstract. On the Lean branch those finite
and algebraic carriers are now concrete:

* residue field: ZMod 2;
* special fibre candidate: y² + y = x³;
* Witt ring: WittVector 2 (ZMod 2);
* deformation carrier: PowerSeries (WittVector 2 (ZMod 2));
* geometric 2-torsion of the candidate: proved trivial;
* maximal-ideal adic completeness of the deformation carrier: proved.

This module packages the remaining SOURCE recognition as one contract:
the external supersingularity criterion and universal-deformation theorem must
identify the source object with these concrete carriers.

No field of this contract is fabricated from a count or from the existing
finite ten-state target.
-/

namespace Integration.OggSSPP2ConcreteF2UniversalDeformationRecognition

namespace Candidate := Integration.OggSSPP2ExplicitF2CurveCandidate
namespace Criterion := Integration.OggSSPP2SupersingularityCriterionWeld
namespace Base := Integration.OggSSPP2WittPowerSeriesBase
namespace Mixed := Integration.OggSSPP2WittPowerSeriesMixedAdicControl
namespace Universal := Integration.OggSSPP2SupersingularUniversalDeformationSource

structure ConcreteF2UniversalDeformationAuthority where
  supersingularityMeaning : Criterion.SourceSupersingularityMeaning

  supersingularityCriterion :
    Criterion.SupersingularityCriterionAuthority supersingularityMeaning

  specialFibreIsExplicitCandidate : Prop
  specialFibreIsExplicitCandidateProof :
    specialFibreIsExplicitCandidate

  completeLocalBaseIsSourceBase : Prop
  completeLocalBaseIsSourceBaseProof :
    completeLocalBaseIsSourceBase

  EllipticFamilyState : Type

  oneParameterUniversalDeformation : Prop
  oneParameterUniversalDeformationProof :
    oneParameterUniversalDeformation

  universalProperty : Prop
  universalPropertyProof :
    universalProperty

  sourceTitle : String
  sourceLocator : String

theorem explicit_candidate_supersingular
    (authority : ConcreteF2UniversalDeformationAuthority) :
    authority.supersingularityMeaning.supersingular :=
  Criterion.explicit_candidate_satisfies_source_supersingularity
    authority.supersingularityCriterion

def concreteSourceDatum
    (authority : ConcreteF2UniversalDeformationAuthority) :
    Universal.SupersingularUniversalDeformationDatum where
  ResidueField := Base.P2ResidueField
  WittBase := Base.P2WittRing
  FormalParameter := Base.P2WittPowerSeriesBase
  DeformationBase := Base.P2WittPowerSeriesBase
  EllipticFamilyState := authority.EllipticFamilyState

  characteristic := 2
  characteristicIsTwo := rfl

  oneFormalParameter := authority.oneParameterUniversalDeformation
  completeLocalWittPowerSeriesShape := authority.completeLocalBaseIsSourceBase
  supersingularSpecialFibre := authority.supersingularityMeaning.supersingular
  universalPropertyImportedFromSource := authority.universalProperty

  sourceReference := authority.sourceTitle ++ " — " ++ authority.sourceLocator

theorem concrete_source_supersingular_special_fibre
    (authority : ConcreteF2UniversalDeformationAuthority) :
    (concreteSourceDatum authority).supersingularSpecialFibre :=
  explicit_candidate_supersingular authority

theorem concrete_source_one_parameter
    (authority : ConcreteF2UniversalDeformationAuthority) :
    (concreteSourceDatum authority).oneFormalParameter :=
  authority.oneParameterUniversalDeformationProof

theorem concrete_source_complete_local_shape
    (authority : ConcreteF2UniversalDeformationAuthority) :
    (concreteSourceDatum authority).completeLocalWittPowerSeriesShape :=
  authority.completeLocalBaseIsSourceBaseProof

theorem concrete_source_universal_property
    (authority : ConcreteF2UniversalDeformationAuthority) :
    (concreteSourceDatum authority).universalPropertyImportedFromSource :=
  authority.universalPropertyProof

theorem concrete_source_residue_field_is_F2
    (authority : ConcreteF2UniversalDeformationAuthority) :
    (concreteSourceDatum authority).ResidueField = Base.P2ResidueField :=
  rfl

theorem concrete_source_witt_base_is_paid_witt_ring
    (authority : ConcreteF2UniversalDeformationAuthority) :
    (concreteSourceDatum authority).WittBase = Base.P2WittRing :=
  rfl

theorem concrete_source_deformation_base_is_paid_power_series
    (authority : ConcreteF2UniversalDeformationAuthority) :
    (concreteSourceDatum authority).DeformationBase =
      Base.P2WittPowerSeriesBase :=
  rfl

noncomputable def concrete_deformation_base_adically_complete :
    IsAdicComplete
      (IsLocalRing.maximalIdeal Base.P2WittPowerSeriesBase)
      Base.P2WittPowerSeriesBase :=
  Mixed.powerSeriesMaximalIdealAdicallyComplete

inductive Residual
  | missingConcreteF2UniversalDeformationAuthority
  | missingGamma0FourMarkedDeformationStates
  | missingTenStateClassificationBidi
  deriving DecidableEq, Repr

def firstResidual : Residual :=
  .missingConcreteF2UniversalDeformationAuthority

structure Boundary where
  explicitF2CurveCandidateReused : Bool
  geometricTwoTorsionTheoremReused : Bool
  maximalIdealAdicCompleteBaseReused : Bool
  residueFieldFixedDefinitionallyToF2 : Bool
  wittBaseFixedDefinitionally : Bool
  deformationBaseFixedDefinitionally : Bool
  separateResidueFieldDescentCodecRequiredAfterRecognition : Bool
  sourceAuthorityInhabitedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  explicitF2CurveCandidateReused := true
  geometricTwoTorsionTheoremReused := true
  maximalIdealAdicCompleteBaseReused := true
  residueFieldFixedDefinitionallyToF2 := true
  wittBaseFixedDefinitionally := true
  deformationBaseFixedDefinitionally := true
  separateResidueFieldDescentCodecRequiredAfterRecognition := false
  sourceAuthorityInhabitedHere := false

end Integration.OggSSPP2ConcreteF2UniversalDeformationRecognition
