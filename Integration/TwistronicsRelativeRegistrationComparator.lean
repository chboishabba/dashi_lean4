import Mathlib
import Integration.NonginOnePointOneArmyRefinement

/-!
# Twistronics relative-registration comparator

Attribution-safe Lean mirror of the generic abstraction introduced on the
J/369 cross-pollination branch.

External physics provenance:
* R. Bistritzer and A. H. MacDonald,
  "Moiré bands in twisted double-layer graphene",
  PNAS 108(30), 12233-12237 (2011), DOI 10.1073/pnas.1108174108.
* Y. Cao et al.,
  "Correlated insulator behaviour at half-filling in magic-angle graphene
  superlattices", Nature 556, 80-84 (2018), DOI 10.1038/nature26154.
* Y. Cao et al.,
  "Unconventional superconductivity in magic-angle graphene superlattices",
  Nature 556, 43-50 (2018), DOI 10.1038/nature26160.

The theorem below is repository-owned.  It abstracts only the structural
pattern

  same microscopic carrier + relative registration -> effective observation.

It makes no identification of a moiré cell, twist angle, or graphene band with
SSP15, Base369, an Ogg lane, or a j-invariant fibre.
-/

namespace Integration.TwistronicsRelativeRegistrationComparator

inductive ClaimOrigin
  | externalTwistronicsTheory
  | externalTwistronicsExperiment
  | repositoryFormalAbstraction
  | repositoryCrossDomainComparator
  | forbiddenSameObjectPromotion
  deriving DecidableEq, Repr

def moireMagicAngleOrigin : ClaimOrigin := .externalTwistronicsTheory
def correlatedPhaseOrigin : ClaimOrigin := .externalTwistronicsExperiment
def relativeRegistrationAbstractionOrigin : ClaimOrigin :=
  .repositoryFormalAbstraction
def codecFibreComparatorOrigin : ClaimOrigin :=
  .repositoryCrossDomainComparator

structure OverlayState (Microscopic Registration : Type) where
  leftMicroscopic : Microscopic
  rightMicroscopic : Microscopic
  relativeRegistration : Registration
  deriving Repr

structure RelativeRegistrationSystem
    (Microscopic Registration Effective : Type) where
  observeEffective : OverlayState Microscopic Registration → Effective

def changeRegistration
    {Microscopic Registration : Type}
    (state : OverlayState Microscopic Registration)
    (registration : Registration) :
    OverlayState Microscopic Registration :=
  { state with relativeRegistration := registration }

theorem changeRegistration_preserves_left
    {Microscopic Registration : Type}
    (state : OverlayState Microscopic Registration)
    (registration : Registration) :
    (changeRegistration state registration).leftMicroscopic =
      state.leftMicroscopic := rfl

theorem changeRegistration_preserves_right
    {Microscopic Registration : Type}
    (state : OverlayState Microscopic Registration)
    (registration : Registration) :
    (changeRegistration state registration).rightMicroscopic =
      state.rightMicroscopic := rfl

structure RegistrationSensitiveWitness
    {Microscopic Registration Effective : Type}
    (system :
      RelativeRegistrationSystem Microscopic Registration Effective) where
  microscopic : Microscopic
  firstRegistration : Registration
  secondRegistration : Registration
  effectiveChanges :
    system.observeEffective
      ⟨microscopic, microscopic, firstRegistration⟩ ≠
    system.observeEffective
      ⟨microscopic, microscopic, secondRegistration⟩

theorem relativeRegistration_can_change_effective_observation
    {Microscopic Registration Effective : Type}
    (system :
      RelativeRegistrationSystem Microscopic Registration Effective)
    (witness : RegistrationSensitiveWitness system) :
    system.observeEffective
      ⟨witness.microscopic, witness.microscopic,
        witness.firstRegistration⟩ ≠
    system.observeEffective
      ⟨witness.microscopic, witness.microscopic,
        witness.secondRegistration⟩ :=
  witness.effectiveChanges

structure TwistronicsComparatorBoundary where
  primaryTheoryAttributed : Bool
  primaryExperimentsAttributed : Bool
  genericRegistrationCarrierRepositoryOwned : Bool
  registrationSensitivityRequiresWitness : Bool
  moireCellIdentifiedWithSSP15 : Bool
  twistAngleIdentifiedWithBase369Digit : Bool
  grapheneBandIdentifiedWithJInvariantFibre : Bool
  twistronicsProvesOggRecognition : Bool
  crossDomainSameObjectPromotionMade : Bool
  deriving Repr

def canonicalBoundary : TwistronicsComparatorBoundary where
  primaryTheoryAttributed := true
  primaryExperimentsAttributed := true
  genericRegistrationCarrierRepositoryOwned := true
  registrationSensitivityRequiresWitness := true
  moireCellIdentifiedWithSSP15 := false
  twistAngleIdentifiedWithBase369Digit := false
  grapheneBandIdentifiedWithJInvariantFibre := false
  twistronicsProvesOggRecognition := false
  crossDomainSameObjectPromotionMade := false

end Integration.TwistronicsRelativeRegistrationComparator


namespace OnePointOneCrossPollination

/-!
The repo uses "1.1" in several non-identical roles.  This mirror makes the
collision firewall explicit instead of treating a shared printed number as a
same-object theorem.
-/

inductive OnePointOneRole
  | twistronicsApproximateAngleRole
  | exactTenPercentScalarRole
  | metacognitiveFrameCoordinateRole
  | decimalFineRefinementRole
  deriving DecidableEq, Repr

theorem twistronics_role_ne_scalar :
    OnePointOneRole.twistronicsApproximateAngleRole ≠
      OnePointOneRole.exactTenPercentScalarRole := by
  decide

theorem twistronics_role_ne_meta :
    OnePointOneRole.twistronicsApproximateAngleRole ≠
      OnePointOneRole.metacognitiveFrameCoordinateRole := by
  decide

theorem scalar_role_ne_meta :
    OnePointOneRole.exactTenPercentScalarRole ≠
      OnePointOneRole.metacognitiveFrameCoordinateRole := by
  decide

theorem three_axis_ten_percent_gain_numerator :
    11 ^ 3 = 1331 := by norm_num

theorem three_axis_ten_percent_gain_denominator :
    10 ^ 3 = 1000 := by norm_num

structure OnePointOneCrossPollinationBoundary where
  exactElevenTenthsArithmeticMirrored : Bool
  metacognitiveOnePointOneTreatedAsScalar : Bool
  approximateMagicAngleEqualsExactElevenTenths : Bool
  equalPrintedTokenImpliesEqualRole : Bool
  exactTenPercentGainExplainsMagicAnglePhysics : Bool
  deriving Repr

def canonicalBoundary : OnePointOneCrossPollinationBoundary where
  exactElevenTenthsArithmeticMirrored := true
  metacognitiveOnePointOneTreatedAsScalar := false
  approximateMagicAngleEqualsExactElevenTenths := false
  equalPrintedTokenImpliesEqualRole := false
  exactTenPercentGainExplainsMagicAnglePhysics := false

end OnePointOneCrossPollination


namespace RegistrationRefinement

structure RegistrationSensitiveWitness
    {Microscopic Registration Effective : Type}
    (observeEffective :
      Integration.TwistronicsRelativeRegistrationComparator.OverlayState
        Microscopic Registration → Effective) where
  microscopic : Microscopic
  firstRegistration : Registration
  secondRegistration : Registration
  effectiveChanges :
    observeEffective
      ⟨microscopic, microscopic, firstRegistration⟩ ≠
    observeEffective
      ⟨microscopic, microscopic, secondRegistration⟩

def forgetRegistration
    {Microscopic Registration : Type} :
    Integration.TwistronicsRelativeRegistrationComparator.OverlayState
      Microscopic Registration →
    Microscopic × Microscopic
  | ⟨left, right, _⟩ => (left, right)

theorem registration_sensitive_implies_distinct
    {Microscopic Registration Effective : Type}
    {observeEffective :
      Integration.TwistronicsRelativeRegistrationComparator.OverlayState
        Microscopic Registration → Effective}
    (w : RegistrationSensitiveWitness observeEffective) :
    w.firstRegistration ≠ w.secondRegistration := by
  intro h
  apply w.effectiveChanges
  cases h
  rfl

theorem coarse_pair_not_injective
    {Microscopic Registration Effective : Type}
    {observeEffective :
      Integration.TwistronicsRelativeRegistrationComparator.OverlayState
        Microscopic Registration → Effective}
    (w : RegistrationSensitiveWitness observeEffective) :
    ¬ Function.Injective
      (forgetRegistration :
        Integration.TwistronicsRelativeRegistrationComparator.OverlayState
          Microscopic Registration →
        Microscopic × Microscopic) := by
  intro h
  have sameState :
      (⟨w.microscopic, w.microscopic, w.firstRegistration⟩ :
        Integration.TwistronicsRelativeRegistrationComparator.OverlayState
          Microscopic Registration) =
      ⟨w.microscopic, w.microscopic, w.secondRegistration⟩ :=
    h rfl
  exact registration_sensitive_implies_distinct w
    (congrArg
      Integration.TwistronicsRelativeRegistrationComparator.OverlayState.relativeRegistration
      sameState)

theorem no_effective_factorization_through_coarse_pair
    {Microscopic Registration Effective : Type}
    {observeEffective :
      Integration.TwistronicsRelativeRegistrationComparator.OverlayState
        Microscopic Registration → Effective}
    (w : RegistrationSensitiveWitness observeEffective) :
    ¬ ∃ coarseObserve : (Microscopic × Microscopic) → Effective,
      ∀ state, observeEffective state = coarseObserve (forgetRegistration state) := by
  rintro ⟨coarseObserve, h⟩
  have left := h
    (⟨w.microscopic, w.microscopic, w.firstRegistration⟩ :
      Integration.TwistronicsRelativeRegistrationComparator.OverlayState
        Microscopic Registration)
  have right := h
    (⟨w.microscopic, w.microscopic, w.secondRegistration⟩ :
      Integration.TwistronicsRelativeRegistrationComparator.OverlayState
        Microscopic Registration)
  exact w.effectiveChanges (left.trans right.symm)

structure NonginTwistronicsRefinementBoundary where
  nonginUsesStrictRefinementShape : Bool
  twistronicsUsesStrictRefinementShape : Bool
  bothNeedConsumerSeparationWitness : Bool
  sharedShapeImpliesSharedMechanism : Bool
  frameCoordinateIsTwistAngle : Bool
  onePointOneExplainsMagicAngleValue : Bool
  deriving Repr

def canonicalBoundary : NonginTwistronicsRefinementBoundary where
  nonginUsesStrictRefinementShape := true
  twistronicsUsesStrictRefinementShape := true
  bothNeedConsumerSeparationWitness := true
  sharedShapeImpliesSharedMechanism := false
  frameCoordinateIsTwistAngle := false
  onePointOneExplainsMagicAngleValue := false

end RegistrationRefinement


namespace PhysicalMeaning

structure TwistronicsPhysicalMeaningReceipt where
  momentumSeparationFormula : String
  dimensionlessCouplingParameter : String
  firstMagicAngleStatement : String
  physicalInterpretation : String
  relativeGeometryEntersEffectiveHamiltonian : Bool
  coherentInterlayerInterferenceRelevant : Bool
  effectiveLowEnergyCarrierCanChangeWithRegistration : Bool
  microscopicCarbonAlphabetChangedByTwist : Bool
  literalTenPercentGainIsPhysicalMechanism : Bool
  nonginFrameCoordinateIsPhysicalTwistAngle : Bool
  deriving Repr

def canonicalReceipt : TwistronicsPhysicalMeaningReceipt where
  momentumSeparationFormula := "k_theta = 2 k_D sin(theta/2)"
  dimensionlessCouplingParameter := "alpha = w / (v k_theta)"
  firstMagicAngleStatement :=
    "Bistritzer--MacDonald continuum model: first Dirac-velocity zero near theta approximately 1.05 degrees for w = 110 meV"
  physicalInterpretation :=
    "relative geometry changes momentum separation and coherent interlayer tunnelling/interference in the effective Hamiltonian; special coupling ratios can flatten the low-energy moire band"
  relativeGeometryEntersEffectiveHamiltonian := true
  coherentInterlayerInterferenceRelevant := true
  effectiveLowEnergyCarrierCanChangeWithRegistration := true
  microscopicCarbonAlphabetChangedByTwist := false
  literalTenPercentGainIsPhysicalMechanism := false
  nonginFrameCoordinateIsPhysicalTwistAngle := false

end PhysicalMeaning
