import Mathlib
import Integration.JInvariant369JointFibredObserver
import Integration.StageTwelveGrothendieckRelation

namespace Integration.JInvariant369ConsolidatedNextStage

open Integration.StageTwelveGrothendieckRelation
open Integration.JInvariant369JointFibredObserver

/-!
Consolidated finite 369/J next-stage mirror.

The state carries:
* a base point and joint C6 x C27 x SignedMultiplicity fibre;
* a signed relation field on the Stage-12 / 144 carrier;
* an anchor cell whose stalk equals the joint signed multiplicity.

Two independent information-loss theorems are then proved:
* level-27 does not factor through the base/phase/coarse-sign surface;
* magnitude does not factor through a surface retaining level-27 but only
  coarse sign at the anchored relation cell.

Finally, the coarse SSP C3 cycle is known to match level-3 translation, but
there is no lift of that cycle to full SignedMultiplicity that both
intertwines the coarse cycle and preserves magnitude.
-/

structure Consolidated369State (Base : Type) where
  joint : JointLift Base
  relationField : SignedRelationField
  anchorCell : StageRelation144
  anchorAgreesWithJointSigned :
    relationField anchorCell = joint.fibre.signedSSP

def jointSigned {Base : Type} (x : Consolidated369State Base) :
    SignedMultiplicity :=
  x.joint.fibre.signedSSP

def principalLevel27 {Base : Type} (x : Consolidated369State Base) :
    Level27 :=
  x.joint.fibre.level27

def principalLevel3 {Base : Type} (x : Consolidated369State Base) :
    Level3 :=
  (x.joint.fibre.level27.val % 3 : Nat)

def signedCoarseLevel3 {Base : Type} (x : Consolidated369State Base) :
    Level3 :=
  signedMultiplicityToC3 (jointSigned x)

def SignedLevel3Coherent {Base : Type} (x : Consolidated369State Base) : Prop :=
  signedCoarseLevel3 x = principalLevel3 x

structure CoherentConsolidated369State (Base : Type) where
  consolidated : Consolidated369State Base
  coherence : SignedLevel3Coherent consolidated

def translateConsolidated {Base : Type}
    (x : Consolidated369State Base) : Consolidated369State Base where
  joint := translateJointLift x.joint
  relationField := x.relationField
  anchorCell := x.anchorCell
  anchorAgreesWithJointSigned := x.anchorAgreesWithJointSigned

def negateSignedField (field : SignedRelationField) : SignedRelationField :=
  fun cell => negateSignedMultiplicity (field cell)

def reflectJointLiftFibreOnly {Base : Type}
    (x : JointLift Base) : JointLift Base where
  base := x.base
  fibre := reflectJoint x.fibre

def reflectConsolidatedFibreOnly {Base : Type}
    (x : Consolidated369State Base) : Consolidated369State Base where
  joint := reflectJointLiftFibreOnly x.joint
  relationField := negateSignedField x.relationField
  anchorCell := x.anchorCell
  anchorAgreesWithJointSigned := by
    exact congrArg negateSignedMultiplicity x.anchorAgreesWithJointSigned

def anchorRestriction {Base : Type}
    (x : Consolidated369State Base) : SignedMultiplicity :=
  x.relationField x.anchorCell

theorem anchorRestriction_eq_jointSigned {Base : Type}
    (x : Consolidated369State Base) :
    anchorRestriction x = jointSigned x :=
  x.anchorAgreesWithJointSigned

def anchorSign {Base : Type} (x : Consolidated369State Base) : Trit :=
  signedMultiplicityToTrit (anchorRestriction x)

def anchorMagnitude {Base : Type} (x : Consolidated369State Base) : Nat :=
  signedMagnitude (anchorRestriction x)

/-! A coarse base surface forgets principal level. -/

structure ConsolidatedBaseSurface (Base : Type) where
  base : Base
  phase6 : Phase6
  anchorCell : StageRelation144
  anchorSign : Trit
  deriving DecidableEq

def consolidatedBaseObserver {Base : Type}
    (x : Consolidated369State Base) : ConsolidatedBaseSurface Base where
  base := x.joint.base
  phase6 := x.joint.fibre.phase6
  anchorCell := x.anchorCell
  anchorSign := anchorSign x

theorem translationInvisibleToConsolidatedBase {Base : Type}
    (x : Consolidated369State Base) :
    consolidatedBaseObserver (translateConsolidated x)
      = consolidatedBaseObserver x := rfl

def constantSignedField (m : SignedMultiplicity) : SignedRelationField :=
  fun _ => m

def levelWitnessZero {Base : Type}
    (base : Base) (phase : Phase6) (cell : StageRelation144)
    (signed : SignedMultiplicity) : Consolidated369State Base where
  joint := ⟨base, ⟨phase, 0, signed⟩⟩
  relationField := constantSignedField signed
  anchorCell := cell
  anchorAgreesWithJointSigned := rfl

def levelWitnessOne {Base : Type}
    (base : Base) (phase : Phase6) (cell : StageRelation144)
    (signed : SignedMultiplicity) : Consolidated369State Base where
  joint := ⟨base, ⟨phase, 1, signed⟩⟩
  relationField := constantSignedField signed
  anchorCell := cell
  anchorAgreesWithJointSigned := rfl

theorem consolidatedLevel_cannot_factor_through_base
    {Base : Type} (base : Base) (phase : Phase6)
    (cell : StageRelation144) (signed : SignedMultiplicity) :
    ¬ FactorsThrough
      (consolidatedBaseObserver : Consolidated369State Base → ConsolidatedBaseSurface Base)
      principalLevel27 := by
  intro h
  let x0 := levelWitnessZero base phase cell signed
  let x1 := levelWitnessOne base phase cell signed
  have sameSurface : consolidatedBaseObserver x0 = consolidatedBaseObserver x1 := rfl
  have sameLevel :=
    calc
      principalLevel27 x0 = h.factor (consolidatedBaseObserver x0) := h.law x0
      _ = h.factor (consolidatedBaseObserver x1) := by rw [sameSurface]
      _ = principalLevel27 x1 := (h.law x1).symm
  norm_num [x0, x1, principalLevel27] at sameLevel

/-! A richer anchor surface keeps level-27 but still forgets signed magnitude. -/

structure ConsolidatedAnchorSurface (Base : Type) where
  base : Base
  phase6 : Phase6
  level27 : Level27
  anchorCell : StageRelation144
  anchorSign : Trit
  deriving DecidableEq

def consolidatedAnchorObserver {Base : Type}
    (x : Consolidated369State Base) : ConsolidatedAnchorSurface Base where
  base := x.joint.base
  phase6 := x.joint.fibre.phase6
  level27 := x.joint.fibre.level27
  anchorCell := x.anchorCell
  anchorSign := anchorSign x

def positiveState {Base : Type}
    (base : Base) (phase : Phase6) (level : Level27)
    (cell : StageRelation144) (magnitude : Nat) :
    Consolidated369State Base where
  joint := ⟨base, ⟨phase, level, .positive magnitude⟩⟩
  relationField := constantSignedField (.positive magnitude)
  anchorCell := cell
  anchorAgreesWithJointSigned := rfl

theorem consolidatedMagnitude_cannot_factor
    {Base : Type} (base : Base) (phase : Phase6)
    (level : Level27) (cell : StageRelation144) :
    ¬ FactorsThrough
      (consolidatedAnchorObserver : Consolidated369State Base → ConsolidatedAnchorSurface Base)
      anchorMagnitude := by
  intro h
  let x1 := positiveState base phase level cell 1
  let x2 := positiveState base phase level cell 2
  have sameSurface : consolidatedAnchorObserver x1 = consolidatedAnchorObserver x2 := rfl
  have sameMagnitude :=
    calc
      anchorMagnitude x1 = h.factor (consolidatedAnchorObserver x1) := h.law x1
      _ = h.factor (consolidatedAnchorObserver x2) := by rw [sameSurface]
      _ = anchorMagnitude x2 := (h.law x2).symm
  norm_num [x1, x2, anchorMagnitude, anchorRestriction, signedMagnitude] at sameMagnitude

def consolidatedMagnitudeRefinedObserver {Base : Type}
    (x : Consolidated369State Base) :
    ConsolidatedAnchorSurface Base × Nat :=
  (consolidatedAnchorObserver x, anchorMagnitude x)

theorem consolidatedMagnitude_repair_sufficient {Base : Type} :
    ConsumerSufficient
      (consolidatedMagnitudeRefinedObserver : Consolidated369State Base →
        ConsolidatedAnchorSurface Base × Nat)
      anchorMagnitude := by
  intro left right h
  exact congrArg Prod.snd h

/-!
The coarse SSP cycle matches level-3 translation, but there is no fine lift
preserving signed FRACTRAN magnitude.
-/

structure MagnitudePreservingSignedCycleLift where
  lift : SignedMultiplicity → SignedMultiplicity
  coarseCycle :
    ∀ m, signedMultiplicityToC3 (lift m)
      = sspCycle (signedMultiplicityToC3 m)
  preservesMagnitude :
    ∀ m, signedMagnitude (lift m) = signedMagnitude m

theorem noMagnitudePreservingSignedCycleLift :
    ¬ Nonempty MagnitudePreservingSignedCycleLift := by
  rintro ⟨bridge⟩
  have hc := bridge.coarseCycle (.negative 1)
  have hm := bridge.preservesMagnitude (.negative 1)
  cases h : bridge.lift (.negative 1) with
  | negative n =>
      simp [signedMultiplicityToC3, sspCycle, h] at hc
  | zero =>
      simp [signedMagnitude, h] at hm
  | positive n =>
      simp [signedMultiplicityToC3, sspCycle, h] at hc

structure ConsolidatedNextStageBoundary where
  jointFibreAnd144SignedStalkComposed : Bool
  anchorRestrictionEqualsJointSignedCoordinate : Bool
  optionalSignedLevel3CoherenceTyped : Bool
  level27FactorsThroughConsolidatedBase : Bool
  signedMagnitudeFactorsThroughAnchorSurface : Bool
  signedMagnitudeRepairPaid : Bool
  coarseSSPLevel3DihedralEquivalencePaid : Bool
  magnitudePreservingFineCycleLiftExists : Bool
  finiteStage12GrothendieckSiteReused : Bool
  stage12SiteEqualsAnalyticModularSite : Bool
  fibreOnlyReflectionEqualsAnalyticReflection : Bool
  signedFRACTRANArithmeticEqualsModularGeometry : Bool
  deriving Repr

def canonicalBoundary : ConsolidatedNextStageBoundary where
  jointFibreAnd144SignedStalkComposed := true
  anchorRestrictionEqualsJointSignedCoordinate := true
  optionalSignedLevel3CoherenceTyped := true
  level27FactorsThroughConsolidatedBase := false
  signedMagnitudeFactorsThroughAnchorSurface := false
  signedMagnitudeRepairPaid := true
  coarseSSPLevel3DihedralEquivalencePaid := true
  magnitudePreservingFineCycleLiftExists := false
  finiteStage12GrothendieckSiteReused := true
  stage12SiteEqualsAnalyticModularSite := false
  fibreOnlyReflectionEqualsAnalyticReflection := false
  signedFRACTRANArithmeticEqualsModularGeometry := false

end Integration.JInvariant369ConsolidatedNextStage
