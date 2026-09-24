import Mathlib

/-!
# Lean mirrors of the two DASHI non-factorability kernels, and three of their consumers

Two modules of the Agda corpus independently define *the same* record pair — a
factorisation of a consumer through a projection, and a witness that refutes
it — under different names and in different vocabularies:

* `Agda/DASHI/Core/IntersectionalNonFactorability.agda`
  (`FactorsThrough` / `NonFactorabilityWitness`);
* `Agda/DASHI/Core/ReopenableConsumerInterventionKernelExact.agda` §1
  (`ConsumerDescent` / `ConsumerDescentDefect`).

This file transcribes both, faithfully, together with three concrete corpus
surfaces that use them:

* `Agda/DASHI/Core/SocioEcologicalFeedbackExact.agda` — a declared static plan
  score against a reactive realised outcome;
* `Agda/DASHI/Education/EarlyLearningIntersectionalCapabilityExact.agda` — a
  situated ten-coordinate position, a flat public label, and a retained
  capability coordinate;
* `Agda/DASHI/Education/EarlyLearningMultiOutcomeVectorExact.agda` — a
  five-axis outcome vector, its axis projections, and the whole-policy verdict
  carrier with its explicit aggregation rule.

**Transcription boundary.**  The Agda originals put the two `…Through` /
`…Descent` records in `Set₁` because they quantify over a function between
`Set`s; the Lean transcriptions put them in `Type`, which is the same statement
with different universe bookkeeping.  `⊥` is transcribed as `False`, `_≡_` as
`Eq`, and `data … : Set where` with no constructors as an empty `inductive`.
No Agda typechecker was run in this environment: these are Lean statements
about Lean definitions that transcribe Agda text, not evidence about the Agda
files.

Nothing here is a claim about people, policy, institutions, ecology or
education.  Every carrier is a finite label type or a record of finite label
types, and the theorems are about functions between them.
-/

namespace AgdaMirror.NonFactorabilityKernels

/-! ## Kernel 1: `DASHI.Core.IntersectionalNonFactorability` -/

namespace Intersectional

/-- Mirror of `FactorsThrough`: the phenomenon is a reading of the flat
projection. -/
structure FactorsThrough {Situated Flat Outcome : Type} (flatten : Situated → Flat)
    (phenomenon : Situated → Outcome) where
  /-- The reading of the flat carrier. -/
  interpretFlat : Flat → Outcome
  /-- It reproduces the phenomenon everywhere. -/
  factorisation : ∀ state, phenomenon state = interpretFlat (flatten state)

/-- Mirror of `NonFactorabilityWitness`. -/
structure NonFactorabilityWitness {Situated Flat Outcome : Type} (flatten : Situated → Flat)
    (phenomenon : Situated → Outcome) where
  /-- The first situated state. -/
  left : Situated
  /-- The second situated state. -/
  right : Situated
  /-- The flat carrier does not tell them apart. -/
  sameFlatProjection : flatten left = flatten right
  /-- The phenomenon does. -/
  situatedOutcomesDiffer : phenomenon left = phenomenon right → False

/-- Mirror of `witnessRulesOutEveryFlatFactorisation`. -/
theorem witnessRulesOutEveryFlatFactorisation {Situated Flat Outcome : Type}
    {flatten : Situated → Flat} {phenomenon : Situated → Outcome}
    (witness : NonFactorabilityWitness flatten phenomenon)
    (factor : FactorsThrough flatten phenomenon) : False :=
  witness.situatedOutcomesDiffer <| by
    rw [factor.factorisation witness.left, factor.factorisation witness.right,
      witness.sameFlatProjection]

/-- Mirror of `SituatedState`. -/
inductive SituatedState
  | sameLabelLowPower | sameLabelHighPower
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `FlatSingleAxis`. -/
inductive FlatSingleAxis
  | sameDemographicLabel
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `flatProjection`. -/
def flatProjection : SituatedState → FlatSingleAxis
  | _ => .sameDemographicLabel

/-- Mirror of `relationalOutcome`. -/
def relationalOutcome : SituatedState → Bool
  | .sameLabelLowPower => false
  | .sameLabelHighPower => true

/-- Mirror of `canonicalIntersectionalNonFactorability`. -/
def canonicalIntersectionalNonFactorability :
    NonFactorabilityWitness flatProjection relationalOutcome where
  left := .sameLabelLowPower
  right := .sameLabelHighPower
  sameFlatProjection := rfl
  situatedOutcomesDiffer := by decide

/-- Mirror of `flatReweightingCannotRepairMissingRelation`. -/
theorem flatReweightingCannotRepairMissingRelation
    (factor : FactorsThrough flatProjection relationalOutcome) : False :=
  witnessRulesOutEveryFlatFactorisation canonicalIntersectionalNonFactorability factor

/-- Mirror of the empty type
`SeparateAxisSufficiencyImpliesIntersectionalSufficiencyPermission`.  The Agda
module states the no-auto-promotion boundary by declaring a type with no
constructors; the transcription keeps that exactly. -/
inductive SeparateAxisSufficiencyImpliesIntersectionalSufficiencyPermission : Type

/-- Mirror of `separateAxisSufficiencyCannotAutoPromote`. -/
theorem separateAxisSufficiencyCannotAutoPromote
    (h : SeparateAxisSufficiencyImpliesIntersectionalSufficiencyPermission) : False :=
  nomatch h

end Intersectional

/-! ## Kernel 2: `DASHI.Core.ReopenableConsumerInterventionKernelExact` §1 -/

namespace ConsumerKernel

/-- Mirror of `ConsumerDescent`. -/
structure ConsumerDescent {Fine Coarse Output : Type} (project : Fine → Coarse)
    (consume : Fine → Output) where
  /-- The consumer as read off the coarse carrier. -/
  quotientConsumer : Coarse → Output
  /-- It reproduces the fine consumer everywhere. -/
  factorises : ∀ fine, consume fine = quotientConsumer (project fine)

/-- Mirror of `ConsumerDescentDefect`. -/
structure ConsumerDescentDefect {Fine Coarse Output : Type} (project : Fine → Coarse)
    (consume : Fine → Output) where
  /-- The first fine state. -/
  left : Fine
  /-- The second fine state. -/
  right : Fine
  /-- The coarse carrier identifies them. -/
  sameProjection : project left = project right
  /-- The consumer separates them. -/
  consumerDistinguishes : consume left = consume right → False

/-- Mirror of `consumerDescentDefectContradictsDescent`. -/
theorem consumerDescentDefectContradictsDescent {Fine Coarse Output : Type}
    {project : Fine → Coarse} {consume : Fine → Output}
    (descent : ConsumerDescent project consume)
    (defect : ConsumerDescentDefect project consume) : False :=
  defect.consumerDistinguishes <| by
    rw [descent.factorises defect.left, descent.factorises defect.right,
      defect.sameProjection]

end ConsumerKernel

/-! ## Consumer 1: `DASHI.Core.SocioEcologicalFeedbackExact` -/

namespace SocioEcologicalFeedback

open ConsumerKernel

/-- Mirror of `ActorDisposition`. -/
inductive ActorDisposition
  | cooperate | resist
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `Intervention`. -/
inductive Intervention
  | voluntaryBuffer
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `StaticPlanScore`. -/
inductive StaticPlanScore
  | sameDeclaredCost
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `World`. -/
inductive World
  | cooperativeWorld | resistantWorld
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `Outcome`. -/
inductive Outcome
  | implemented | blocked
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `actorOf`. -/
def actorOf : World → ActorDisposition
  | .cooperativeWorld => .cooperate
  | .resistantWorld => .resist

/-- Mirror of `staticScore`: the declared-cost observation, constant. -/
def staticScore : World → StaticPlanScore
  | _ => .sameDeclaredCost

/-- Mirror of `react`: the realised outcome of an intervention in a world. -/
def react : Intervention → World → Outcome
  | .voluntaryBuffer, .cooperativeWorld => .implemented
  | .voluntaryBuffer, .resistantWorld => .blocked

/-- Mirror of `staticScoreCollision`. -/
theorem staticScoreCollision :
    staticScore .cooperativeWorld = staticScore .resistantWorld := rfl

/-- Mirror of `staticPlanScoreCannotDetermineReactiveOutcome`. -/
def staticPlanScoreCannotDetermineReactiveOutcome :
    ConsumerDescentDefect staticScore (react .voluntaryBuffer) where
  left := .cooperativeWorld
  right := .resistantWorld
  sameProjection := rfl
  consumerDistinguishes := by decide

/-- Mirror of `ReactiveAgentSystem`: an agent-state carrier whose response
reproduces the world's reaction. -/
structure ReactiveAgentSystem where
  /-- The agent-state carrier. -/
  AgentState : Type
  /-- What the system observes of the world. -/
  observeActor : World → AgentState
  /-- How it responds. -/
  respond : Intervention → AgentState → Outcome
  /-- The response agrees with the world's reaction. -/
  responseMatchesWorld :
    ∀ intervention world, respond intervention (observeActor world) = react intervention world

/-- Mirror of `canonicalReactiveAgentSystem`: the actor disposition is enough. -/
def canonicalReactiveAgentSystem : ReactiveAgentSystem where
  AgentState := ActorDisposition
  observeActor := actorOf
  respond := fun _ a => match a with | .cooperate => .implemented | .resist => .blocked
  responseMatchesWorld := by decide

end SocioEcologicalFeedback

/-! ## Consumer 2: `DASHI.Education.EarlyLearningIntersectionalCapabilityExact` -/

namespace SituatedCapability

open Intersectional

/-- Mirror of `ChildPosition`. -/
inductive ChildPosition | childPositionA | childPositionB
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `CaregiverPosition`. -/
inductive CaregiverPosition | caregiverPositionA | caregiverPositionB
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `HouseholdPosition`. -/
inductive HouseholdPosition | householdPositionA | householdPositionB
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `PlacePosition`. -/
inductive PlacePosition | urban | regional | remote
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `LabourPosition`. -/
inductive LabourPosition | secureFlexible | precariousTimePoor
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `AccessPosition`. -/
inductive AccessPosition | ordinaryAccess | specialistAccessRequired
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `CultureLanguagePosition`. -/
inductive CultureLanguagePosition | dominantLanguage | multilingualOrCommunityLanguage
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `GenderedCarePosition`. -/
inductive GenderedCarePosition | lowerCareBurden | higherCareBurden
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `CommunityAuthorityPosition`. -/
inductive CommunityAuthorityPosition | nuclearHouseholdOnly | kinCommunityGoverned
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `InstitutionalRelation`. -/
inductive InstitutionalRelation
  | institutionTrusted | institutionMixed | institutionHistoricallyUnsafe
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `SituatedEarlyLearningPosition`: ten independently visible
coordinates. -/
structure SituatedEarlyLearningPosition where
  /-- Child coordinate. -/
  child : ChildPosition
  /-- Caregiver coordinate. -/
  caregiver : CaregiverPosition
  /-- Household coordinate. -/
  household : HouseholdPosition
  /-- Place coordinate. -/
  place : PlacePosition
  /-- Labour coordinate. -/
  labour : LabourPosition
  /-- Access coordinate. -/
  access : AccessPosition
  /-- Culture/language coordinate. -/
  cultureLanguage : CultureLanguagePosition
  /-- Gendered-care coordinate. -/
  genderedCare : GenderedCarePosition
  /-- Community-authority coordinate. -/
  communityAuthority : CommunityAuthorityPosition
  /-- Institutional-relation coordinate. -/
  institutionalRelation : InstitutionalRelation
  deriving DecidableEq

/-- Mirror of `PublicFamilyChoiceLabel`. -/
inductive PublicFamilyChoiceLabel | sameFormalFamilyChoice
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `familyChoiceProjection`: the flat public label. -/
def familyChoiceProjection : SituatedEarlyLearningPosition → PublicFamilyChoiceLabel
  | _ => .sameFormalFamilyChoice

/-- Mirror of `lowReachabilityPosition`. -/
def lowReachabilityPosition : SituatedEarlyLearningPosition :=
  ⟨.childPositionA, .caregiverPositionA, .householdPositionA, .urban,
    .precariousTimePoor, .specialistAccessRequired, .multilingualOrCommunityLanguage,
    .higherCareBurden, .nuclearHouseholdOnly, .institutionMixed⟩

/-- Mirror of `highReachabilityPosition`. -/
def highReachabilityPosition : SituatedEarlyLearningPosition :=
  ⟨.childPositionB, .caregiverPositionB, .householdPositionB, .urban,
    .secureFlexible, .ordinaryAccess, .dominantLanguage,
    .lowerCareBurden, .kinCommunityGoverned, .institutionTrusted⟩

/-- Mirror of `effectiveCapabilityWitness`: the retained fine coordinate. -/
def effectiveCapabilityWitness (p : SituatedEarlyLearningPosition) : Bool :=
  match p.labour with
  | .secureFlexible => true
  | .precariousTimePoor => false

/-- Mirror of `familyChoiceIntersectionalNonFactorability`. -/
def familyChoiceIntersectionalNonFactorability :
    NonFactorabilityWitness familyChoiceProjection effectiveCapabilityWitness where
  left := lowReachabilityPosition
  right := highReachabilityPosition
  sameFlatProjection := rfl
  situatedOutcomesDiffer := by decide

/-- Mirror of `familyChoiceCannotDetermineEffectiveCapability`. -/
theorem familyChoiceCannotDetermineEffectiveCapability
    (factor : FactorsThrough familyChoiceProjection effectiveCapabilityWitness) : False :=
  witnessRulesOutEveryFlatFactorisation familyChoiceIntersectionalNonFactorability factor

end SituatedCapability

/-! ## Consumer 3: `DASHI.Education.EarlyLearningMultiOutcomeVectorExact` -/

namespace MultiOutcomeVector

open Intersectional

/-- Mirror of `EvidenceDirection`. -/
inductive EvidenceDirection
  | adverseSignal | unresolvedSignal | beneficialSignal
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `EntitlementState`. -/
inductive EntitlementState
  | entitlementAbsent | entitlementRetained
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `EarlyLearningOutcomeVector`: five separate evidence axes. -/
structure EarlyLearningOutcomeVector where
  /-- Child-development axis. -/
  childDevelopment : EvidenceDirection
  /-- Caregiver-labour axis. -/
  caregiverLabour : EvidenceDirection
  /-- Caregiver-wellbeing axis. -/
  caregiverWellbeing : EvidenceDirection
  /-- Fiscal-balance axis. -/
  fiscalBalance : EvidenceDirection
  /-- Entitlement axis. -/
  entitlement : EntitlementState
  deriving DecidableEq

/-- The outcome vector is the product of its five axes.  (A Lean-side
convenience: the Agda original is a record and states no such equivalence.) -/
def outcomeEquiv :
    EarlyLearningOutcomeVector ≃
      EvidenceDirection × EvidenceDirection × EvidenceDirection × EvidenceDirection ×
        EntitlementState where
  toFun v := (v.childDevelopment, v.caregiverLabour, v.caregiverWellbeing, v.fiscalBalance,
    v.entitlement)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv := by rintro ⟨_, _, _, _, _⟩; rfl
  right_inv := by rintro ⟨_, _, _, _, _⟩; rfl

instance : Fintype EarlyLearningOutcomeVector := Fintype.ofEquiv _ outcomeEquiv.symm

/-- Mirror of `labourProjection`. -/
def labourProjection : EarlyLearningOutcomeVector → EvidenceDirection :=
  EarlyLearningOutcomeVector.caregiverLabour

/-- Mirror of `childProjection`. -/
def childProjection : EarlyLearningOutcomeVector → EvidenceDirection :=
  EarlyLearningOutcomeVector.childDevelopment

/-- Mirror of `fiscalProjection`. -/
def fiscalProjection : EarlyLearningOutcomeVector → EvidenceDirection :=
  EarlyLearningOutcomeVector.fiscalBalance

/-- Mirror of `LabourMatchedCase`. -/
inductive LabourMatchedCase
  | labourGainChildAdverse | labourGainChildBeneficial
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `labourMatchedProjection`. -/
def labourMatchedProjection : LabourMatchedCase → EvidenceDirection
  | _ => .beneficialSignal

/-- Mirror of `childSignalAt`. -/
def childSignalAt : LabourMatchedCase → EvidenceDirection
  | .labourGainChildAdverse => .adverseSignal
  | .labourGainChildBeneficial => .beneficialSignal

/-- Mirror of `labourGainCannotDetermineChildEffect`, with its witness named. -/
def labourGainWitness : NonFactorabilityWitness labourMatchedProjection childSignalAt where
  left := .labourGainChildAdverse
  right := .labourGainChildBeneficial
  sameFlatProjection := rfl
  situatedOutcomesDiffer := by decide

theorem labourGainCannotDetermineChildEffect
    (factor : FactorsThrough labourMatchedProjection childSignalAt) : False :=
  witnessRulesOutEveryFlatFactorisation labourGainWitness factor

/-- Mirror of `SameChildDifferentFiscal`. -/
inductive SameChildDifferentFiscal
  | adverseChildFiscalUnknown | adverseChildFiscalPositive
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `sameChildProjection`. -/
def sameChildProjection : SameChildDifferentFiscal → EvidenceDirection
  | _ => .adverseSignal

/-- Mirror of `fiscalSignalAt`. -/
def fiscalSignalAt : SameChildDifferentFiscal → EvidenceDirection
  | .adverseChildFiscalUnknown => .unresolvedSignal
  | .adverseChildFiscalPositive => .beneficialSignal

/-- Mirror of `childSignalCannotDetermineFiscalEffect`, with its witness named. -/
def sameChildWitness : NonFactorabilityWitness sameChildProjection fiscalSignalAt where
  left := .adverseChildFiscalUnknown
  right := .adverseChildFiscalPositive
  sameFlatProjection := rfl
  situatedOutcomesDiffer := by decide

theorem childSignalCannotDetermineFiscalEffect
    (factor : FactorsThrough sameChildProjection fiscalSignalAt) : False :=
  witnessRulesOutEveryFlatFactorisation sameChildWitness factor

/-- Mirror of `WholePolicyVerdict`. -/
inductive WholePolicyVerdict
  | rejectPolicy | revisePolicy | supportPolicy
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `ExplicitAggregationRule`: the aggregation is a supplied function
and nothing about it is assumed. -/
structure ExplicitAggregationRule where
  /-- The supplied normative aggregation. -/
  aggregate : EarlyLearningOutcomeVector → WholePolicyVerdict

/-- Mirror of the empty type `SingleAxisWholeVerdictAuthority`. -/
inductive SingleAxisWholeVerdictAuthority : Type

/-- Mirror of `singleAxisCannotAutoPromoteToWholeVerdict`. -/
theorem singleAxisCannotAutoPromoteToWholeVerdict
    (h : SingleAxisWholeVerdictAuthority) : False := nomatch h

/-- The outcome vector carrier has 162 elements. -/
theorem card_outcomeVector : Fintype.card EarlyLearningOutcomeVector = 162 := by
  have h3 : Fintype.card EvidenceDirection = 3 := rfl
  have h2 : Fintype.card EntitlementState = 2 := rfl
  rw [Fintype.card_congr outcomeEquiv, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_prod, h3, h2]

/-- The verdict carrier has 3. -/
theorem card_verdict : Fintype.card WholePolicyVerdict = 3 := by decide

end MultiOutcomeVector

end AgdaMirror.NonFactorabilityKernels
