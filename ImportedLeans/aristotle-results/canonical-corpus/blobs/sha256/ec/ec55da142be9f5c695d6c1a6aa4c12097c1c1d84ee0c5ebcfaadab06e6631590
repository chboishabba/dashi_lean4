import Integration.PipelineAdequacy
import Integration.SeparabilityContrast
import AgdaMirror.NonFactorabilityKernels
import AgdaMirror.MonsterOntos
import Integration.Levels

/-!
# Source-exact welds: the Level-II owners against real corpus carriers

The Level-II round left three welds honest but undischarged (registry rows 62,
63 and 67), because the surfaces they were written for were not in the tree.
This file goes the other way round: it starts from carriers that *are* in the
tree — transcribed in `AgdaMirror.NonFactorabilityKernels` and
`AgdaMirror.MonsterOntos` — and asks, for each, whether the four frozen owners
absorb it, and if not, exactly what is missing.

The owners are used as they stand.  No new owner is introduced; the only
addition to one is a further *construction* of an existing datum
(`Integration.FactorisationCollision.nonempty_collision_of_card_lt`), which is
a fifth way to build a `Collision`, not a fifth theorem family.

## What is established

### §1 The corpus already has the collision owner, twice

`DASHI.Core.IntersectionalNonFactorability` and
`DASHI.Core.ReopenableConsumerInterventionKernelExact` §1 define the same pair
of records under different names.  `kernelWitnessEquiv` is an explicit
equivalence between the two Agda-side defect records, and
`collisionOfNonFactorability` / `nonFactorabilityOfCollision` (and their
`ConsumerDescent` counterparts) are inverse translations to the Lean owner.  So
both kernels are **exact instances** of `Collision`, not analogues of it.

### §2 Weld 62, discharged from a checked corpus surface

`DASHI.Core.SocioEcologicalFeedbackExact` supplies exactly the carrier the weld
needed: a declared resource-level observer `staticScore`, a mediating
disposition coordinate `actorOf`, and a realised outcome `react`.  The precise
question — *is the resource observer adequate for the realised-outcome
consumer?* — is answered **no** (`resource_observer_not_adequate`), and the
answer is a `Collision`, hence also `¬ ComputationRepair`.  Restoring the
mediating information makes the pipeline adequate
(`provisioned_pipeline_adequate`), so the repair is representational.
`resource_does_not_determine_realised_outcome` is the requested theorem shape
`∃ x y, R x = R y ∧ P x ≠ P y ∧ W x ≠ W y`.

### §3 Two empty types in the corpus, given content

Both kernels state a no-auto-promotion boundary by declaring a type with no
constructors.  That is a declaration, not a theorem.  Here are the theorems:

* `no_aggregation_rule_determines_the_outcome_vector` — for **every** explicit
  aggregation rule, the whole-policy verdict fails to determine the five-axis
  outcome vector, by cardinality;
* `marginals_do_not_determine_interaction` — a representation retaining every
  marginal coordinate loses the joint, so **interaction is not another
  coordinate**;
* `interaction_zero_iff_separable` — and the lost quantity is exactly the
  rectangle obstruction that `Integration.SeparabilityContrast` owns.

### §4 An honest negative about the contrast owner

The corpus's intersectional and provisioning surfaces are *collisions*, not
contrast reversals.  `separable_of_subsingleton_left` and
`socioEcological_every_table_separable` prove why in the provisioning case: the
intervention carrier has one element, so every table over it is separable and
no rectangle obstruction can exist there.  The contrast owner therefore does
**not** apply to that surface, and saying so is a theorem rather than a
judgement call.

### §5 Exhaustiveness evidence on a real proof-producing carrier

`AgdaMirror.MonsterOntos.SSP` is a corpus carrier with a finite enumeration
whose completeness is proved by kernel computation.  `sspExhaustive` is genuine
`Exhaustive` evidence, and `twoDigit_adequate` is `AdequateOn + Exhaustive ⇒
Adequate` applied to it.  The contrast is `lastDigit_adequateOn_atlas` versus
`lastDigit_not_adequate`: the same route over a three-element sub-atlas
delivers nothing, because that carrier has no such evidence.

Nothing here is a claim about ecology, policy, education, institutions or the
Monster group.  Every carrier is a finite label type, a record of finite label
types, `ℚ`, or a fifteen-element enumeration.
-/

namespace Integration.SourceExactWelds

open Integration.CoordinateSufficiency
open Integration.FactorisationCollision
open Integration.RealisationAdequacy
open Integration.PipelineAdequacy
open AgdaMirror.NonFactorabilityKernels

/-! ## §1 Both Agda kernels are the collision owner -/

section Kernels

variable {X Y Z : Type} {P : X → Y} {C : X → Z}

/-- A `NonFactorabilityWitness` of the Agda intersectionality kernel **is** a
`Collision`: the separated pair is distinct because the consumer separates
it. -/
def collisionOfNonFactorability (w : Intersectional.NonFactorabilityWitness P C) :
    Collision P C where
  left := w.left
  right := w.right
  distinct := fun h => w.situatedOutcomesDiffer (congrArg C h)
  collide := w.sameFlatProjection
  separate := fun h => w.situatedOutcomesDiffer h

/-- And conversely. -/
def nonFactorabilityOfCollision (w : Collision P C) :
    Intersectional.NonFactorabilityWitness P C where
  left := w.left
  right := w.right
  sameFlatProjection := w.collide
  situatedOutcomesDiffer := w.separate

/-- A `ConsumerDescentDefect` of the reopenable-consumer kernel is the same
`Collision`. -/
def collisionOfConsumerDescentDefect (w : ConsumerKernel.ConsumerDescentDefect P C) :
    Collision P C where
  left := w.left
  right := w.right
  distinct := fun h => w.consumerDistinguishes (congrArg C h)
  collide := w.sameProjection
  separate := fun h => w.consumerDistinguishes h

/-- And conversely. -/
def consumerDescentDefectOfCollision (w : Collision P C) :
    ConsumerKernel.ConsumerDescentDefect P C where
  left := w.left
  right := w.right
  sameProjection := w.collide
  consumerDistinguishes := w.separate

/-- **The two corpus kernels are literally the same record.**  The
intersectionality kernel's `NonFactorabilityWitness` and the
reopenable-consumer kernel's `ConsumerDescentDefect` are equivalent, for every
projection and every consumer. -/
def kernelWitnessEquiv :
    Intersectional.NonFactorabilityWitness P C ≃ ConsumerKernel.ConsumerDescentDefect P C where
  toFun w := ⟨w.left, w.right, w.sameFlatProjection, w.situatedOutcomesDiffer⟩
  invFun w := ⟨w.left, w.right, w.sameProjection, w.consumerDistinguishes⟩
  left_inv := by rintro ⟨_, _, _, _⟩; rfl
  right_inv := by rintro ⟨_, _, _, _⟩; rfl

/-- The pair-swap involution on an intersectionality witness. -/
def swapWitness (w : Intersectional.NonFactorabilityWitness P C) :
    Intersectional.NonFactorabilityWitness P C where
  left := w.right
  right := w.left
  sameFlatProjection := w.sameFlatProjection.symm
  situatedOutcomesDiffer := fun h => w.situatedOutcomesDiffer h.symm

/-- The pair-swap involution on a consumer-descent defect. -/
def swapDefect (w : ConsumerKernel.ConsumerDescentDefect P C) :
    ConsumerKernel.ConsumerDescentDefect P C where
  left := w.right
  right := w.left
  sameProjection := w.sameProjection.symm
  consumerDistinguishes := fun h => w.consumerDistinguishes h.symm

/-- A corpus `FactorsThrough` gives the owner's `Determines`. -/
theorem determines_of_factorsThrough (d : Intersectional.FactorsThrough P C) :
    Determines P C := by
  intro x y hxy
  rw [d.factorisation x, d.factorisation y, hxy]

/-- A corpus `ConsumerDescent` gives the owner's `Determines`. -/
theorem determines_of_consumerDescent (d : ConsumerKernel.ConsumerDescent P C) :
    Determines P C := by
  intro x y hxy
  rw [d.factorises x, d.factorises y, hxy]

/-- And back, so the corpus's positive notion is the owner's, not a weaker
relative.  (`Nonempty Z` is needed only to name a value off the image.) -/
theorem nonempty_factorsThrough_iff_determines [Nonempty Z] (P : X → Y) (C : X → Z) :
    Nonempty (Intersectional.FactorsThrough P C) ↔ Determines P C := by
  constructor
  · rintro ⟨d⟩; exact determines_of_factorsThrough d
  · intro h
    obtain ⟨f, hf⟩ := (determines_iff_refines P C).mp h
    exact ⟨⟨f, hf⟩⟩

/-- **The kernels' refutation lemmas are the owner theorem.** -/
theorem kernel_refutations_are_the_owner :
    (Intersectional.NonFactorabilityWitness P C → ¬ Determines P C) ∧
      (ConsumerKernel.ConsumerDescentDefect P C → ¬ Determines P C) :=
  ⟨fun w => (collisionOfNonFactorability w).not_determines,
    fun w => (collisionOfConsumerDescentDefect w).not_determines⟩

end Kernels

/-! ### The three corpus consumers, filed against the owner -/

/-- The situated early-learning position's flat public label collides against
the retained capability coordinate. -/
def situatedCapabilityCollision :
    Collision SituatedCapability.familyChoiceProjection
      SituatedCapability.effectiveCapabilityWitness :=
  collisionOfNonFactorability SituatedCapability.familyChoiceIntersectionalNonFactorability

/-- The labour axis collides against the child-development axis. -/
def labourAxisCollision :
    Collision MultiOutcomeVector.labourMatchedProjection MultiOutcomeVector.childSignalAt :=
  collisionOfNonFactorability MultiOutcomeVector.labourGainWitness

/-- The child axis collides against the fiscal axis. -/
def childAxisCollision :
    Collision MultiOutcomeVector.sameChildProjection MultiOutcomeVector.fiscalSignalAt :=
  collisionOfNonFactorability MultiOutcomeVector.sameChildWitness

/-- **Three corpus surfaces, one owner.**  Each corpus non-factorability lemma
is `Collision.not_determines` applied to a corpus witness. -/
theorem three_corpus_surfaces_one_owner :
    ¬ Determines SituatedCapability.familyChoiceProjection
        SituatedCapability.effectiveCapabilityWitness ∧
      ¬ Determines MultiOutcomeVector.labourMatchedProjection
        MultiOutcomeVector.childSignalAt ∧
      ¬ Determines MultiOutcomeVector.sameChildProjection
        MultiOutcomeVector.fiscalSignalAt :=
  ⟨situatedCapabilityCollision.not_determines, labourAxisCollision.not_determines,
    childAxisCollision.not_determines⟩

/-- **The two kernels are the same structure, with its operation.**  The
equivalence intertwines the pair-swap involution, so the identification is a
`Integration.Levels.Transport` and not merely a bijection of carriers.  Stated
at the corpus's own provisioning surface. -/
def kernelTransport :
    Integration.Levels.Transport
      (Intersectional.NonFactorabilityWitness SocioEcologicalFeedback.staticScore
        (SocioEcologicalFeedback.react .voluntaryBuffer))
      (ConsumerKernel.ConsumerDescentDefect SocioEcologicalFeedback.staticScore
        (SocioEcologicalFeedback.react .voluntaryBuffer))
      swapWitness swapDefect where
  map := kernelWitnessEquiv
  equivariant := fun _ => rfl

/-! ## §2 Weld 62: the resource observer against the realised-outcome consumer -/

namespace Provisioning

open SocioEcologicalFeedback

/-- The realised outcome of the corpus's single declared intervention. -/
def realisedOutcome : World → Outcome := react .voluntaryBuffer

/-- The resource-level observer the corpus supplies: the declared static plan
score. -/
def resourceObserver : World → StaticPlanScore := staticScore

/-- The mediating coordinate the corpus supplies: the actor disposition. -/
def provisioningObserver : World → ActorDisposition := actorOf

/-- **The collision.**  The resource observer identifies two worlds that the
realised outcome separates.  This is the corpus's own
`staticPlanScoreCannotDetermineReactiveOutcome`, translated into the owner. -/
def resourceCollision : Collision resourceObserver realisedOutcome :=
  collisionOfConsumerDescentDefect staticPlanScoreCannotDetermineReactiveOutcome

/-- **The requested theorem shape.**  Two states with the same resource reading,
different provisioning information, and different realised outcomes. -/
theorem resource_does_not_determine_realised_outcome :
    ∃ x y : World, resourceObserver x = resourceObserver y ∧
      provisioningObserver x ≠ provisioningObserver y ∧
      realisedOutcome x ≠ realisedOutcome y :=
  ⟨.cooperativeWorld, .resistantWorld, rfl, by decide, by decide⟩

/-- The resource-only pipeline: the source is the world, the representation is
the declared score, and the realisation carries nothing more. -/
def resourcePipeline : Pipeline World StaticPlanScore StaticPlanScore where
  represent := resourceObserver
  realise := id

/-- The provisioned pipeline: the representation retains the mediating
coordinate and the realisation is the response computed from it. -/
def provisionedPipeline : Pipeline World ActorDisposition Outcome where
  represent := provisioningObserver
  realise := fun a => match a with | .cooperate => .implemented | .resist => .blocked

/-- The provisioned pipeline really does realise the corpus's reaction: this is
the mirror's `canonicalReactiveAgentSystem.responseMatchesWorld`. -/
theorem provisionedPipeline_state : provisionedPipeline.state = realisedOutcome := by
  funext w; cases w <;> rfl

/-- The realised-outcome consumer, observing the realisation in full. -/
def outcomeConsumer : ConsumerSpec World Outcome where
  Obs := Outcome
  observe := id
  Ans := Outcome
  demand := realisedOutcome

/-- The same consumer, reading the resource-only realisation. -/
def resourceOutcomeConsumer : ConsumerSpec World StaticPlanScore where
  Obs := StaticPlanScore
  observe := id
  Ans := Outcome
  demand := realisedOutcome

/-- **The answer to the weld's question: no.**  The resource observer is not
adequate for the realised-outcome consumer — and not for any consumer asking
that question, whatever it observes of the resource-only realisation. -/
theorem resource_observer_not_adequate (Obs : Type) (observe : StaticPlanScore → Obs) :
    ¬ AdequateFor resourcePipeline ⟨Obs, observe, Outcome, realisedOutcome⟩ :=
  pipeline_adequacy_lost_at_realisation resourcePipeline resourceCollision Obs observe

/-- In particular for the identity observation. -/
theorem resource_outcome_consumer_not_adequate :
    ¬ AdequateFor resourcePipeline resourceOutcomeConsumer :=
  resource_observer_not_adequate StaticPlanScore id

/-- **And the repair is representational, not computational.**  No reading of
the declared score returns the realised outcome, while a finer representation
that does exist. -/
theorem resource_repair_is_representational :
    ¬ ComputationRepair resourceObserver realisedOutcome ∧
      RepresentationRepair resourceObserver realisedOutcome :=
  repair_dichotomy resourceCollision

/-- **Restoring the provisioning information restores adequacy.** -/
theorem provisioned_pipeline_adequate : AdequateFor provisionedPipeline outcomeConsumer := by
  intro x y hxy
  have : provisionedPipeline.state x = provisionedPipeline.state y := hxy
  rw [provisionedPipeline_state] at this
  exact this

/-- **Weld 62, discharged.**  On the corpus's own carrier: the resource observer
is inadequate for the realised-outcome consumer, no downstream computation
repairs that, and the pipeline that retains the mediating coordinate is
adequate. -/
theorem weld62_resource_adequacy :
    (¬ AdequateFor resourcePipeline resourceOutcomeConsumer) ∧
      (¬ ComputationRepair resourceObserver realisedOutcome) ∧
      AdequateFor provisionedPipeline outcomeConsumer :=
  ⟨resource_outcome_consumer_not_adequate, resource_repair_is_representational.1,
    provisioned_pipeline_adequate⟩

end Provisioning

/-! ## §3 The corpus's two empty types, given content -/

/-- **Every explicit aggregation rule loses the outcome vector.**  The corpus
declares `SingleAxisWholeVerdictAuthority` to be empty; the theorem behind that
declaration is this one, and it is stronger: it is not that no *privileged*
aggregation exists, but that no aggregation whatsoever determines the vector,
because the verdict carrier has three elements and the vector carrier has one
hundred and sixty-two. -/
theorem no_aggregation_rule_determines_the_outcome_vector
    (rule : MultiOutcomeVector.ExplicitAggregationRule) :
    ¬ Determines rule.aggregate (id : MultiOutcomeVector.EarlyLearningOutcomeVector →
      MultiOutcomeVector.EarlyLearningOutcomeVector) := by
  refine not_determines_of_card_lt rule.aggregate ?_
  rw [MultiOutcomeVector.card_verdict, MultiOutcomeVector.card_outcomeVector]
  norm_num

/-- Nor does any reading of the verdict. -/
theorem no_reading_of_the_verdict_determines_the_vector
    (rule : MultiOutcomeVector.ExplicitAggregationRule)
    (f : MultiOutcomeVector.WholePolicyVerdict → MultiOutcomeVector.EarlyLearningOutcomeVector) :
    ¬ ∀ v, v = f (rule.aggregate v) := by
  have h : Fintype.card MultiOutcomeVector.WholePolicyVerdict <
      Fintype.card MultiOutcomeVector.EarlyLearningOutcomeVector := by
    rw [MultiOutcomeVector.card_verdict, MultiOutcomeVector.card_outcomeVector]; norm_num
  exact (nonempty_collision_of_card_lt rule.aggregate h).some.no_reading f

/-! ### Interaction is not another coordinate -/

section Interaction

open Integration.SeparabilityContrast

/-- The pair of unnormalised marginals of a two-by-two rational table: every
row total and every column total. -/
def marginalPair (C : Bool → Bool → ℚ) : (Bool → ℚ) × (Bool → ℚ) :=
  (fun a => C a false + C a true, fun b => C false b + C true b)

/-- The rectangle defect of a two-by-two table. -/
def interaction (C : Bool → Bool → ℚ) : ℚ :=
  C true true + C false false - C true false - C false true

/-- **The lost quantity is exactly the separability obstruction.**  A
two-by-two rational table is separable if and only if its rectangle defect
vanishes. -/
theorem interaction_zero_iff_separable (C : Bool → Bool → ℚ) :
    interaction C = 0 ↔ Separable C := by
  rw [separable_iff_rectangle]
  constructor
  · intro h a a' b b'
    have h' : C true true + C false false = C true false + C false true := by
      simp only [interaction] at h; linarith
    cases a <;> cases a' <;> cases b <;> cases b' <;> linarith
  · intro h
    have := h true false true false
    simp only [interaction]
    linarith

/-- One table with unit marginals. -/
def diagTable : Bool → Bool → ℚ := fun a b => if a = b then 1 else 0

/-- Another table with the same marginals. -/
def antiTable : Bool → Bool → ℚ := fun a b => if a = b then 0 else 1

/-- **Interaction is not another coordinate.**  The representation that retains
every marginal coordinate identifies two tables whose rectangle defects differ
by four.  A representation can therefore keep all the marginals and still lose
their joint structure. -/
def marginalCollisionOnInteraction : Collision marginalPair interaction where
  left := diagTable
  right := antiTable
  distinct := by
    intro h
    have := congrFun (congrFun h true) true
    simp [diagTable, antiTable] at this
  collide := by
    simp only [marginalPair, Prod.mk.injEq]
    constructor <;> funext x <;> cases x <;> norm_num [diagTable, antiTable]
  separate := by norm_num [interaction, diagTable, antiTable]

/-- Hence the marginals do not determine the interaction, and no reading of
them does. -/
theorem marginals_do_not_determine_interaction : ¬ Determines marginalPair interaction :=
  marginalCollisionOnInteraction.not_determines

/-- **The corpus's `separateAxisSufficiencyCannotAutoPromote`, as a theorem.**
Each marginal observation determines its own marginal question, yet the pair of
them does not determine the joint structure.  The corpus states this by
declaring an empty permission type; this is the mathematical content behind
it. -/
theorem separate_axis_sufficiency_does_not_promote :
    Determines marginalPair (fun C => (marginalPair C).1) ∧
      Determines marginalPair (fun C => (marginalPair C).2) ∧
      ¬ Determines marginalPair interaction :=
  ⟨fun _ _ h => congrArg Prod.fst h, fun _ _ h => congrArg Prod.snd h,
    marginals_do_not_determine_interaction⟩

/-- And the two tables really are separated by separability itself: one is
non-separable and the other is too, but their defects have opposite sign, so no
reweighting of either coordinate reconciles them. -/
theorem tables_not_separable : ¬ Separable diagTable ∧ ¬ Separable antiTable := by
  constructor
  · rw [← interaction_zero_iff_separable]; norm_num [interaction, diagTable]
  · rw [← interaction_zero_iff_separable]; norm_num [interaction, antiTable]

end Interaction

/-! ## §4 Where the contrast owner does not apply -/

section NoRectangle

open Integration.SeparabilityContrast

/-- **A one-element first coordinate admits no interaction.**  Every table whose
first coordinate is a subsingleton is separable, so no contrast obstruction can
be exhibited over it. -/
theorem separable_of_subsingleton_left {A B M : Type*} [AddCommGroup M] [Subsingleton A]
    (C : A → B → M) : Separable C := by
  classical
  by_cases h : Nonempty A
  · obtain ⟨a₀⟩ := h
    exact ⟨fun _ => 0, fun b => C a₀ b, fun a b => by rw [zero_add, Subsingleton.elim a a₀]⟩
  · exact ⟨fun _ => 0, fun _ => 0, fun a _ => absurd ⟨a⟩ h⟩

/-- Applied to the provisioning surface: the corpus declares exactly one
intervention, so every rational table indexed by interventions is separable and
the contrast owner has nothing to refute there.  The obstruction on that surface
is of collision type and cannot be of contrast type. -/
theorem socioEcological_every_table_separable
    (C : SocioEcologicalFeedback.Intervention → Bool → ℚ) : Separable C := by
  haveI : Subsingleton SocioEcologicalFeedback.Intervention :=
    ⟨fun a b => by cases a; cases b; rfl⟩
  exact separable_of_subsingleton_left C

end NoRectangle

/-! ## §5 Exhaustiveness evidence on a proof-producing corpus carrier -/

namespace SSPAdequacy

open AgdaMirror.MonsterOntos

deriving instance Fintype for AgdaMirror.MonsterOntos.SSP

/-- The full corpus enumeration of the fifteen supersingular primes. -/
def sspEnumeration : List SSP :=
  [.p2, .p3, .p5, .p7, .p11, .p13, .p17, .p19, .p23, .p29, .p31, .p41, .p47, .p59, .p71]

/-- A three-element sub-atlas of it. -/
def sspAtlas : List SSP := [.p2, .p3, .p5]

/-- **The enumeration is complete, by kernel computation.**  This is the
proof-producing part: the completeness is decided, not declared. -/
theorem sspEnumeration_complete : ∀ p : SSP, p ∈ sspEnumeration := by decide

/-- Hence genuine `Exhaustive` evidence for the declared carrier. -/
def sspExhaustive : Exhaustive (fun p : SSP => p ∈ sspEnumeration) where
  covers := sspEnumeration_complete

/-- The sub-atlas has no such evidence. -/
theorem sspAtlas_not_exhaustive : ¬ Nonempty (Exhaustive (fun p : SSP => p ∈ sspAtlas)) := by
  rintro ⟨e⟩
  have : (SSP.p7 : SSP) ∈ sspAtlas := e.covers .p7
  revert this
  decide

/-- The identity pipeline on the corpus carrier. -/
def sspPipeline : Pipeline SSP SSP SSP where
  represent := id
  realise := id

/-- The last decimal digit of the prime. -/
def lastDigit (p : SSP) : ℕ := toNat p % 10

/-- The two-digit reading of the prime. -/
def twoDigit (p : SSP) : ℕ := toNat p % 100

/-- The consumer that asks for the prime and reads the last digit. -/
def lastDigitConsumer : ConsumerSpec SSP SSP where
  Obs := ℕ
  observe := lastDigit
  Ans := ℕ
  demand := toNat

/-- The consumer that asks for the prime and reads two digits. -/
def twoDigitConsumer : ConsumerSpec SSP SSP where
  Obs := ℕ
  observe := twoDigit
  Ans := ℕ
  demand := toNat

/-- On the three-element sub-atlas the last digit is adequate — checked by
enumeration over that carrier. -/
theorem lastDigit_adequateOn_atlas :
    AdequateOn (fun p : SSP => p ∈ sspAtlas) sspPipeline lastDigitConsumer := by
  have h : ∀ x y : SSP, x ∈ sspAtlas → y ∈ sspAtlas → lastDigit x = lastDigit y →
      toNat x = toNat y := by decide
  exact h

/-- **But it is not adequate on the carrier.**  Three and thirteen share a last
digit, so the sub-atlas result licenses nothing about `SSP`. -/
theorem lastDigit_not_adequate : ¬ AdequateFor sspPipeline lastDigitConsumer := by
  intro h
  have : toNat SSP.p3 = toNat SSP.p13 := h .p3 .p13 rfl
  revert this
  decide

/-- The two-digit reading is adequate **on the full declared enumeration** —
again checked by enumeration, over fifteen elements. -/
theorem twoDigit_adequateOn_enumeration :
    AdequateOn (fun p : SSP => p ∈ sspEnumeration) sspPipeline twoDigitConsumer := by
  have h : ∀ x y : SSP, x ∈ sspEnumeration → y ∈ sspEnumeration → twoDigit x = twoDigit y →
      toNat x = toNat y := by decide
  exact h

/-- **`AdequateOn` + `Exhaustive` ⇒ `Adequate`, on a real proof-producing
carrier.**  The upgrade is the owner's, the enumeration is the corpus's, and the
exhaustiveness is a decided theorem rather than a flag. -/
theorem twoDigit_adequate : AdequateFor sspPipeline twoDigitConsumer :=
  adequate_of_adequateOn_exhaustive twoDigit_adequateOn_enumeration sspExhaustive

/-- **And the evidence is what makes the difference.**  The same route over the
sub-atlas gives an `AdequateOn` with no `Exhaustive` to pair it with, and the
global statement is false there. -/
theorem exhaustiveness_evidence_is_load_bearing :
    AdequateOn (fun p : SSP => p ∈ sspAtlas) sspPipeline lastDigitConsumer ∧
      ¬ Nonempty (Exhaustive (fun p : SSP => p ∈ sspAtlas)) ∧
      ¬ AdequateFor sspPipeline lastDigitConsumer ∧
      AdequateFor sspPipeline twoDigitConsumer :=
  ⟨lastDigit_adequateOn_atlas, sspAtlas_not_exhaustive, lastDigit_not_adequate,
    twoDigit_adequate⟩

end SSPAdequacy

end Integration.SourceExactWelds
