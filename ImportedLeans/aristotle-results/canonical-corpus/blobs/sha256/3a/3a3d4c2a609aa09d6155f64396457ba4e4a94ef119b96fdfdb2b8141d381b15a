import Integration.RealisationAdequacy
import Integration.FactorisationCollision
import Integration.SeparabilityContrast
import Integration.LanguageReachability
import Integration.SelectiveDecision
import Integration.CounterfactualEffect
import Integration.ParetoOutcome

/-!
# The welds: thin consumers sewn back onto the Level-II owners

The four owners of this round —

* `Integration.RealisationAdequacy` (consumer-indexed realisation/adequacy),
* `Integration.FactorisationCollision` (projection/aggregation/scalarisation
  loss),
* `Integration.SeparabilityContrast` (interaction and non-separability),
* `Integration.LanguageReachability` (language-indexed reachability)

— are only worth having if the lanes that used to prove these things for
themselves now *consume* them.  This file is the seam.  Every weld below is
either

* an **instance**: a statement already in the tree, re-derived from an owner
  rather than from a bespoke argument; or
* a **bridge**: a proved implication whose hypothesis is the datum a lane would
  have to supply.  The bridge is filed as a candidate exactly because the
  hypothesis is not discharged here.

The distinction is kept explicit in the names (`weld_…_instance` versus
`weld_…_bridge`), and the registry rows in `Integration.SewingRegistry` carry
it in their class.

**Structural resemblance is never taken as an identification.**  Where the
handoff names a surface that is not in this tree, the weld is a bridge over an
undischarged hypothesis and no instance is claimed.

## The eight welds

1. formalisation/reconstruction → consumer-indexed adequacy;
2. provisioning / mediation → realisation (mediator) adequacy;
3. threshold-distance and trajectory comparison → interaction;
4. early-learning / counterfactual reasoning → hidden-coordinate essentiality;
5. Pareto planning → scalarisation collision and non-descent;
6. selective decision → action/readout non-invertibility;
7. atlases → declared-carrier completeness;
8. admissible reachability → language-relative reachability.
-/

namespace Integration.LevelIIWelds

open Integration.CoordinateSufficiency
open Integration.RealisationAdequacy
open Integration.FactorisationCollision
open Integration.SeparabilityContrast
open Integration.LanguageReachability
open Integration.DeclaredCarrier

/-! ## Weld 1: formalisation/reconstruction → consumer-indexed adequacy -/

open Integration.ContextIndexedRole in
/-- Reading the corpus's flattening as a pipeline: the situated state is
represented faithfully and then *realised* as its flat label. -/
def flatteningPipeline : Pipeline SituatedState SituatedState FlatSingleAxis where
  represent := id
  realise := flatProjection

open Integration.ContextIndexedRole in
/-- The consumer that asks only for the flat label. -/
def labelConsumer : ConsumerSpec SituatedState FlatSingleAxis where
  Obs := FlatSingleAxis
  observe := id
  Ans := FlatSingleAxis
  demand := flatProjection

open Integration.ContextIndexedRole in
/-- The consumer that asks for the relational outcome. -/
def relationalConsumer : ConsumerSpec SituatedState FlatSingleAxis where
  Obs := FlatSingleAxis
  observe := id
  Ans := Bool
  demand := relationalOutcome

open Integration.ContextIndexedRole in
/-- **Weld 1, instance.**  One reconstruction, two consumers: the flattened
reconstruction is adequate for the consumer that asks about the label and
inadequate for the consumer that asks about the relation.  The corpus's
`flatReweightingCannotRepairMissingRelation` is the second half; the first half
is what makes the failure *consumer-relative* rather than a defect of the
reconstruction as such. -/
theorem weld_reconstruction_instance :
    AdequateFor flatteningPipeline labelConsumer ∧
      ¬ AdequateFor flatteningPipeline relationalConsumer :=
  ⟨fun _ _ h => h, flat_reweighting_cannot_repair⟩

open Integration.ContextIndexedRole in
/-- **Weld 1, located.**  The loss is at the realisation stage, not at the
representation stage: the representation determines the relational outcome and
its realisation does not. -/
theorem weld_reconstruction_loss_is_at_realisation :
    RepresentationAdequate flatteningPipeline relationalConsumer ∧
      ¬ RealisationAdequate flatteningPipeline relationalConsumer :=
  ⟨fun _ _ h => congrArg relationalOutcome h, flat_reweighting_cannot_repair⟩

/-! ## Weld 2: provisioning / mediation → realisation adequacy -/

/-- **Weld 2, bridge.**  The datum a mediation lane must supply is a collision
of the *realised* state against the consumer's demand.  Given it, the mediator
is inadequate — and so is every observation of the mediator's output, however
the output is post-processed.  The hypothesis is left undischarged: this tree
contains no provisioning surface. -/
theorem weld_mediator_bridge {S R X : Type} {P : Pipeline S R X} {c : ConsumerSpec S X}
    (w : Collision P.state c.demand) :
    ¬ RealisationAdequate P c ∧
      ∀ (Obs : Type) (o : X → Obs), ¬ Determines (fun s => o (P.state s)) c.demand :=
  ⟨w.not_determines, fun _ o => (w.post o).not_determines⟩

open Integration.SelectiveDecision in
/-- The in-tree mediator: a decision is compiled to an action, and the action is
what any downstream consumer sees. -/
def compilePipeline : Pipeline Decision Decision Action where
  represent := id
  realise := compileDecision

open Integration.SelectiveDecision in
/-- The consumer that needs the believed direction. -/
def directionConsumer : ConsumerSpec Decision Action where
  Obs := Action
  observe := id
  Ans := Direction
  demand := Decision.direction

open Integration.SelectiveDecision in
/-- The collision the bridge asks for, in the tree. -/
def compileCollision : Collision compilePipeline.state directionConsumer.demand where
  left := ⟨.down, true⟩
  right := ⟨.up, true⟩
  distinct := by decide
  collide := rfl
  separate := show Direction.down ≠ Direction.up by decide

open Integration.SelectiveDecision in
/-- **Weld 2, instance.**  The compiled action is a mediator that loses the
direction: representation adequacy holds, mediator adequacy fails, and no
reading of the action recovers it. -/
theorem weld_mediator_instance :
    RepresentationAdequate compilePipeline directionConsumer ∧
      ¬ RealisationAdequate compilePipeline directionConsumer ∧
      ∀ (Obs : Type) (o : Action → Obs),
        ¬ Determines (fun d => o (compileDecision d)) Decision.direction :=
  ⟨fun _ _ h => congrArg Decision.direction h,
    (weld_mediator_bridge compileCollision).1,
    (weld_mediator_bridge compileCollision).2⟩

/-! ## Weld 3: threshold distance and trajectory comparison → interaction -/

/-- **Weld 3, bridge.**  The datum a threshold or trajectory lane must supply is
a pair of weightings of the second coordinate under which the first-coordinate
contrast changes sign.  Given it, the consumer is not a sum of coordinatewise
effects, so no reweighting repairs the comparison. -/
theorem weld_threshold_bridge {C : Bool → Bool → ℚ}
    (hpos : 0 < contrast C atTrue true false) (hneg : contrast C atFalse true false < 0) :
    ¬ Separable C :=
  not_separable_of_contrast_reversal atTrue_sum atFalse_sum hpos hneg

/-- **Weld 3, instance.**  A two-point horizon on which the comparison between
two trajectories reverses: which is ahead is a joint property of the trajectory
pair and the horizon weighting. -/
theorem weld_threshold_instance : ¬ Separable trajectory := thresholdInstance.2.2

/-- **Weld 3, second instance.**  A product of two indicator coordinates: the
contextual/intersectional shape, refuted by the same owner. -/
theorem weld_product_instance : ¬ Separable product := productInstance.2.2

/-! ## Weld 4: early learning / counterfactual → hidden-coordinate essentiality -/

open Integration.CounterfactualEffect in
/-- The corpus's situated exposure, re-coordinatised as a two-coordinate
Boolean product: the observed position and the hidden counterfactual.  (The
intervention label carrier has one element, so nothing is lost.) -/
def exposureOf (x : Fin 2 → Bool) : SituatedExposure where
  intervention := .expandedSubsidisedECEC
  observedPosition := if x 0 then .observedHigherResource else .observedLowerResource
  counterfactual := if x 1 then .strongerAlternativeCare else .weakerAlternativeCare

open Integration.CounterfactualEffect in
/-- The re-coordinatisation is onto: every situated exposure is `exposureOf` of
some coordinate pair, so the encoding drops nothing. -/
theorem exposureOf_surjective : Function.Surjective exposureOf := by
  rintro ⟨⟨⟩, p, c⟩
  cases p <;> cases c
  · exact ⟨![true, true], rfl⟩
  · exact ⟨![true, false], rfl⟩
  · exact ⟨![false, true], rfl⟩
  · exact ⟨![false, false], rfl⟩

open Integration.CounterfactualEffect in
/-- The effect, read on the coordinate product. -/
def effectOfCoords (x : Fin 2 → Bool) : EffectDirection :=
  counterfactualRelativeEffect (exposureOf x)

open Integration.CounterfactualEffect in
/-- **Weld 4, instance.**  The hidden coordinate is essential and the observed
one is not: the corpus's counterfactual lane is exactly one essential coordinate
in the owner's sense. -/
theorem weld_hidden_coordinate_essential :
    Essential (A := fun _ : Fin 2 => Bool) 1 effectOfCoords ∧
      ¬ Essential (A := fun _ : Fin 2 => Bool) 0 effectOfCoords := by
  constructor
  · refine ⟨![false, true], ![false, false], ?_, ?_⟩
    · intro i hi; fin_cases i <;> simp_all
    · decide
  · rintro ⟨x, y, hxy, hne⟩
    apply hne
    have h1 : x 1 = y 1 := hxy 1 (by decide)
    refine counterfactual_determines_effect (exposureOf x) (exposureOf y) ?_
    simp only [exposureOf, h1]

open Integration.CounterfactualEffect in
/-- **Weld 4, owner form.**  Deleting the hidden coordinate destroys the effect,
via the collision the owner builds from essentiality.  This is the corpus's
"observed position cannot determine the effect" as an instance of coordinate
deletion. -/
theorem weld_hidden_deletion :
    ¬ Determines (deleteCoord (A := fun _ : Fin 2 => Bool) 1) effectOfCoords :=
  (Collision.ofEssential weld_hidden_coordinate_essential.1).not_determines

/-! ## Weld 5: Pareto planning → scalarisation collision and non-descent -/

open Integration.ParetoOutcome in
/-- The scalar total of the corpus's two-objective outcome collides. -/
def paretoTotalCollision : Collision total (fun a : Outcome 2 => a 0) where
  left := pair 0 2
  right := pair 2 0
  distinct := by
    intro h
    have := congrFun h 0
    simp [pair, mo] at this
  collide := total_collides_incomparable
  separate := by simp [mo]

open Integration.ParetoOutcome in
/-- **Weld 5, instance.**  The scalar total does not determine the objective
vector, obtained from the collision owner; and no post-processing of the total
does either. -/
theorem weld_pareto_scalarisation :
    ¬ Determines total (fun a : Outcome 2 => a 0) ∧
      ∀ (W : Type) (g : ℕ → W), ¬ Determines (fun a => g (total a)) (fun a : Outcome 2 => a 0) :=
  ⟨paretoTotalCollision.not_determines, fun _ g => (paretoTotalCollision.post g).not_determines⟩

open Integration.ParetoOutcome in
/-- **Weld 5, non-descent.**  A strict decrease of the scalar total is not a
Pareto improvement: the two outcomes below are incomparable and the total
strictly orders them.  So minimising the scalar is not descent in the dominance
order. -/
theorem weld_scalar_descent_is_not_dominance :
    total (pair 1 1) < total (pair 0 3) ∧ ¬ Dominates (pair 1 1) (pair 0 3) ∧
      ¬ Dominates (pair 0 3) (pair 1 1) :=
  ⟨scalarisation_invents_order.2.2, scalarisation_invents_order.1,
    scalarisation_invents_order.2.1⟩

/-! ## Weld 6: selective decision → action/readout non-invertibility -/

open Integration.SelectiveDecision in
/-- **Weld 6, instance.**  The compiled action is not invertible, and its
non-invertibility is exactly the collision that refutes every readout of the
direction. -/
theorem weld_action_not_invertible : ¬ Function.Injective compileDecision :=
  compileCollision.projection_not_injective

open Integration.SelectiveDecision in
/-- And the corpus's own statement, re-derived from the owner rather than from a
bespoke witness. -/
theorem weld_action_readout : ¬ Determines compileDecision Decision.direction :=
  compileCollision.not_determines

/-! ## Weld 7: atlases → declared-carrier completeness -/

/-- An enumeration exhaustive of *the ambient type* is exhaustiveness evidence
for the carrier "belongs to the enumeration"; this is the arrow from the atlas
vocabulary to the adequacy owner's `Exhaustive`. -/
def exhaustiveOfList {X : Type} {l : List X} (h : ExhaustiveOn l (fun _ => True)) :
    Exhaustive (fun x : X => x ∈ l) := ⟨fun x => h x trivial⟩

/-- **Weld 7, bridge.**  An atlas gives a universal claim exactly when it
supplies exhaustiveness *evidence*: adequacy checked on the enumerated states
plus an `Exhaustive` record upgrades to adequacy outright.  The hypothesis is
the evidence, and the corpus atlases explicitly decline to supply it. -/
theorem weld_atlas_bridge {S R X : Type} {l : List S} {P : Pipeline S R X}
    {c : ConsumerSpec S X} (hadq : AdequateOn (fun s => s ∈ l) P c)
    (hex : ExhaustiveOn l (fun _ => True)) : AdequateFor P c :=
  adequate_of_adequateOn_exhaustive hadq (exhaustiveOfList hex)

/-- **Weld 7, negative.**  Without the evidence the upgrade fails, and a `Bool`
coverage flag is not the evidence: here is a declaration whose flag is set, whose
adequacy on the declared carrier holds, and whose global adequacy fails. -/
theorem weld_atlas_flag_is_not_evidence :
    ∃ d : CoverageDeclaration ℕ,
      d.claimsExhaustive = true ∧
        AdequateOn d.carrier faithfulPipeline parityConsumer ∧
        ¬ AdequateFor faithfulPipeline parityConsumer :=
  ⟨⟨small, true⟩, rfl, adequateOn_not_adequate.1, adequateOn_not_adequate.2⟩

/-! ## Weld 8: admissible reachability → language-relative reachability -/

/-- **Weld 8, identification.**  The corpus's counter system under a declared
language *is* the language-indexed reachability of the owner: the two agree for
every language and every pair of states.  So the corpus lane is an instance and
not an analogue. -/
theorem weld_counter_is_language_indexed (L : Bool → Prop) (x y : ℕ) :
    Integration.ReachabilityBarrier.Reachable
        (Integration.ReachabilityBarrier.counter L) x y ↔
      ReachableIn counterSystem L x y := by
  constructor
  · intro h
    exact Integration.ReachabilityBarrier.reachable_of_weaker_precondition
      (S := Integration.ReachabilityBarrier.counter L) (T := restrict counterSystem L)
      (fun _ a (hp : L a) => show L a ∧ True from ⟨hp, trivial⟩) (fun _ _ _ hq => hq) h
  · intro h
    exact Integration.ReachabilityBarrier.reachable_of_weaker_precondition
      (S := restrict counterSystem L) (T := Integration.ReachabilityBarrier.counter L)
      (fun _ a (hp : L a ∧ True) => show L a from hp.1) (fun _ _ _ hq => hq) h

/-- **Weld 8, positive.**  Language inclusion transports reachability upwards,
with the inclusion an explicit hypothesis. -/
theorem weld_reachability_monotone {L₁ L₂ : Bool → Prop} (hL : ∀ a, L₁ a → L₂ a)
    (x y : ℕ) (h : Integration.ReachabilityBarrier.Reachable
      (Integration.ReachabilityBarrier.counter L₁) x y) :
    Integration.ReachabilityBarrier.Reachable
      (Integration.ReachabilityBarrier.counter L₂) x y :=
  (weld_counter_is_language_indexed L₂ x y).mpr
    (reachableIn_mono hL ((weld_counter_is_language_indexed L₁ x y).mp h))

/-- **Weld 8, retained negative.**  Unreachability transports nowhere: the
general statement, quantified over all systems and all language inclusions, is
false. -/
theorem weld_unreachability_negative :
    ¬ (∀ (S : Integration.ReachabilityBarrier.ActionSystem ℕ Bool) (L₁ L₂ : Bool → Prop),
        (∀ a, L₁ a → L₂ a) → ∀ x y, ¬ ReachableIn S L₁ x y → ¬ ReachableIn S L₂ x y) :=
  unreachability_does_not_transfer

/-! ## The welds, collected -/

/-- **The seam, in one statement.**  Each conjunct is a domain-lane fact whose
proof above is an application of an owner, not a bespoke argument. -/
theorem welds_are_owner_applications :
    (¬ AdequateFor flatteningPipeline relationalConsumer) ∧
    (¬ RealisationAdequate compilePipeline directionConsumer) ∧
    (¬ Separable trajectory) ∧
    (¬ Determines (deleteCoord (A := fun _ : Fin 2 => Bool) 1) effectOfCoords) ∧
    (¬ Determines Integration.ParetoOutcome.total
      (fun a : Integration.ParetoOutcome.Outcome 2 => a 0)) ∧
    (¬ Function.Injective Integration.SelectiveDecision.compileDecision) ∧
    (¬ ReachableIn counterSystem evenOnly 0 3) ∧
    ReachableIn counterSystem allActions 0 3 :=
  ⟨weld_reconstruction_instance.2, weld_mediator_instance.2.1, weld_threshold_instance,
    weld_hidden_deletion, weld_pareto_scalarisation.1, weld_action_not_invertible,
    not_reachable_evenOnly, reachable_allActions⟩

end Integration.LevelIIWelds
