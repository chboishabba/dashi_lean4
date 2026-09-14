import Integration.PredictionEnvelope
import Integration.PromotionEvidence
import Integration.DeclaredCarrier

/-!
# Prediction status: propagate ideas freely, propagate certainty conservatively

`Integration.PredictionEnvelope` says *what* a prediction is when the evidence
does not pin a value.  This file says *how far it may travel and under what
label*.

## The discipline, in one line

A prediction's distance from its evidence may grow along a chain of steps; its
**status may weaken or stay equal, and may strengthen only when a step carries a
receipt** — the very `Receipt` object of `Integration.PromotionEvidence`, so a
strengthening step must present evidence rather than assert it.

`no_epistemic_laundering` is the theorem that matters: no receipt-free chain
starting from a speculative analogy ends at a model-conditional prediction.

## Contents

* `§1` the tiers, with `rank` read as **distance from evidence**, explicitly not
  as quality: a `speculativeAnalogy` is a legitimate research object, and the
  file proves it can carry a useful search prediction (`§4`);
* `§2` steps, propagation and the monotonicity law
  (`propagate_never_strengthens_without_receipt`, `chain_rank_monotone`,
  `no_epistemic_laundering`, `analogy_step_is_permanent_without_a_receipt`);
* `§3` support cones: a conclusion's status is *computed* from its chain, so the
  whole support is inspectable (`status_is_computed_not_declared`);
* `§4` search predictions: a negative result generates a *place to look*.  The
  precondition is proved **necessary and not sufficient**, which is exactly the
  epistemic content of "worth testing";
* `§5` the antipattern test battery: eight generic negative statements, each an
  instantiation of an existing owner, that a cross-domain proposal can be run
  against.  The historical names are prose labels; the theorems are about
  observation maps and consumers, and assert nothing historical or physical.

Nothing in this file is a claim about any physical, chemical, historical or
empirical subject matter.
-/

namespace Integration.PredictionStatus

open Integration.CoordinateSufficiency
open Integration.FactorisationCollision
open Integration.PredictionEnvelope
open Integration.PromotionEvidence
open Integration.PromotionDiscipline
open Integration.Levels

/-! ## §1 The tiers -/

/-- Epistemic role of a prediction.  These are **roles, not grades**: a
`speculativeAnalogy` is not a defective `provedConsequence`, it is a different
object with a different use. -/
inductive Tier
  /-- A proved consequence of stated premises. -/
  | provedConsequence
  /-- A consequence of a model, conditional on that model. -/
  | modelConditional
  /-- An extrapolation beyond the range where the model was checked. -/
  | empiricalExtrapolation
  /-- A conjecture motivated by structure. -/
  | structuralConjecture
  /-- A hypothesis suggested by analogy. -/
  | speculativeAnalogy
  deriving DecidableEq, Repr, Fintype

/-- **Distance from evidence.**  Not a quality score: it counts how much has to
be granted before the claim is licensed. -/
def Tier.rank : Tier → ℕ
  | .provedConsequence => 0
  | .modelConditional => 1
  | .empiricalExtrapolation => 2
  | .structuralConjecture => 3
  | .speculativeAnalogy => 4

/-- The weaker (further-from-evidence) of two tiers. -/
def maxTier (a b : Tier) : Tier := if a.rank ≤ b.rank then b else a

theorem le_maxTier_left (a b : Tier) : a.rank ≤ (maxTier a b).rank := by
  unfold maxTier; split <;> omega

theorem le_maxTier_right (a b : Tier) : b.rank ≤ (maxTier a b).rank := by
  unfold maxTier; split <;> omega

/-! ## §2 Steps and propagation -/

/-- Whether an evidence kind is hollow — a receipt of that kind is available to
every claim, so it cannot license a strengthening.  This is the same split the
promotion table makes. -/
def isHollow : EvidenceKind → Bool
  | .namingResemblance => true
  | .booleanCoverageDeclaration => true
  | .agdaTypecheckResult => true
  | _ => false

/-- The hollow kinds are exactly the kinds the promotion table licenses nothing
for — the two files agree on which evidence is empty. -/
theorem isHollow_iff_promotes_nothing (e : EvidenceKind) :
    isHollow e = true ↔ ∀ k : SewingTaxonomy.Kind, e.mayPromoteTo k = false := by
  constructor
  · intro h k; revert h; revert k; revert e; decide
  · intro h; revert h; revert e; decide

/-- A step a prediction can take on its way to a new context. -/
inductive Step : Type 1
  /-- A proved implication: the distance from evidence is unchanged. -/
  | formalImplication
  /-- The step is licensed only inside a model. -/
  | modelAssumption
  /-- The step leaves the checked range. -/
  | empiricalExtrapolation
  /-- The step is motivated by structure. -/
  | structuralArgument
  /-- The step is an analogy. -/
  | analogy
  /-- An independent receipt enters the chain, proposing a new tier. -/
  | receipt (e : EvidenceKind) (r : Receipt e) (proposed : Tier)

/-- Whether a step carries a receipt with content. -/
def Step.isStrengthening : Step → Bool
  | .receipt e _ _ => !isHollow e
  | _ => false

/-- **Propagation.**  Every non-receipt step can only move the claim further
from its evidence; a receipt step may set the tier, but only if the receipt is
not hollow. -/
def propagate : Tier → Step → Tier
  | t, .formalImplication => t
  | t, .modelAssumption => maxTier t .modelConditional
  | t, .empiricalExtrapolation => maxTier t .empiricalExtrapolation
  | t, .structuralArgument => maxTier t .structuralConjecture
  | t, .analogy => maxTier t .speculativeAnalogy
  | t, .receipt e _ proposed => if isHollow e then t else proposed

/-- **The monotonicity law.**  Without a receipt, distance from evidence never
decreases: status can stay equal or weaken, never strengthen automatically. -/
theorem propagate_never_strengthens_without_receipt (t : Tier) (s : Step)
    (h : s.isStrengthening = false) : t.rank ≤ (propagate t s).rank := by
  cases s with
  | formalImplication => exact le_of_eq rfl
  | modelAssumption => exact le_maxTier_left _ _
  | empiricalExtrapolation => exact le_maxTier_left _ _
  | structuralArgument => exact le_maxTier_left _ _
  | analogy => exact le_maxTier_left _ _
  | receipt e r p =>
    simp only [Step.isStrengthening, Bool.not_eq_false'] at h
    simp only [propagate, if_pos h]
    exact le_refl _

/-- **A hollow receipt is not a strengthening.**  Presenting a name, a Boolean
coverage flag or a checker result leaves the status exactly where it was. -/
theorem hollow_receipt_is_a_no_op (t : Tier) (e : EvidenceKind) (r : Receipt e)
    (h : isHollow e = true) : propagate t (.receipt e r .provedConsequence) = t := by
  simp [propagate, h]

/-- Propagation along a chain of steps. -/
def chain (t : Tier) (ss : List Step) : Tier := ss.foldl propagate t

@[simp] theorem chain_nil (t : Tier) : chain t [] = t := rfl

@[simp] theorem chain_cons (t : Tier) (s : Step) (ss : List Step) :
    chain t (s :: ss) = chain (propagate t s) ss := rfl

theorem chain_append (t : Tier) (a b : List Step) :
    chain t (a ++ b) = chain (chain t a) b := List.foldl_append

/-- **The chain law.**  A receipt-free chain never brings a claim closer to its
evidence, however many steps it takes. -/
theorem chain_rank_monotone (t : Tier) (ss : List Step)
    (h : ∀ s ∈ ss, s.isStrengthening = false) : t.rank ≤ (chain t ss).rank := by
  induction ss generalizing t with
  | nil => exact le_of_eq rfl
  | cons s ss ih =>
    refine le_trans (propagate_never_strengthens_without_receipt t s (h s (by simp))) ?_
    exact ih _ (fun s' hs' => h s' (by simp [hs']))

/-- **No epistemic laundering.**  A speculative analogy cannot become a
model-conditional prediction by any receipt-free chain of steps, of any length.
Speculation is allowed to travel; it is not allowed to arrive relabelled. -/
theorem no_epistemic_laundering (ss : List Step)
    (h : ∀ s ∈ ss, s.isStrengthening = false) :
    chain .speculativeAnalogy ss ≠ .modelConditional := by
  intro hc
  have := chain_rank_monotone .speculativeAnalogy ss h
  rw [hc] at this
  simp [Tier.rank] at this

/-- The same for the strongest tier: nothing receipt-free ever ends at
`provedConsequence` unless it began there. -/
theorem no_receipt_free_route_to_proof (t : Tier) (ss : List Step)
    (h : ∀ s ∈ ss, s.isStrengthening = false)
    (hc : chain t ss = .provedConsequence) : t = .provedConsequence := by
  have := chain_rank_monotone t ss h
  rw [hc] at this
  cases t <;> simp [Tier.rank] at this ⊢

/-- **An analogy step is permanent without a receipt.**  Once a chain passes
through an analogy, every later receipt-free step keeps it at the analogy
tier. -/
theorem analogy_step_is_permanent_without_a_receipt (t : Tier) (pre post : List Step)
    (h : ∀ s ∈ post, s.isStrengthening = false) :
    4 ≤ (chain t (pre ++ .analogy :: post)).rank := by
  rw [chain_append, chain_cons]
  refine le_trans ?_ (chain_rank_monotone _ post h)
  have hstep : propagate (chain t pre) .analogy = maxTier (chain t pre) .speculativeAnalogy := rfl
  rw [hstep]
  calc (4 : ℕ) = Tier.rank .speculativeAnalogy := rfl
    _ ≤ (maxTier (chain t pre) .speculativeAnalogy).rank := le_maxTier_right _ _

/-- **And a genuine receipt may strengthen.**  The discipline is not uniformly
negative: a non-hollow receipt — here the corpus's decided enumeration — sets
the tier it licenses. -/
theorem receipt_may_strengthen :
    propagate .speculativeAnalogy
      (.receipt .enumerationCompleteness sspEnumerationReceipt .provedConsequence) =
      .provedConsequence := rfl

/-! ## §3 Support cones -/

/-- A prediction, carried with its support: where it started and every step it
took.  The status is not a field — it is computed. -/
structure SupportedPrediction : Type 1 where
  /-- The tier of the claim the chain starts from. -/
  origin : Tier
  /-- The steps taken, in order. -/
  steps : List Step

/-- The status of a supported prediction. -/
def SupportedPrediction.status (p : SupportedPrediction) : Tier := chain p.origin p.steps

/-- **Status is computed, not declared.**  Two predictions with the same support
cone have the same status, so the label cannot be set independently of the
chain. -/
theorem status_is_computed_not_declared (p q : SupportedPrediction)
    (ho : p.origin = q.origin) (hs : p.steps = q.steps) : p.status = q.status := by
  simp [SupportedPrediction.status, ho, hs]

/-- **The support cone is load-bearing.**  Deleting a step can change the
status, so the chain may not be summarised away: here dropping the analogy turns
a speculative claim into a proved one. -/
theorem dropping_a_step_changes_the_status :
    ({ origin := .provedConsequence, steps := [.analogy] } : SupportedPrediction).status ≠
      ({ origin := .provedConsequence, steps := [] } : SupportedPrediction).status := by
  decide

/-- A failed prediction does not annihilate its support cone: the steps remain
available for inspection, and only the assumptions the failure actually depends
on are impugned.  Formally: two predictions can share an origin and diverge, so
refuting one does not refute the other. -/
theorem refutation_does_not_reject_the_whole_cone :
    ∃ p q : SupportedPrediction,
      p.origin = q.origin ∧ p.status ≠ q.status := by
  refine ⟨{ origin := .provedConsequence, steps := [.analogy] },
    { origin := .provedConsequence, steps := [] }, rfl, ?_⟩
  decide

/-! ## §4 Search predictions -/

/-- **A search prediction.**  A structural precondition on a representation, and
the phenomenon it makes worth testing.  It asserts neither that the phenomenon
occurs nor that it does not. -/
structure SearchPrediction (X Y Z : Type) where
  /-- The structural configuration to look for. -/
  precondition : (X → Y) → Prop
  /-- The phenomenon to test for once the configuration is found. -/
  phenomenon : (X → Y) → (X → Z) → Prop

/-- The canonical search prediction generated by the collision owner: *where an
observation is non-injective, look for a consumer it separates.* -/
def collisionSearch (X Y Z : Type) : SearchPrediction X Y Z where
  precondition := fun O => ¬ Function.Injective O
  phenomenon := fun O C => Nonempty (Collision O C)

/-- **The precondition is necessary.**  Searching where it fails is wasted
work: an injective representation has no collisions at all. -/
theorem search_precondition_is_necessary {X Y Z : Type} {O : X → Y} {C : X → Z}
    (h : Nonempty (Collision O C)) : ¬ Function.Injective O :=
  h.elim (fun w => w.projection_not_injective)

/-- **And not sufficient.**  The same non-injective representation has a
colliding consumer and a non-colliding one, so the search prediction is a place
to look and not a claim that the phenomenon is there. -/
theorem search_precondition_is_not_sufficient :
    ∃ (O : ℕ → ℕ) (C₁ C₂ : ℕ → ℕ),
      ¬ Function.Injective O ∧ Nonempty (Collision O C₁) ∧ ¬ Nonempty (Collision O C₂) := by
  refine ⟨fun n => n % 2, id, fun n => n % 2, ?_, ⟨?_⟩, ?_⟩
  · intro h
    have : (0 : ℕ) = 2 := h (by norm_num)
    omega
  · exact { left := 0, right := 2, distinct := by omega, collide := rfl,
            separate := by simp }
  · rintro ⟨w⟩
    exact w.separate w.collide

/-- Consequently a search prediction is exactly a `structuralConjecture`-tier
object: it is generated by a proved negative, and it takes a receipt to move it
anywhere else. -/
theorem search_prediction_tier :
    propagate .provedConsequence .structuralArgument = .structuralConjecture := rfl

/-! ## §5 The antipattern test battery -/

/-- **Test 1 (resemblance is not identity).**  Two carriers can satisfy the same
shape predicate with no map between them, so a shared shape — a fortiori a
shared name — is not an identification. -/
theorem resemblance_is_not_identity : IsEmpty (Transport Unit Bool id id) :=
  shared_shape_gives_no_transport_structure

/-- **Test 2 (encoding is not explanation).**  A representation can be produced
by two different mechanisms, so exhibiting the representation does not identify
the mechanism that generates it. -/
theorem encoding_does_not_identify_mechanism :
    ∃ (O : ℕ → ℕ) (f g : ℕ → ℕ), f ≠ g ∧ ∀ x, O (f x) = O (g x) := by
  refine ⟨fun n => n % 2, id, fun n => n + 2, ?_, fun x => by show x % 2 = (x + 2) % 2; omega⟩
  intro h
  have : (0 : ℕ) = 0 + 2 := congrFun h 0
  omega

/-- **Test 3 (local success does not globalise).**  Determination on a declared
carrier does not give determination outright: a model complete in its own chart
licenses nothing outside it. -/
theorem local_success_does_not_globalise :
    Integration.DeclaredCarrier.DeterminesOn Integration.DeclaredCarrier.declared
        (fun n : ℕ => n % 2) (fun n : ℕ => n) ∧
      ¬ Determines (fun n : ℕ => n % 2) (fun n : ℕ => n) :=
  Integration.DeclaredCarrier.determinesOn_not_determines

/-- **Test 4 (recovering the established phenomena).**  A proposal must
determine the quantities already known; if it collides on one of them, no
downstream reading repairs that. -/
theorem must_recover_known_quantities {X Y Z : Type} {O : X → Y} {C : X → Z}
    (w : Collision O C) (f : Y → Z) : ¬ ∀ x, C x = f (O x) :=
  w.no_reading f

/-- **Test 5 (identifiability).**  A framework identifies the world for a
quantity exactly when every prediction envelope is a point; a wide envelope is
the precise form of "too many admissible realisations". -/
theorem identifiability_is_envelope_width {X Y Z : Type} (O : X → Y) (C : X → Z) :
    Determines O C ↔ ∀ y, (Pred O C y).Subsingleton :=
  determines_iff_envelope_subsingleton O C

/-- **Test 6 (out-of-sample content).**  Two models agreeing on the fitting data
can disagree outside it, so a measurement outside the data discriminates them:
this is what makes a prediction risky. -/
theorem out_of_sample_measurement_discriminates {X Z : Type} {D : X → Prop}
    {m₁ m₂ : X → Z} (hfit : ∀ x, D x → m₁ x = m₂ x) {x₀ : X}
    (hne : m₁ x₀ ≠ m₂ x₀) : (∀ x, D x → m₁ x = m₂ x) ∧ ¬ ∀ x, m₁ x = m₂ x :=
  ⟨hfit, fun h => absurd (h x₀) (by simpa using hne)⟩

/-- **Test 7 (scope).**  Adequacy is consumer-relative: a representation
sufficient for one question can fail another, so a scope claim must name its
consumer. -/
theorem scope_must_name_the_consumer :
    ∃ (O : ℕ → ℕ) (C₁ C₂ : ℕ → ℕ), Determines O C₁ ∧ ¬ Determines O C₂ :=
  ⟨fun n => n % 2, fun n => n % 2, id, fun _ _ h => h, by
    intro h; have : (0 : ℕ) = 2 := h 0 2 rfl; omega⟩

/-- **Test 8 (a failed interpretation is not a failed structure).**  Rejecting a
claim does not reject everything derived alongside it: sharing an origin, two
predictions can have different statuses, so a refutation must be traced through
the support cone rather than applied to the whole cone. -/
theorem rejection_does_not_propagate_to_the_cone :
    ∃ p q : SupportedPrediction, p.origin = q.origin ∧ p.status ≠ q.status :=
  refutation_does_not_reject_the_whole_cone

end Integration.PredictionStatus
