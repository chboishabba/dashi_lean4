import Integration.Kernel.Quotient

/-!
# Declared state and realised state

Four lanes of this corpus keep separating the same two things under different
names: an order and the world after it, a transition emitted and a transition
executed, a nominal input condition and the local state it actually produces, a
claimed status and an inhabiting term.  This file gives that motif one owner.

The chain modelled here is

```
declared  →  authorised  →  acknowledged  →  realised  →  consumer's outcome test
```

and the content is that **no link in it is automatic**: each coordinate can
agree while the next differs.  `Integration.Kernel.Instances.SourceStage`
already owns the proof-system end of the same motif (`flag = true` is not an
attached witness); this file owns the execution end, generically.

## What is proved

* **`no_link_of_the_chain_is_automatic`** — collected form of the four
  non-descents `authorised_does_not_descend_through_declared`,
  `acknowledged_does_not_descend_through_authorised`,
  `realised_does_not_descend_through_acknowledged` and
  `declared_does_not_descend_through_realised`.  Each is an instance of
  `Integration.Kernel.Quotient.not_descendsThrough_of_collision` with an
  explicit pair of episodes.
* **`Receipt`** — what does close the gap: a structure carrying *proofs* that
  the step was acknowledged and that the observed state is the target one.
  `Receipt.determines_realised` is its payoff, and
  `acknowledgement_alone_is_not_a_receipt` is the negative that makes it
  non-trivial.
* **`success_is_not_a_function_of_the_world`** — the coordinate the legal lane
  contributes and the runtime lane lacks: the outcome test belongs to the
  consumer, so two consumers reading the *same* realised state disagree about
  whether the remedy closed.  `success_descends_through_pair` says the
  (state, criterion) pair is the right index, exactly as in
  `Integration.Kernel.QueryResidual`.
* `episode_is_the_join` — the four coordinates together do determine the
  episode, so the chain is a genuine refinement tower and not a
  contradiction.

**Claim boundary.**  An `Episode` is four Booleans introduced here.  Nothing is
claimed about any real order, remedy, execution engine or physical process; the
theorems are about which coordinate is a function of which.
-/

namespace Integration.Kernel.DeclaredRealised

open Integration.Kernel.Quotient

/-! ## §1 The chain -/

/-- One pass through the chain, as four independent Boolean coordinates. -/
structure Episode : Type where
  /-- The step was ordered or announced. -/
  declared : Bool
  /-- An implementation was actually authorised. -/
  authorised : Bool
  /-- The execution was acknowledged. -/
  acknowledged : Bool
  /-- The world was observed in the target state. -/
  realised : Bool
  deriving DecidableEq, Repr

/-- Declared, and nothing else. -/
def declaredOnly : Episode := ⟨true, false, false, false⟩

/-- Declared and authorised, but never acknowledged. -/
def authorisedOnly : Episode := ⟨true, true, false, false⟩

/-- Acknowledged, yet the world is not in the target state. -/
def acknowledgedNotRealised : Episode := ⟨true, true, true, false⟩

/-- The complete chain. -/
def fullyRealised : Episode := ⟨true, true, true, true⟩

/-- Realised without ever having been declared. -/
def realisedUndeclared : Episode := ⟨false, false, false, true⟩

/-! ## §2 No link of the chain is automatic -/

/-- Declaring does not authorise. -/
theorem authorised_does_not_descend_through_declared :
    ¬ DescendsThrough Episode.authorised Episode.declared :=
  not_descendsThrough_of_collision (x := declaredOnly) (y := authorisedOnly) rfl (by decide)

/-- Authorising does not execute. -/
theorem acknowledged_does_not_descend_through_authorised :
    ¬ DescendsThrough Episode.acknowledged Episode.authorised :=
  not_descendsThrough_of_collision (x := authorisedOnly) (y := acknowledgedNotRealised) rfl
    (by decide)

/-- **An execution acknowledgement is not an observed outcome.** -/
theorem realised_does_not_descend_through_acknowledged :
    ¬ DescendsThrough Episode.realised Episode.acknowledged :=
  not_descendsThrough_of_collision (x := acknowledgedNotRealised) (y := fullyRealised) rfl
    (by decide)

/-- And the chain does not run backwards either: a realised state does not
witness that it was declared. -/
theorem declared_does_not_descend_through_realised :
    ¬ DescendsThrough Episode.declared Episode.realised :=
  not_descendsThrough_of_collision (x := fullyRealised) (y := realisedUndeclared) rfl (by decide)

/-- The motif, collected. -/
theorem no_link_of_the_chain_is_automatic :
    ¬ DescendsThrough Episode.authorised Episode.declared ∧
      ¬ DescendsThrough Episode.acknowledged Episode.authorised ∧
        ¬ DescendsThrough Episode.realised Episode.acknowledged ∧
          ¬ DescendsThrough Episode.declared Episode.realised :=
  ⟨authorised_does_not_descend_through_declared,
    acknowledged_does_not_descend_through_authorised,
    realised_does_not_descend_through_acknowledged,
    declared_does_not_descend_through_realised⟩

/-- The four coordinates together *do* determine the episode: the chain is a
refinement tower, so recording execution does not retract the declaration. -/
theorem episode_is_the_join {e f : Episode} (hd : e.declared = f.declared)
    (ha : e.authorised = f.authorised) (hk : e.acknowledged = f.acknowledged)
    (hr : e.realised = f.realised) : e = f := by
  cases e; cases f; simp_all

/-! ## §3 What does close the gap -/

/-- An execution receipt: proofs, not flags. -/
structure Receipt (target : Bool) : Type where
  /-- The episode being certified. -/
  episode : Episode
  /-- The execution really was acknowledged. -/
  acknowledged : episode.acknowledged = true
  /-- And the world really was observed in the target state. -/
  observed : episode.realised = target

/-- A receipt determines the realised state; that is the whole point of asking
for one. -/
theorem Receipt.determines_realised {target : Bool} (r : Receipt target) :
    r.episode.realised = target := r.observed

/-- **The acknowledgement alone is not a receipt.**  There is an acknowledged
episode whose realised state is not the target, so the acknowledgement cannot be
promoted to the observation. -/
theorem acknowledgement_alone_is_not_a_receipt :
    acknowledgedNotRealised.acknowledged = true ∧ acknowledgedNotRealised.realised ≠ true :=
  ⟨rfl, by decide⟩

/-- A receipt for the target state is available exactly when such an episode
exists — nothing here manufactures one. -/
theorem receipt_exists_iff :
    Nonempty (Receipt true) ↔ ∃ e : Episode, e.acknowledged = true ∧ e.realised = true := by
  constructor
  · rintro ⟨r⟩
    exact ⟨r.episode, r.acknowledged, r.observed⟩
  · rintro ⟨e, hk, hr⟩
    exact ⟨⟨e, hk, hr⟩⟩

/-! ## §4 The outcome test belongs to the consumer -/

/-- Whether the episode counts as a success, according to a criterion supplied
by whoever is affected. -/
def succeeds (crit : Episode → Bool) (e : Episode) : Bool := crit e

/-- Criterion A: the step was acknowledged. -/
def acknowledgementCriterion : Episode → Bool := Episode.acknowledged

/-- Criterion B: the world is in the target state. -/
def realisedCriterion : Episode → Bool := Episode.realised

/-- **Success is not a function of the world state alone.**  On the same
episode, one consumer's criterion reports success and another's does not, so
"closed" is a property of the (state, criterion) pair. -/
theorem success_is_not_a_function_of_the_world :
    succeeds acknowledgementCriterion acknowledgedNotRealised = true ∧
      succeeds realisedCriterion acknowledgedNotRealised = false :=
  ⟨rfl, rfl⟩

/-- Stated as a non-descent: forgetting whose criterion is being applied
destroys the verdict. -/
theorem success_does_not_descend_through_episode :
    ¬ DescendsThrough
        (fun p : (Episode → Bool) × Episode => succeeds p.1 p.2)
        (fun p : (Episode → Bool) × Episode => p.2) :=
  not_descendsThrough_of_collision
    (x := (acknowledgementCriterion, acknowledgedNotRealised))
    (y := (realisedCriterion, acknowledgedNotRealised)) rfl (by decide)

/-- The pair is the right index. -/
theorem success_descends_through_pair :
    DescendsThrough
      (fun p : (Episode → Bool) × Episode => succeeds p.1 p.2)
      (fun p : (Episode → Bool) × Episode => p) :=
  ⟨fun p => succeeds p.1 p.2, fun _ => rfl⟩

end Integration.Kernel.DeclaredRealised
