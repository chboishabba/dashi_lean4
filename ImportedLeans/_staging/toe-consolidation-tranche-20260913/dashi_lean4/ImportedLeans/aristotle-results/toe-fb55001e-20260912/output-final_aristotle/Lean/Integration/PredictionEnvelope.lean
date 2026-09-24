import Integration.ClaimTransportGeometry

/-!
# Prediction envelopes: what the evidence leaves open

The determination owner answers a yes/no question: does the observation `O`
fix the consumer's quantity `C`?  When the answer is *no*, the corpus so far
records a `Collision` and stops.  This file takes the constructive step: when
determination fails, the honest output is not silence but a **set**,

```
Pred O C y = { C x | O x = y }
```

the set of values of the predicted quantity across the fibre of the evidence.

## The organising theorem

`determines_iff_envelope_subsingleton` — `Determines O C` holds **iff** every
envelope has at most one element.  So the existing determination/factorisation
theory *is* the theory of point-identifiable predictions, and set-valued
prediction is its proper generalisation rather than a new layer.  No new owner
is introduced: everything below is stated with `Determines`, `Factors` and
`Collision`.

## Contents

* `§1` the envelope, its inhabitants, and the organising theorem;
* `§2` **tightening**: finer evidence never widens an envelope
  (`refinement_narrows_envelope`), adjoining a second measurement contracts it
  (`joint_evidence_contracts`), and the contraction can be strict;
* `§3` when a point prediction is impossible: a collision gives a two-element
  envelope, and **no downstream algorithm on this representation** recovers the
  quantity (`no_algorithm_recovers_from_this_representation`);
* `§4` **relational and impossibility predictions**: a comparison can be
  determined when neither of its sides is, and "aggregation must erase a
  consumer-relevant distinction" is a theorem about cardinality, not a slogan;
* `§5` **which extra measurement to take**: a coordinate that separates a
  colliding pair is exactly what turns the envelope into a point.

Every carrier is `ℕ`, `Bool`, `ℚ` or an arbitrary type.  Nothing here is a
claim about any physical, chemical or empirical system: the objects are
observation maps and consumers.
-/

namespace Integration.PredictionEnvelope

open Integration.CoordinateSufficiency
open Integration.FactorisationCollision
open Integration.ClaimTransportGeometry

variable {X Y Z W : Type}

/-! ## §1 The envelope -/

/-- **The prediction envelope.**  Given evidence `O` reading value `y`, the set
of values the predicted quantity `C` can take across the states compatible with
that reading. -/
def Pred (O : X → Y) (C : X → Z) (y : Y) : Set Z := {z | ∃ x, O x = y ∧ C x = z}

/-- Every state contributes its own prediction to the envelope of its
reading. -/
theorem mem_envelope_self (O : X → Y) (C : X → Z) (x : X) : C x ∈ Pred O C (O x) :=
  ⟨x, rfl, rfl⟩

/-- The envelope is nonempty exactly when the reading is realisable. -/
theorem envelope_nonempty_iff (O : X → Y) (C : X → Z) (y : Y) :
    (Pred O C y).Nonempty ↔ ∃ x, O x = y := by
  constructor
  · rintro ⟨z, x, hx, -⟩; exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩; exact ⟨C x, x, hx, rfl⟩

/-- **The organising theorem.**  The evidence determines the quantity exactly
when every envelope is at most a point.  Determination theory is
point-identifiability; the envelope is what remains when it fails. -/
theorem determines_iff_envelope_subsingleton (O : X → Y) (C : X → Z) :
    Determines O C ↔ ∀ y, (Pred O C y).Subsingleton := by
  constructor
  · rintro h y z₁ ⟨x₁, hx₁, rfl⟩ z₂ ⟨x₂, hx₂, rfl⟩
    exact h x₁ x₂ (hx₁.trans hx₂.symm)
  · intro h x₁ x₂ hx
    exact h (O x₁) (mem_envelope_self O C x₁) ⟨x₂, hx.symm, rfl⟩

/-- The same statement in factorisation form, via the transport geometry. -/
theorem factors_iff_envelope_subsingleton [Nonempty Z] (O : X → Y) (C : X → Z) :
    Factors O C ↔ ∀ y, (Pred O C y).Subsingleton :=
  (factors_iff_determines O C).trans (determines_iff_envelope_subsingleton O C)

/-- When the quantity *is* determined, the envelope of a realised reading is the
singleton of the predicted value. -/
theorem envelope_eq_singleton_of_determines {O : X → Y} {C : X → Z}
    (h : Determines O C) (x : X) : Pred O C (O x) = {C x} := by
  ext z
  constructor
  · rintro ⟨x', hx', rfl⟩; exact (h x' x hx').symm ▸ rfl
  · rintro rfl; exact mem_envelope_self O C x

/-! ## §2 Tightening: more evidence never widens the envelope -/

/-- **Refinement narrows.**  If the finer evidence `O₂` determines the coarser
evidence `O₁`, then the envelope computed from `O₂` is contained in the one
computed from `O₁`.  Prediction sets contract as evidence refines; they never
widen. -/
theorem refinement_narrows_envelope {O₁ : X → Y} {O₂ : X → W} {C : X → Z}
    (href : Determines O₂ O₁) (x : X) :
    Pred O₂ C (O₂ x) ⊆ Pred O₁ C (O₁ x) := by
  rintro z ⟨x', hx', rfl⟩
  exact ⟨x', href x' x hx', rfl⟩

/-- **Adjoining a measurement contracts.**  The envelope from the joint reading
`(O₁, O₂)` is inside the envelope from `O₁` alone. -/
theorem joint_evidence_contracts (O₁ : X → Y) (O₂ : X → W) (C : X → Z) (x : X) :
    Pred (fun x => (O₁ x, O₂ x)) C (O₁ x, O₂ x) ⊆ Pred O₁ C (O₁ x) := by
  rintro z ⟨x', hx', rfl⟩
  exact ⟨x', congrArg Prod.fst hx', rfl⟩

/-- **And the contraction can be strict.**  With `O₁` constant the envelope is
everything the quantity can be; the joint reading with the quantity itself
collapses it to a point. -/
theorem contraction_can_be_strict :
    Pred (fun _ : ℕ => ()) (id : ℕ → ℕ) () = Set.univ ∧
      Pred (fun n : ℕ => ((), n)) (id : ℕ → ℕ) ((), 0) = {0} := by
  constructor
  · ext z; exact ⟨fun _ => trivial, fun _ => ⟨z, rfl, rfl⟩⟩
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (congrArg Prod.snd hx)
    · rintro rfl; exact ⟨0, rfl, rfl⟩

/-- Envelope containment transfers along a post-processing of the quantity: a
derived quantity's envelope is the image of the envelope. -/
theorem envelope_image (O : X → Y) (C : X → Z) (g : Z → W) (y : Y) :
    Pred O (fun x => g (C x)) y = g '' Pred O C y := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨C x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩

/-! ## §3 When no point prediction exists -/

/-- **A collision is a two-element envelope.**  The obstruction to a point
prediction is the existing datum, and what it produces is an envelope with two
distinct members. -/
theorem envelope_not_subsingleton_of_collision {O : X → Y} {C : X → Z}
    (w : Collision O C) : ¬ (Pred O C (O w.left)).Subsingleton := by
  intro h
  exact w.separate (h (mem_envelope_self O C w.left) ⟨w.right, w.collide.symm, rfl⟩)

/-- Conversely, a non-subsingleton envelope is a collision. -/
theorem collision_of_envelope_not_subsingleton {O : X → Y} {C : X → Z} {y : Y}
    (h : ¬ (Pred O C y).Subsingleton) : Nonempty (Collision O C) := by
  refine nonempty_collision_of_not_determines ?_
  intro hd
  exact h ((determines_iff_envelope_subsingleton O C).mp hd y)

/-- **A structural impossibility prediction.**  Once a collision exists, *no*
downstream algorithm reading only this representation recovers the quantity —
not merely the ones tried.  This is the strongest kind of prediction an abstract
analysis can emit, and it is a theorem. -/
theorem no_algorithm_recovers_from_this_representation {O : X → Y} {C : X → Z}
    (w : Collision O C) (f : Y → Z) : ¬ ∀ x, C x = f (O x) :=
  w.no_reading f

/-- The same conclusion for every *post-processing* of the representation: no
further deterministic transformation of `O` repairs it either. -/
theorem no_post_processing_repairs {O : X → Y} {C : X → Z} (w : Collision O C)
    (g : Y → W) : ¬ Determines (fun x => g (O x)) C :=
  (w.post g).not_determines

/-! ## §4 Relational and impossibility predictions -/

/-- **A comparison can be predicted when neither side is.**  The evidence here
fixes no value of either quantity, yet the relation between them is determined:
a genuine prediction that is not a number. -/
theorem relational_prediction_without_point_prediction :
    ∃ (O : ℕ → Unit) (a b : ℕ → ℕ),
      Determines O (fun x => decide (a x < b x)) ∧ ¬ Determines O a ∧ ¬ Determines O b := by
  refine ⟨fun _ => (), id, fun n => n + 1, ?_, ?_, ?_⟩
  · intro x y _
    simp
  · intro h; have : (0 : ℕ) = 1 := h 0 1 rfl; omega
  · intro h; have : (0 : ℕ) + 1 = 1 + 1 := h 0 1 rfl; omega

/-- **Aggregation must erase a consumer-relevant distinction**, whenever the
readings are fewer than the states.  This is an impossibility prediction proved
by counting: it applies to every aggregation of that shape, before any
particular consumer is chosen. -/
theorem aggregation_must_erase {X Y : Type} [Fintype X] [Fintype Y]
    (O : X → Y) (h : Fintype.card Y < Fintype.card X) : ¬ Function.Injective O :=
  fun hinj => absurd (Fintype.card_le_of_injective O hinj) (by omega)

/-- Hence, for any consumer that separates the erased pair, the envelope is not
a point — the failure is predicted from the shape of the representation alone. -/
theorem envelope_wide_of_undersized_representation {X Y : Type} [Fintype X] [Fintype Y]
    (O : X → Y) (h : Fintype.card Y < Fintype.card X) :
    ∃ x₁ x₂ : X, x₁ ≠ x₂ ∧ O x₁ = O x₂ := by
  have hni := aggregation_must_erase O h
  simp only [Function.Injective, not_forall] at hni
  obtain ⟨x₁, x₂, hx, hne⟩ := hni
  exact ⟨x₁, x₂, hne, hx⟩

/-! ## §5 Which extra measurement to take -/

/-- **The measurement that closes the envelope.**  If a further coordinate `M`
separates the colliding pair, the joint reading no longer collides on it: the
negative result names the experiment that would remove the ambiguity. -/
theorem separating_measurement_breaks_the_collision {O : X → Y} {C : X → Z} {M : X → W}
    (w : Collision O C) (hsep : M w.left ≠ M w.right) :
    (fun x => (O x, M x)) w.left ≠ (fun x => (O x, M x)) w.right :=
  fun h => hsep (congrArg Prod.snd h)

/-- And a coordinate that does *not* separate the pair leaves the envelope
exactly as wide: adjoining it is not an experiment. -/
def non_separating_measurement_changes_nothing {O : X → Y} {C : X → Z} {M : X → W}
    (w : Collision O C) (hno : M w.left = M w.right) :
    Collision (fun x => (O x, M x)) C where
  left := w.left
  right := w.right
  distinct := w.distinct
  collide := by rw [w.collide, hno]
  separate := w.separate

/-- The two together are the search prediction attached to a collision: *measure
a coordinate that separates these two states*, and nothing weaker will do. -/
theorem experiment_must_separate_the_pair {O : X → Y} {C : X → Z} {M : X → W}
    (w : Collision O C) :
    (M w.left ≠ M w.right) ∨ ¬ Determines (fun x => (O x, M x)) C := by
  by_cases h : M w.left = M w.right
  · exact Or.inr (non_separating_measurement_changes_nothing w h).not_determines
  · exact Or.inl h

end Integration.PredictionEnvelope
