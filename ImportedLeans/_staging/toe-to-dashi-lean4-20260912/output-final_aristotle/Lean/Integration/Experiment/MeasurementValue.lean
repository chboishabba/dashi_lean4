import Integration.Experiment.Risk

/-!
# Lane 5 — measurement-value analysis

Given a wide envelope, which additional measurement contracts it most?  On a
finite state space the question has an exact answer, and this file computes it.

## The measure

`ambiguity O C` counts the ordered pairs of states the instruments `O` identify
and the consumer `C` separates — the collisions of the existing owner, counted.
Then:

* `ambiguity_eq_zero_iff_determines` — zero ambiguity **is** determination, so
  the score is not a heuristic proxy for the structural question but the same
  question counted;
* `ambiguity_join_le` — adjoining a sensor never increases ambiguity (evidence
  never widens an envelope, in counted form);
* `bestSensor` / `bestSensor_minimal` — the recommended next measurement is the
  candidate minimising the residual ambiguity, and it is proved minimal among
  the declared candidates;
* `bestSensor_resolves_iff_some_candidate_resolves` — the recommendation
  resolves the question exactly when some declared candidate does, so the
  procedure never misses an adequate sensor and never invents one;
* `best_sensor_depends_on_the_question` — the honest negative: the ranking is
  relative to the consumer, so a "most informative sensor" claim must name the
  question it is informative for.

Everything is over a finite state space with decidable equality; the sensors are
functions into a type with decidable equality.  No claim is made about any
physical instrument.
-/

namespace Integration.Experiment.MeasurementValue

open Integration.CoordinateSufficiency
open Integration.FactorisationCollision
open Integration.ClaimTransportGeometry

variable {X Y Z W : Type} [Fintype X] [DecidableEq Y] [DecidableEq Z]

/-! ## §1 Counting the residual ambiguity -/

/-- The ordered pairs of states that `O` confuses and `C` distinguishes. -/
def ambiguousPairs (O : X → Y) (C : X → Z) : Finset (X × X) :=
  (Finset.univ : Finset (X × X)).filter (fun p => O p.1 = O p.2 ∧ C p.1 ≠ C p.2)

/-- **The score**: how much consumer-relevant ambiguity the instruments leave. -/
def ambiguity (O : X → Y) (C : X → Z) : ℕ := (ambiguousPairs O C).card

/-- **Zero ambiguity is determination.**  The score is the determination
question, counted. -/
theorem ambiguity_eq_zero_iff_determines (O : X → Y) (C : X → Z) :
    ambiguity O C = 0 ↔ Determines O C := by
  unfold ambiguity ambiguousPairs
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h x y hxy
    by_contra hne
    exact (h (Finset.mem_univ (x, y))) ⟨hxy, hne⟩
  · rintro h ⟨x, y⟩ - ⟨hxy, hne⟩
    exact hne (h x y hxy)

/-- A positive score exhibits an actual collision. -/
theorem collision_of_ambiguity_pos {O : X → Y} {C : X → Z} (h : 0 < ambiguity O C) :
    Nonempty (Collision O C) := by
  have hne : ambiguity O C ≠ 0 := by omega
  rw [Ne, ambiguity_eq_zero_iff_determines] at hne
  exact nonempty_collision_of_not_determines hne

/-! ## §2 Adjoining a sensor -/

/-- The joint reading of the current instruments and a candidate sensor. -/
def joint (O : X → Y) (M : X → W) : X → Y × W := fun x => (O x, M x)

/-- **A sensor never widens the envelope**: the ambiguity of the joint reading
is at most the ambiguity of the instruments alone. -/
theorem ambiguity_join_le [DecidableEq W] (O : X → Y) (M : X → W) (C : X → Z) :
    ambiguity (joint O M) C ≤ ambiguity O C := by
  refine Finset.card_le_card ?_
  intro p hp
  simp only [ambiguousPairs, Finset.mem_filter, Finset.mem_univ, true_and, joint,
    Prod.mk.injEq] at hp ⊢
  exact ⟨hp.1.1, hp.2⟩

/-- A sensor is *sufficient* for the question when the joint reading determines
the consumer. -/
def Resolves (O : X → Y) (M : X → W) (C : X → Z) : Prop := Determines (joint O M) C

/-- Resolution is exactly a zero residual score. -/
theorem resolves_iff_ambiguity_zero [DecidableEq W] (O : X → Y) (M : X → W) (C : X → Z) :
    Resolves O M C ↔ ambiguity (joint O M) C = 0 :=
  (ambiguity_eq_zero_iff_determines (joint O M) C).symm

/-! ## §3 Recommending the next measurement -/

/-- A candidate sensor: a name and a rational readout of the state. -/
structure Sensor (X : Type) where
  /-- A label for the sensor. -/
  name : String
  /-- What it reads. -/
  readout : X → ℚ

/-- The residual ambiguity left after adding a candidate sensor. -/
def residual (O : X → Y) (C : X → Z) (s : Sensor X) : ℕ :=
  ambiguity (joint O s.readout) C

/-- **The recommendation**: the declared candidate leaving the least residual
ambiguity. -/
def bestSensor (O : X → Y) (C : X → Z) (cands : List (Sensor X)) : Option (Sensor X) :=
  cands.argmin (residual O C)

/-- **The recommendation is minimal** among the declared candidates. -/
theorem bestSensor_minimal {O : X → Y} {C : X → Z} {cands : List (Sensor X)} {s t : Sensor X}
    (hs : s ∈ bestSensor O C cands) (ht : t ∈ cands) : residual O C s ≤ residual O C t :=
  List.le_of_mem_argmin ht hs

/-- The recommendation is one of the declared candidates: the procedure does not
invent an instrument. -/
theorem bestSensor_mem {O : X → Y} {C : X → Z} {cands : List (Sensor X)} {s : Sensor X}
    (hs : s ∈ bestSensor O C cands) : s ∈ cands :=
  List.argmin_mem hs

/-- There is a recommendation exactly when a candidate was offered. -/
theorem bestSensor_isSome_iff (O : X → Y) (C : X → Z) (cands : List (Sensor X)) :
    (bestSensor O C cands).isSome = true ↔ cands ≠ [] := by
  cases hc : cands with
  | nil => simp [bestSensor]
  | cons a t =>
    have : (bestSensor O C (a :: t)).isSome = true := by
      rcases h : List.argmin (residual O C) (a :: t) with _ | s
      · exact absurd h (by simp [List.argmin_eq_none])
      · simp [bestSensor, h]
    simp [this]

/-- **The recommendation resolves the question exactly when some declared
candidate does.**  So the procedure never misses an adequate sensor, and never
claims adequacy that no candidate has. -/
theorem bestSensor_resolves_iff_some_candidate_resolves
    {O : X → Y} {C : X → Z} {cands : List (Sensor X)} {s : Sensor X}
    (hs : s ∈ bestSensor O C cands) :
    Resolves O s.readout C ↔ ∃ t ∈ cands, Resolves O t.readout C := by
  constructor
  · exact fun h => ⟨s, bestSensor_mem hs, h⟩
  · rintro ⟨t, ht, hres⟩
    rw [resolves_iff_ambiguity_zero] at hres ⊢
    have := bestSensor_minimal hs ht
    unfold residual at this
    omega

/-- **The honest negative.**  The best available sensor need not be a sufficient
one: here the only candidate strictly contracts the envelope and still leaves
the consumer undetermined, so "recommended" never means "adequate". -/
theorem best_is_not_always_sufficient :
    ∃ (O : Fin 4 → Unit) (C : Fin 4 → Fin 4) (s : Sensor (Fin 4)),
      residual O C s < ambiguity O C ∧ ¬ Resolves O s.readout C := by
  refine ⟨fun _ => (), id, ⟨"parity", fun i => if i.val % 2 = 0 then 0 else 1⟩, ?_, ?_⟩
  · decide
  · intro h
    have := h 0 2 (by decide)
    exact absurd this (by decide)

/-- **And the ranking is relative to the question.**  Two consumers rank the
same pair of candidate sensors in opposite orders, so a measurement-value claim
must name the consumer it is valuable for. -/
theorem best_sensor_depends_on_the_question :
    ∃ (O : Fin 2 × Fin 2 → Unit) (C₁ C₂ : Fin 2 × Fin 2 → Fin 2) (s t : Sensor (Fin 2 × Fin 2)),
      residual O C₁ s < residual O C₁ t ∧ residual O C₂ t < residual O C₂ s := by
  refine ⟨fun _ => (), fun p => p.1, fun p => p.2,
    ⟨"first coordinate", fun p => (p.1 : ℚ)⟩, ⟨"second coordinate", fun p => (p.2 : ℚ)⟩, ?_, ?_⟩
  · decide
  · decide

end Integration.Experiment.MeasurementValue
