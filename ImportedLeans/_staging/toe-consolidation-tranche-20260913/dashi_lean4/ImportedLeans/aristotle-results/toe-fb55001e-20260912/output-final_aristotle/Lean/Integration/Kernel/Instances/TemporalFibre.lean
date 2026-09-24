import Integration.Kernel.Quotient

/-!
# A temporal instance: point-in-time fibres and universe leakage

`Agda/DASHI/Finance/PointInTimeUniverseFibreExact.agda` and
`…/UniverseLeakageResidualDependencyExact.agda` state two things about
historical evaluation of a rule over time: that a later membership list may not
be transported backwards into an earlier fibre, and that two evaluations can
expose the same coarse feature surface while differing in whether they depend
on the future.  The first is proved there against a `ForwardPath` relation; the
second is a genuine `HiddenResidualDependency` witness, wrapped in a
`Bool`-valued boundary record.  Both are restated here as Lean theorems, the
second as a direct instance of `Integration.Kernel.Quotient`.

## What is proved

* `no_backward_transport` — lawful transport is forward only, so a fibre carried
  from a later time is not available at an earlier one.
* **`static_universe_is_pit_iff_constant`** — a static membership list taken at
  one time reproduces the point-in-time list at *every* time exactly when
  membership never changes; `membership_changes` exhibits a membership function
  for which it does not, and `static_universe_misclassifies` is the resulting
  concrete error.  This is the survivorship/universe-selection defect stated as
  an equivalence rather than as a warning.
* `feature_pit_does_not_give_universe_pit` — the same statement at the level of
  observers: point-in-time correctness of the *features* does not determine
  point-in-time correctness of the *universe*.
* **`universe_dependence_does_not_descend`** — two evaluations with the same
  coarse feature surface and different future-dependence: the dependence code is
  not a function of the feature surface.  `dependence_strictly_refines` records
  that adding it is a strict refinement of the feature observer, and
  `features_still_correct` that the coarse feature reading survives that
  refinement unchanged.

**Claim boundary.** An "asset" is one of two labels, a "universe" is a
`ℕ → Asset → Bool`, and an "evaluation" is one of two labels.  Nothing here is
a claim about any market, data set, strategy or estimator, and no statement
about returns, risk or performance is made anywhere.
-/

namespace Integration.Kernel.Instances.TemporalFibre

open Integration.Kernel.Quotient

/-! ## §1 Forward-only transport -/

/-- A datum together with the time it is known at. -/
structure Fibre (α : Type*) where
  /-- The time at which the datum is available. -/
  time : ℕ
  /-- The datum. -/
  datum : α

/-- Transport is lawful only forwards in time. -/
def LawfulTransport {α : Type*} (s t : Fibre α) : Prop := s.time ≤ t.time

theorem lawfulTransport_refl {α : Type*} (s : Fibre α) : LawfulTransport s s := le_rfl

theorem lawfulTransport_trans {α : Type*} {s t u : Fibre α}
    (h₁ : LawfulTransport s t) (h₂ : LawfulTransport t u) : LawfulTransport s u :=
  h₁.trans h₂

/-- **A later fibre cannot be used earlier.** -/
theorem no_backward_transport {α : Type*} {s t : Fibre α} (h : t.time < s.time) :
    ¬ LawfulTransport s t := not_le.2 h

/-! ## §2 Point-in-time membership versus a static list -/

/-- Two labelled assets. -/
inductive Asset
  /-- An asset present throughout. -/
  | alpha
  /-- An asset admitted to the universe only later. -/
  | beta
  deriving DecidableEq, Fintype, Repr

/-- A point-in-time universe: which assets are members at each time. -/
def Universe : Type := ℕ → Asset → Bool

/-- The static list read off at one time and reused at every time. -/
def staticAt (U : Universe) (T : ℕ) : Universe := fun _ => U T

/-- **A static list is point-in-time correct exactly when membership never
changes.** -/
theorem static_universe_is_pit_iff_constant (U : Universe) (T : ℕ) :
    staticAt U T = U ↔ ∀ t, U t = U T := by
  constructor
  · intro h t
    exact (congrFun h t).symm
  · intro h
    exact funext fun t => (h t).symm

/-- A membership function in which `beta` joins the universe at time `1`. -/
def entrant : Universe := fun t a =>
  match a with
  | Asset.alpha => true
  | Asset.beta => decide (1 ≤ t)

theorem membership_changes : ¬ ∀ t, entrant t = entrant 1 := by
  intro h
  have := congrFun (h 0) Asset.beta
  simp [entrant] at this

/-- The concrete defect: the static list taken at time `1` reports the later
entrant as a member at time `0`. -/
theorem static_universe_misclassifies :
    staticAt entrant 1 0 Asset.beta ≠ entrant 0 Asset.beta := by
  simp [staticAt, entrant]

theorem static_entrant_not_pit : staticAt entrant 1 ≠ entrant := by
  intro h
  exact static_universe_misclassifies (congrFun (congrFun h 0) Asset.beta)

/-! ## §3 The observer form: same features, different provenance -/

/-- Two evaluations of the same rule. -/
inductive Evaluation
  /-- Membership taken from the point-in-time history. -/
  | pointInTime
  /-- Membership taken from a later static list. -/
  | leakedStatic
  deriving DecidableEq, Fintype, Repr

/-- What the coarse feature observer reports: both evaluations expose the same
causal feature surface. -/
def featureSurface : Evaluation → Unit := fun _ => ()

/-- Whether the evaluation depends on data from the future. -/
def universeDependence : Evaluation → Bool
  | Evaluation.pointInTime => false
  | Evaluation.leakedStatic => true

theorem feature_collides :
    featureSurface Evaluation.pointInTime = featureSurface Evaluation.leakedStatic := rfl

theorem dependence_separates :
    universeDependence Evaluation.pointInTime ≠ universeDependence Evaluation.leakedStatic := by
  decide

/-- **Feature-level agreement does not certify provenance.**  The
future-dependence code is not a function of the feature surface. -/
theorem universe_dependence_does_not_descend :
    ¬ DescendsThrough universeDependence featureSurface :=
  not_descendsThrough_of_collision feature_collides dependence_separates

/-- Reading the provenance coordinate strictly refines the feature observer. -/
theorem dependence_strictly_refines :
    StrictlyRefines featureSurface (pair featureSurface universeDependence) :=
  strictlyRefines_pair_of_separates featureSurface universeDependence
    feature_collides dependence_separates

/-- …and the feature reading itself is unchanged by that refinement. -/
theorem features_still_correct :
    DescendsThrough featureSurface (pair featureSurface universeDependence) :=
  refinement_is_not_refutation featureSurface universeDependence

/-- The same statement in the vocabulary of the finance lane: point-in-time
correctness of the features does not imply point-in-time correctness of the
universe, because the two evaluations agree on the former and differ on the
latter. -/
theorem feature_pit_does_not_give_universe_pit :
    ∃ e₁ e₂ : Evaluation,
      featureSurface e₁ = featureSurface e₂ ∧ universeDependence e₁ ≠ universeDependence e₂ :=
  ⟨Evaluation.pointInTime, Evaluation.leakedStatic, feature_collides, dependence_separates⟩

end Integration.Kernel.Instances.TemporalFibre
