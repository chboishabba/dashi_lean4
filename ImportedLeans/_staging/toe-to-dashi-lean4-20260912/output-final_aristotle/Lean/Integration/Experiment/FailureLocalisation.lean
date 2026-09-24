import Integration.Experiment.MeasurementValue
import Integration.PredictionStatus

/-!
# Lane 6 — prediction failure, localisation and repair

When the observation falls outside the predicted envelope the system must not
say "model wrong".  It must say *which* of the things the prediction depended
on could be wrong, and what would discriminate them.

## What is proved

* `falsification_localises_to_a_dependency` — the honest content of a
  falsification: if the derivation is sound whenever all of its declared
  dependencies hold, then an observation outside the envelope proves that **at
  least one declared dependency fails**.  Nothing stronger is available, and the
  file proves nothing stronger is available:
* `failure_does_not_localise_uniquely` — two different single-class repairs can
  both restore consistency, so the discrepancy does not determine the
  failure class.  This is again the factorisation owner: the map
  "discrepancy ↦ failure class" does not exist;
* `measurement_failure_is_not_model_failure` — a discrepancy attributable to the
  instrument leaves every model dependency intact, so falsification must be
  traced, not broadcast;
* `discriminating_experiment_exists_iff_repairs_differ` — the loop closes: the
  next experiment is worth running exactly when the surviving repairs predict
  different observations, which is the Lane-5 question asked of the repair set;
* `repair_needs_a_receipt` — a repair does not promote the prediction's status
  on its own: adopting it is a receipt-free step, so the status can only weaken
  or stay put (the existing promotion discipline, applied to model repair).

Nothing here asserts that any particular model, instrument or measurement is
right or wrong.  `Derivation` is a record with an abstract set of admissible
observations.
-/

namespace Integration.Experiment.FailureLocalisation

open Integration.CoordinateSufficiency
open Integration.FactorisationCollision
open Integration.PredictionEnvelope
open Integration.PredictionStatus

/-! ## §1 Dependencies of a prediction -/

/-- The failure classes a prediction can be traced to.  This list is the
declared dependency structure of the derivation: a falsification can be
localised to it and, by `failure_does_not_localise_uniquely`, no further. -/
inductive FailureClass
  /-- The instrument misreported. -/
  | badMeasurement
  /-- A parameter value was wrong. -/
  | wrongParameter
  /-- The state space omits a variable that matters. -/
  | missingStateVariable
  /-- An approximation was used outside its range. -/
  | invalidApproximation
  /-- The dynamics are wrong. -/
  | incorrectDynamics
  /-- A bridge between domains does not transport. -/
  | wrongBridge
  /-- An assumption inherited from a source is false. -/
  | wrongSourceAssumption
  deriving DecidableEq, Repr, Fintype

/-- Which failure classes are about the model rather than the instrument. -/
def FailureClass.isModelSide : FailureClass → Bool
  | .badMeasurement => false
  | _ => true

/-- A derivation of a prediction: what it depends on, what it predicts, what
was observed, and the soundness link between them. -/
structure Derivation (Obs : Type) where
  /-- For each class, the proposition that this dependency is in fact sound. -/
  correct : FailureClass → Prop
  /-- The predicted envelope. -/
  envelope : Set Obs
  /-- The realised observation. -/
  actual : Obs
  /-- **The content of "the prediction was derived correctly"**: if every
  declared dependency holds, the observation lies in the envelope. -/
  sound : (∀ c, correct c) → actual ∈ envelope

/-- **Falsification localises — exactly this far.**  An observation outside the
envelope proves that some declared dependency fails. -/
theorem falsification_localises_to_a_dependency {Obs : Type} (d : Derivation Obs)
    (h : d.actual ∉ d.envelope) : ∃ c, ¬ d.correct c := by
  by_contra hc
  push_neg at hc
  exact h (d.sound hc)

/-- The specialisation to a prediction envelope of the existing lane: if the
realised value of the consumer is not in `Pred O C y`, some dependency of the
derivation that produced `Pred` fails. -/
theorem envelope_falsification {X Y Z : Type} (O : X → Y) (C : X → Z) (y : Y)
    (d : Derivation Z) (henv : d.envelope = Pred O C y) (h : d.actual ∉ Pred O C y) :
    ∃ c, ¬ d.correct c :=
  falsification_localises_to_a_dependency d (henv ▸ h)

/-! ## §2 Repair hypotheses -/

/-- A repair hypothesis: a failure class to revise, the envelope the revised
derivation predicts, and the proof that the revision accommodates the
observation. -/
structure Repair (Obs : Type) (d : Derivation Obs) where
  /-- Which dependency the repair blames. -/
  target : FailureClass
  /-- What the repaired model predicts. -/
  revised : Set Obs
  /-- The repaired model accommodates what was seen. -/
  restores : d.actual ∈ revised

/-- A falsified prediction: the model predicted the value `0`, the value `1`
was observed. -/
def twoRepairExample : Derivation ℚ where
  correct := fun c => c ≠ .wrongParameter
  envelope := {0}
  actual := 1
  sound := fun h => absurd rfl (h .wrongParameter)

/-- **Failure does not localise uniquely.**  Two repairs of the same
falsification blame different classes and both restore consistency, so the
discrepancy does not determine the failure class: no function from observed
discrepancies to failure classes is available, and the choice between repairs
is an *experimental* question, not a logical one. -/
theorem failure_does_not_localise_uniquely :
    ∃ (r₁ r₂ : Repair ℚ twoRepairExample), r₁.target ≠ r₂.target := by
  refine ⟨⟨.wrongParameter, {1}, rfl⟩, ⟨.incorrectDynamics, Set.Icc 0 2, ?_⟩, ?_⟩
  · exact Set.mem_Icc.mpr (by norm_num [twoRepairExample])
  · simp

/-- **A measurement failure is not a model failure.**  There is a derivation
whose only false dependency is the instrument: every model-side dependency
holds, so a falsification must be traced through the dependency structure and
not broadcast to the model. -/
theorem measurement_failure_is_not_model_failure :
    ∃ d : Derivation ℚ,
      d.actual ∉ d.envelope ∧ ¬ d.correct .badMeasurement ∧
      ∀ c, c.isModelSide = true → d.correct c := by
  refine ⟨{ correct := fun c => c ≠ .badMeasurement, envelope := {0}, actual := 1,
            sound := fun h => absurd rfl (h .badMeasurement) }, ?_, ?_, ?_⟩
  · intro hmem
    have : (1 : ℚ) = 0 := hmem
    norm_num at this
  · exact fun h => h rfl
  · intro c hc
    cases c <;> simp_all [FailureClass.isModelSide]

/-! ## §3 Closing the loop: which experiment discriminates the repairs? -/

/-- Two surviving repairs are discriminable when some future observation
distinguishes their predictions. -/
def Discriminable {Obs : Type} {d : Derivation Obs} (r₁ r₂ : Repair Obs d) : Prop :=
  r₁.revised ≠ r₂.revised

/-- **The loop closes.**  A next experiment is worth running exactly when the
surviving repairs predict different observation sets — the Lane-5 question
("which measurement splits the fibre?") asked of the repair set rather than of
the state space. -/
theorem discriminating_experiment_exists_iff_repairs_differ {Obs : Type}
    {d : Derivation Obs} (r₁ r₂ : Repair Obs d) :
    Discriminable r₁ r₂ ↔ ∃ o : Obs, (o ∈ r₁.revised) ≠ (o ∈ r₂.revised) := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact h (Set.ext fun o => by
      have := hc o
      constructor
      · intro ho; rw [← this]; exact ho
      · intro ho; rw [this]; exact ho)
  · rintro ⟨o, ho⟩ hEq
    exact ho (by rw [hEq])

/-- Repairs that predict the same observations everywhere are not
distinguishable by any experiment in this observation language: the honest
"unfalsifiable pair" verdict. -/
theorem indistinguishable_repairs_need_a_richer_language {Obs : Type}
    {d : Derivation Obs} (r₁ r₂ : Repair Obs d) (h : r₁.revised = r₂.revised) :
    ¬ Discriminable r₁ r₂ := fun hd => hd h

/-! ## §4 A repair does not promote a prediction -/

/-- **Adopting a repair is a receipt-free step.**  Model repair changes what the
model says; it does not by itself supply evidence, so under the existing
promotion discipline the repaired prediction's status can only stay where it was
or weaken.  Nothing is laundered by being repaired. -/
theorem repair_needs_a_receipt (t : Tier) (ss : List Step)
    (h : ∀ s ∈ ss, s.isStrengthening = false) : t.rank ≤ (chain t ss).rank :=
  chain_rank_monotone t ss h

/-- In particular a repaired speculative analogy is still not a
model-conditional prediction until a receipt arrives. -/
theorem repaired_analogy_is_still_an_analogy (ss : List Step)
    (h : ∀ s ∈ ss, s.isStrengthening = false) :
    chain .speculativeAnalogy ss ≠ .modelConditional :=
  no_epistemic_laundering ss h

end Integration.Experiment.FailureLocalisation
