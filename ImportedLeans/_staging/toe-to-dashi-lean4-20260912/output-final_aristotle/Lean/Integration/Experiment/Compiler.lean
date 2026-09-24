import Integration.Experiment.FailureLocalisation
import Integration.Experiment.QuantityGraph

/-!
# The experiment compiler

This file assembles the five preceding lanes into one object,

```
ExperimentSpec  →  ExperimentPrediction
```

and proves the properties the assembly is supposed to have.  The compiler is
**domain-neutral**: it is a single generic function, and the two instance files
(`Integration.Experiment.Lithium`, `Integration.Experiment.ThermalDiffusion`)
call it without adding any machinery of their own.

## The shape

A specification carries a finite family `H` of *candidate hypotheses* — the
latent states and parameter settings the evidence has not ruled out — together
with an initial state, dynamics and observation map for each, the declared
prediction consumers, the declared hazards, an uncertainty budget, a support
cone and a list of candidate sensors.  Compilation returns the trajectory of the
nominal hypothesis, the prediction envelope over the admissible hypotheses, the
reported intervals, the risk envelope, the assumptions, the sensitivity list,
the support cone, the epistemic status and the recommended next measurement.

## What is proved about the compiler

* `truth_in_envelope` — **soundness**: if the true hypothesis is admissible, the
  true value of a declared quantity is in the reported envelope.  Nothing is
  predicted that excludes the truth;
* `envelope_is_a_point_iff_determined` — the envelope collapses to a point
  exactly when the admissible hypotheses agree, i.e. exactly the determination
  criterion of the existing owner;
* `risk_resolved_iff_no_ambiguity`, `recommendation_is_minimal`,
  `recommendation_resolves_iff_possible` — the risk verdict and the
  next-measurement recommendation, inherited from Lanes 4 and 5;
* `status_is_the_computed_one` — the epistemic status of the output is the
  status computed from the support cone, so a specification cannot declare its
  own tier;
* `observation_outside_envelope_localises` — the Lane-6 hook: an observation
  outside the compiled envelope is a falsification of the compiled derivation.

No physical claim is made here; `ExperimentSpec` is a record and `compile` is a
function between records.
-/

namespace Integration.Experiment.Compiler

open Integration.CoordinateSufficiency
open Integration.FactorisationCollision
open Integration.PredictionEnvelope
open Integration.PredictionStatus
open Integration.Experiment.Intervention
open Integration.Experiment.Uncertainty
open Integration.Experiment.Risk
open Integration.Experiment.MeasurementValue
open Integration.Experiment.FailureLocalisation

/-! ## §1 The specification -/

/-- A named prediction consumer: a quantity read off the final state. -/
structure Consumer (State : Type) where
  /-- A label. -/
  name : String
  /-- The quantity predicted. -/
  quantity : State → ℚ

/-- **The experimental specification.**  `H` is the finite family of candidate
hypotheses the evidence leaves open (latent states together with parameter
settings). -/
structure ExperimentSpec (H State Control Obs : Type) where
  /-- The initial state under each hypothesis. -/
  initialState : H → State
  /-- The protocol: the intervention applied. -/
  controls : Protocol Control
  /-- The dynamics under each hypothesis. -/
  dynamics : H → Dynamics State Control
  /-- The instrumentation. -/
  observe : State → Obs
  /-- Which hypotheses the prior evidence and the validity region leave
  admissible. -/
  admissible : H → Bool
  /-- The hypothesis whose prediction is reported as the central value. -/
  nominal : H
  /-- The declared prediction consumers. -/
  quantities : List (Consumer State)
  /-- The declared hazards. -/
  hazards : List (Hazard State)
  /-- The uncertainty budget attached to the central value. -/
  budget : Budget
  /-- The rule by which a variance is turned into a reported interval. -/
  coverage : Coverage
  /-- The assumptions inherited from the laws used. -/
  assumptions : List String
  /-- Declared first-order sensitivities of the reported quantity. -/
  sensitivities : List (String × ℚ)
  /-- Declared independent input variances of the reported quantity, paired
  with the sensitivity of that quantity to each input: entry `i` is
  `(∂y/∂xᵢ, σᵢ²)`.  The default is the empty list, i.e. *nothing declared*; the
  compiler then reports a propagated variance of `0` and
  `Integration.Experiment.CertifiedPropagation` says exactly what that is worth.
  Whether the first components really are derivatives is a separate obligation,
  discharged for a law by a `CertifiedLaw` certificate. -/
  inputVariances : List (ℚ × ℚ) := []
  /-- The support cone: where the prediction started and every step it took. -/
  support : SupportedPrediction
  /-- Candidate additional sensors, reading the latent hypothesis. -/
  candidateSensors : List (Sensor H)

namespace ExperimentSpec

variable {H State Control Obs : Type}

/-- The state reached at time `n` under hypothesis `h`. -/
def stateAt (e : ExperimentSpec H State Control Obs) (h : H) (n : ℕ) : State :=
  trajectory (e.dynamics h) (e.initialState h) e.controls.control n

/-- The final state under hypothesis `h`. -/
def finalState (e : ExperimentSpec H State Control Obs) (h : H) : State :=
  e.stateAt h e.controls.horizon

/-- The observation trace predicted under hypothesis `h`. -/
def traceOf (e : ExperimentSpec H State Control Obs) (h : H) : List Obs :=
  (List.range (e.controls.horizon + 1)).map (fun n => e.observe (e.stateAt h n))

/-- The risk profile predicted under hypothesis `h`. -/
def riskOf (e : ExperimentSpec H State Control Obs) (h : H) : List Bool :=
  profile e.hazards (e.finalState h)

/-- The hypotheses the evidence leaves open. -/
def admissibleSet (e : ExperimentSpec H State Control Obs) : Set H :=
  {h | e.admissible h = true}

end ExperimentSpec

/-! ## §2 The compiled output -/

/-- **The compiled prediction.** -/
structure ExperimentPrediction (H State Obs : Type) where
  /-- The trajectory of the nominal hypothesis. -/
  trajectory : ℕ → State
  /-- For each declared consumer, the set of values the admissible hypotheses
  allow. -/
  predictionEnvelope : List (String × Set ℚ)
  /-- For each declared consumer, the reported interval around its central
  value. -/
  intervals : List (String × Set ℚ)
  /-- The set of risk profiles the admissible hypotheses allow. -/
  riskEnvelope : Set (List Bool)
  /-- The assumptions the prediction inherits. -/
  assumptions : List String
  /-- The declared sensitivities. -/
  sensitivity : List (String × ℚ)
  /-- The support cone. -/
  supportCone : SupportedPrediction
  /-- The status computed from that cone. -/
  epistemicStatus : Tier
  /-- The uncertainty budget, kept as three separate entries. -/
  uncertainty : Budget
  /-- The first-order propagated variance of the reported quantity, **computed**
  by the compiler from the declared input variances and sensitivities — not a
  declared field.  `Integration.Experiment.CertifiedPropagation` proves it is
  the `Cov.push` of the declared row against the diagonal input covariance. -/
  propagatedVariance : ℚ
  /-- The recommended next measurement, if any candidate was offered. -/
  recommendedMeasurement : Option (Sensor H)

/-! ## §3 The compiler -/

variable {H State Control Obs : Type} [Fintype H] [DecidableEq Obs]

/-- **The compiler.**  One generic function; the domain instances supply only
data. -/
noncomputable def compile (e : ExperimentSpec H State Control Obs) :
    ExperimentPrediction H State Obs where
  trajectory := fun n => e.stateAt e.nominal n
  predictionEnvelope :=
    e.quantities.map (fun c => (c.name, (fun h => c.quantity (e.finalState h)) '' e.admissibleSet))
  intervals :=
    e.quantities.map (fun c =>
      (c.name, interval e.coverage (c.quantity (e.finalState e.nominal)) e.budget.quantifiedTotal))
  riskEnvelope := e.riskOf '' e.admissibleSet
  assumptions := e.assumptions
  sensitivity := e.sensitivities
  supportCone := e.support
  epistemicStatus := e.support.status
  uncertainty := e.budget
  propagatedVariance := (e.inputVariances.map (fun p => p.1 ^ 2 * p.2)).sum
  recommendedMeasurement := bestSensor e.traceOf e.riskOf e.candidateSensors

/-! ## §4 What the compiler guarantees -/

/-- **Soundness.**  If the true hypothesis is admissible, the true value of every
declared quantity lies in the reported envelope. -/
theorem truth_in_envelope (e : ExperimentSpec H State Control Obs) (c : Consumer State)
    (hc : c ∈ e.quantities) (h : H) (hadm : e.admissible h = true) :
    (c.name, (fun h' => c.quantity (e.finalState h')) '' e.admissibleSet) ∈
        (compile e).predictionEnvelope ∧
      c.quantity (e.finalState h) ∈
        (fun h' => c.quantity (e.finalState h')) '' e.admissibleSet := by
  constructor
  · exact List.mem_map_of_mem hc
  · exact ⟨h, hadm, rfl⟩

/-- The risk envelope contains the true risk profile of any admissible
hypothesis, for the same reason. -/
theorem truth_in_risk_envelope (e : ExperimentSpec H State Control Obs) (h : H)
    (hadm : e.admissible h = true) : e.riskOf h ∈ (compile e).riskEnvelope :=
  ⟨h, hadm, rfl⟩

omit [Fintype H] [DecidableEq Obs] in
/-- **A point prediction is exactly determination.**  The envelope of a consumer
is a single value iff the admissible hypotheses agree on it. -/
theorem envelope_is_a_point_iff_determined (e : ExperimentSpec H State Control Obs)
    (c : Consumer State) :
    ((fun h => c.quantity (e.finalState h)) '' e.admissibleSet).Subsingleton ↔
      ∀ h₁ ∈ e.admissibleSet, ∀ h₂ ∈ e.admissibleSet,
        c.quantity (e.finalState h₁) = c.quantity (e.finalState h₂) := by
  constructor
  · intro hsub h₁ h1 h₂ h2
    exact hsub ⟨h₁, h1, rfl⟩ ⟨h₂, h2, rfl⟩
  · rintro hall z₁ ⟨h₁, h1, rfl⟩ z₂ ⟨h₂, h2, rfl⟩
    exact hall h₁ h1 h₂ h2

/-- **The risk verdict.**  The instrumentation answers the risk question exactly
when the predicted traces leave no consumer-relevant ambiguity among the
hypotheses. -/
theorem risk_resolved_iff_no_ambiguity (e : ExperimentSpec H State Control Obs) :
    Determines e.traceOf e.riskOf ↔ ambiguity e.traceOf e.riskOf = 0 :=
  (ambiguity_eq_zero_iff_determines e.traceOf e.riskOf).symm

/-- **The recommendation is minimal** among the declared candidates. -/
theorem recommendation_is_minimal (e : ExperimentSpec H State Control Obs) {s t : Sensor H}
    (hs : s ∈ (compile e).recommendedMeasurement) (ht : t ∈ e.candidateSensors) :
    residual e.traceOf e.riskOf s ≤ residual e.traceOf e.riskOf t :=
  bestSensor_minimal (O := e.traceOf) (C := e.riskOf) hs ht

/-- **And it resolves the risk question exactly when some candidate does.** -/
theorem recommendation_resolves_iff_possible (e : ExperimentSpec H State Control Obs)
    {s : Sensor H} (hs : s ∈ (compile e).recommendedMeasurement) :
    Resolves e.traceOf s.readout e.riskOf ↔
      ∃ t ∈ e.candidateSensors, Resolves e.traceOf t.readout e.riskOf :=
  bestSensor_resolves_iff_some_candidate_resolves hs

/-- **Status is computed, not declared.**  The output's tier is the tier of the
support cone; a specification cannot set it independently. -/
theorem status_is_the_computed_one (e : ExperimentSpec H State Control Obs) :
    (compile e).epistemicStatus = chain e.support.origin e.support.steps := rfl

/-- **The Lane-6 hook.**  An observed value outside the compiled envelope
falsifies the compiled derivation, and therefore localises to one of its
declared dependencies. -/
theorem observation_outside_envelope_localises (d : Derivation ℚ)
    (h : d.actual ∉ d.envelope) : ∃ c, ¬ d.correct c :=
  falsification_localises_to_a_dependency d h

/-- **The uncertainty budget survives compilation intact**: the three sources
are carried through as three fields, not summed. -/
theorem compile_keeps_the_budget (e : ExperimentSpec H State Control Obs) :
    (compile e).uncertainty = e.budget := rfl

/-- The assumptions of the laws used travel with the prediction. -/
theorem compile_keeps_the_assumptions (e : ExperimentSpec H State Control Obs) :
    (compile e).assumptions = e.assumptions := rfl

end Integration.Experiment.Compiler
