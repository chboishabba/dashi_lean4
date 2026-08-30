import Integration.Experiment.Compiler
import Integration.Experiment.ModelSelection
import Integration.Experiment.CertifiedPropagation

/-!
# The first domain instance: a lithium cell under a galvanostatic hold

This file supplies **data only**.  Every theorem below is either an instance of
a generic result from the experiment compiler and its lanes, or an arithmetic
fact about this particular cell model; no new machinery is introduced, which is
the point of the exercise.

## The setup

A cell is described by its state of charge, its temperature, its internal
resistance (a latent parameter carried in the state) and the current last
applied.  Under a constant current `I` the model is

```
soc'  = soc + I dt
temp' = temp + I² R dt / C
V     = V₀ + k · soc + I R          (the instrument reading)
```

Three candidate hypotheses are declared.  Two of them — a low-resistance cell at
a higher state of charge and a high-resistance cell at a lower one — produce
**identical voltage-and-current traces** for the whole hold, and different
temperatures.  The third is ruled out by the data.

## What comes out

* `traces_agree` and `risks_differ` — the observational collision;
* `voltage_and_current_are_insufficient_for_the_thermal_risk` — the Lane-4
  verdict, obtained by applying the generic theorem;
* `temperature_envelope_is_not_a_point` — the prediction envelope has two
  elements, so no point prediction of the final temperature exists;
* `budget_is_not_one_number` — the reported uncertainty is dominated by a
  parameter term while the model discrepancy is unquantified, and the two facts
  are reported separately;
* `some_candidate_resolves_the_risk_question` and
  `recommendation_resolves_the_risk_question` — the Lane-5 output: a temperature
  measurement splits the surviving pair, an impedance measurement also does, a
  repeat voltage measurement does not, and whatever the compiler recommends is
  therefore adequate;
* `charge_delivered_is_typed` — the typed-quantity graph agrees with the
  simulated trajectory on the charge passed.

**Nothing here is a claim about real lithium cells.**  The numbers are a model
instance chosen to exercise the calculus: the "cell" is four rationals, the
"instrument" is a rational-valued function of them, and the hazard threshold is
a declared rational.
-/

namespace Integration.Experiment.Lithium

open Integration.CoordinateSufficiency
open Integration.FactorisationCollision
open Integration.Experiment.Dimension
open Integration.Experiment.QuantityGraph
open Integration.Experiment.Intervention
open Integration.Experiment.Uncertainty
open Integration.Experiment.Risk
open Integration.Experiment.MeasurementValue
open Integration.Experiment.Compiler
open Integration.PredictionStatus
open Integration.Experiment.FailureLocalisation

/-! ## §1 The cell model -/

/-- The state of the cell: charge state, temperature, internal resistance (a
latent parameter carried in the state) and the current last applied. -/
structure CellState where
  /-- State of charge, in coulombs passed. -/
  soc : ℚ
  /-- Temperature. -/
  temp : ℚ
  /-- Internal resistance. -/
  resistance : ℚ
  /-- The current last applied. -/
  current : ℚ
  deriving DecidableEq

/-- One time step: coulomb counting plus ohmic self-heating. -/
def cellDynamics (dt heatCapacity : ℚ) : Dynamics CellState ℚ where
  step := fun x i =>
    { soc := x.soc + i * dt,
      temp := x.temp + i ^ 2 * x.resistance * dt / heatCapacity,
      resistance := x.resistance,
      current := i }

/-- The instrument: terminal voltage and applied current. -/
def observeCell (v₀ k : ℚ) (x : CellState) : ℚ × ℚ :=
  (v₀ + k * x.soc + x.current * x.resistance, x.current)

/-- **The closed form of the hold.**  Under a constant unit current with unit
time step and unit heat capacity, the state at step `n` is explicit. -/
theorem hold_stateAt (x₀ : CellState) (hc : x₀.current = 1) (n : ℕ) :
    trajectory (cellDynamics 1 1) x₀ (fun _ => (1 : ℚ)) n =
      ⟨x₀.soc + n, x₀.temp + n * x₀.resistance, x₀.resistance, 1⟩ := by
  induction n with
  | zero => cases x₀; simp_all
  | succ n ih =>
    rw [trajectory_succ, ih]
    simp only [cellDynamics, CellState.mk.injEq]
    and_intros <;> first | trivial | (push_cast; ring)

/-! ## §2 The declared hypotheses -/

/-- The three candidate latent states.  `h₀` and `h₁` are the observationally
indistinguishable pair; `h₂` is ruled out by the data. -/
def initial : Fin 3 → CellState
  | 0 => ⟨1, 300, 1, 1⟩
  | 1 => ⟨0, 300, 2, 1⟩
  | 2 => ⟨5, 300, 1, 1⟩

/-- The declared hazard: an over-temperature threshold. -/
def overTemperature : Hazard CellState :=
  { name := "cell temperature above 315", quantity := CellState.temp, threshold := 315 }

/-- The candidate sensors: a surface-temperature probe, an impedance
measurement, a repeat of the voltage reading and an electrolyte-concentration
proxy that is constant across the hypotheses. -/
def temperatureSensor : Sensor (Fin 3) :=
  { name := "cell surface temperature",
    readout := fun h => (initial h).temp + 10 * (initial h).resistance }

/-- Impedance spectroscopy, reading the internal resistance directly. -/
def impedanceSensor : Sensor (Fin 3) :=
  { name := "impedance", readout := fun h => (initial h).resistance }

/-- A repeat of the terminal-voltage reading. -/
def voltageRepeatSensor : Sensor (Fin 3) :=
  { name := "terminal voltage, repeated",
    readout := fun h => 3 + ((initial h).soc + 10) + (initial h).resistance }

/-- An electrolyte-concentration proxy that happens to be identical across the
candidates. -/
def concentrationSensor : Sensor (Fin 3) :=
  { name := "electrolyte concentration proxy", readout := fun _ => 1 }

/-- **The specification.**  Ten steps of a unit galvanostatic hold, one
prediction consumer, one hazard, a three-way uncertainty budget whose model
discrepancy is unquantified, and four candidate sensors. -/
def spec : ExperimentSpec (Fin 3) CellState ℚ (ℚ × ℚ) where
  initialState := initial
  controls := { control := fun _ => 1, horizon := 10 }
  dynamics := fun _ => cellDynamics 1 1
  observe := observeCell 3 1
  admissible := fun h => h ≠ 2
  nominal := 0
  quantities := [{ name := "final temperature", quantity := CellState.temp }]
  hazards := [overTemperature]
  budget := { measurement := 1 / 100, parameter := 4, modelDiscrepancy := none }
  coverage := clampCoverage
  assumptions :=
    ["ohmic heating is the only heat source",
     "no heat loss to the environment over the hold",
     "open-circuit voltage is affine in the state of charge",
     "internal resistance is constant over the hold"]
  sensitivities := [("d(temp)/d(resistance)", 10), ("d(temp)/d(current)", 20)]
  inputVariances := [(10, 1 / 10000), (20, 1 / 10000)]
  support := { origin := .modelConditional, steps := [] }
  candidateSensors := [voltageRepeatSensor, concentrationSensor, temperatureSensor,
    impedanceSensor]

/-! ## §3 The trajectory and the observational collision -/

@[simp] theorem spec_initialState : spec.initialState = initial := rfl
@[simp] theorem spec_observe : spec.observe = observeCell 3 1 := rfl
@[simp] theorem spec_horizon : spec.controls.horizon = 10 := rfl
@[simp] theorem spec_hazards : spec.hazards = [overTemperature] := rfl
@[simp] theorem spec_admissible (h : Fin 3) : spec.admissible h = decide (h ≠ 2) := rfl
@[simp] theorem spec_dynamics (h : Fin 3) : spec.dynamics h = cellDynamics 1 1 := rfl
@[simp] theorem spec_control (n : ℕ) : spec.controls.control n = 1 := rfl

/-- The state of hypothesis `h` at step `n`, in closed form. -/
theorem spec_stateAt (h : Fin 3) (n : ℕ) :
    spec.stateAt h n =
      ⟨(initial h).soc + n, (initial h).temp + n * (initial h).resistance,
        (initial h).resistance, 1⟩ := by
  have hc : (initial h).current = 1 := by fin_cases h <;> rfl
  exact hold_stateAt (initial h) hc n

/-- The final temperature under each hypothesis. -/
theorem final_temperature (h : Fin 3) :
    (spec.finalState h).temp = (initial h).temp + 10 * (initial h).resistance := by
  rw [ExperimentSpec.finalState, spec_stateAt]
  norm_num

/-- The final state of charge under each hypothesis. -/
theorem final_soc (h : Fin 3) : (spec.finalState h).soc = (initial h).soc + 10 := by
  rw [ExperimentSpec.finalState, spec_stateAt]
  norm_num

/-- The instrument reading of hypothesis `h` at step `n`. -/
theorem spec_observation (h : Fin 3) (n : ℕ) :
    spec.observe (spec.stateAt h n) =
      (3 + ((initial h).soc + n) + (initial h).resistance, 1) := by
  rw [spec_stateAt]
  simp [observeCell]

/-- **The two surviving hypotheses produce identical traces.**  A low-resistance
cell at a higher state of charge and a high-resistance cell at a lower one are
indistinguishable to voltage and current, for the whole hold. -/
theorem traces_agree : spec.traceOf 0 = spec.traceOf 1 := by
  unfold ExperimentSpec.traceOf
  refine List.map_congr_left ?_
  intro n _
  rw [spec_observation, spec_observation]
  have : (3 : ℚ) + ((initial 0).soc + n) + (initial 0).resistance
      = 3 + ((initial 1).soc + n) + (initial 1).resistance := by
    show (3 : ℚ) + (1 + n) + 1 = 3 + (0 + n) + 2
    ring
  rw [this]

/-- **And their risks differ.**  At the end of the hold the high-resistance cell
is over the declared threshold and the other is not. -/
theorem risks_differ : spec.riskOf 0 ≠ spec.riskOf 1 := by
  have v0 : (spec.finalState 0).temp = 310 := by
    rw [final_temperature]; show (300 : ℚ) + 10 * 1 = 310; norm_num
  have v1 : (spec.finalState 1).temp = 320 := by
    rw [final_temperature]; show (300 : ℚ) + 10 * 2 = 320; norm_num
  have p0 : ¬ (315 : ℚ) < (spec.finalState 0).temp := by rw [v0]; norm_num
  have p1 : (315 : ℚ) < (spec.finalState 1).temp := by rw [v1]; norm_num
  simp only [ExperimentSpec.riskOf, profile, spec_hazards, List.map_cons, List.map_nil,
    Hazard.exceeded, overTemperature, ne_eq, List.cons.injEq, and_true, decide_eq_decide]
  intro hiff
  exact p0 (hiff.mpr p1)

/-- **The Lane-4 verdict, instantiated.**  Voltage and current are insufficient
instrumentation for the thermal-risk question: no reading of them answers it,
and no post-processing repairs that. -/
theorem voltage_and_current_are_insufficient_for_the_thermal_risk :
    ¬ Determines spec.traceOf spec.riskOf ∧
      ∀ f : List (ℚ × ℚ) → List Bool, ¬ ∀ h, spec.riskOf h = f (spec.traceOf h) :=
  instrumentation_insufficient_for_the_risk_question
    (by decide : (0 : Fin 3) ≠ 1) traces_agree risks_differ

/-! ## §4 The prediction envelope and the uncertainty budget -/

/-- **The envelope is not a point.**  Both `310` and `320` are admissible
predictions of the final temperature, so the compiled output is a genuine set
and not a number. -/
theorem temperature_envelope_is_not_a_point :
    (310 : ℚ) ∈ (fun h => (spec.finalState h).temp) '' spec.admissibleSet ∧
      (320 : ℚ) ∈ (fun h => (spec.finalState h).temp) '' spec.admissibleSet ∧
      ¬ ((fun h => (spec.finalState h).temp) '' spec.admissibleSet).Subsingleton := by
  have m0 : (0 : Fin 3) ∈ spec.admissibleSet := by
    simp [ExperimentSpec.admissibleSet]
  have m1 : (1 : Fin 3) ∈ spec.admissibleSet := by
    simp [ExperimentSpec.admissibleSet]
  have v0 : (spec.finalState 0).temp = 310 := by
    rw [final_temperature]; show (300 : ℚ) + 10 * 1 = 310; norm_num
  have v1 : (spec.finalState 1).temp = 320 := by
    rw [final_temperature]; show (300 : ℚ) + 10 * 2 = 320; norm_num
  refine ⟨⟨0, m0, v0⟩, ⟨1, m1, v1⟩, ?_⟩
  intro hsub
  have := hsub ⟨0, m0, v0⟩ ⟨1, m1, v1⟩
  norm_num at this

/-- **The uncertainty is not one number.**  The quantified budget is dominated
by the parameter term, and the model discrepancy is unquantified — so the
dominant *quantified* source and the dominant *unknown* are different questions,
reported separately. -/
theorem budget_is_not_one_number :
    spec.budget.dominantQuantified = .parameter ∧
      spec.budget.isComplete = false ∧
      spec.budget.quantifiedTotal = 401 / 100 := by
  refine ⟨?_, rfl, ?_⟩
  · norm_num [Budget.dominantQuantified, spec]
  · norm_num [Budget.quantifiedTotal, spec]

/-! ## §5 Which measurement to take next -/

/-- **A temperature measurement resolves the risk question.** -/
theorem temperature_sensor_resolves :
    Resolves spec.traceOf temperatureSensor.readout spec.riskOf := by
  intro x y hxy
  have hread : temperatureSensor.readout x = temperatureSensor.readout y :=
    congrArg Prod.snd hxy
  have htemp : (spec.finalState x).temp = (spec.finalState y).temp := by
    rw [final_temperature, final_temperature]
    simpa [temperatureSensor] using hread
  simp only [ExperimentSpec.riskOf, profile, spec_hazards, List.map_cons, List.map_nil,
    Hazard.exceeded, overTemperature, htemp]

/-- **A repeated voltage measurement does not.**  It reads the same value on the
two surviving hypotheses, so the joint reading still confuses them. -/
theorem voltage_repeat_does_not_resolve :
    ¬ Resolves spec.traceOf voltageRepeatSensor.readout spec.riskOf := by
  intro hres
  refine risks_differ (hres 0 1 ?_)
  have hv : voltageRepeatSensor.readout 0 = voltageRepeatSensor.readout 1 := by
    show (3 : ℚ) + (1 + 10) + 1 = 3 + (0 + 10) + 2
    norm_num
  simp only [joint, Prod.mk.injEq]
  exact ⟨traces_agree, hv⟩

/-- Hence some declared candidate resolves the question. -/
theorem some_candidate_resolves_the_risk_question :
    ∃ t ∈ spec.candidateSensors, Resolves spec.traceOf t.readout spec.riskOf :=
  ⟨temperatureSensor, by simp [spec], temperature_sensor_resolves⟩

/-- **The recommendation is adequate.**  The compiler offers a recommendation,
and by the generic Lane-5 theorem — not by any lithium-specific argument — that
recommendation resolves the thermal-risk question. -/
theorem recommendation_resolves_the_risk_question :
    ∃ s, (compile spec).recommendedMeasurement = some s ∧
      Resolves spec.traceOf s.readout spec.riskOf := by
  have hne : spec.candidateSensors ≠ [] := by simp [spec]
  have hsome : (bestSensor spec.traceOf spec.riskOf spec.candidateSensors).isSome = true :=
    (bestSensor_isSome_iff _ _ _).mpr hne
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨s, hs, ?_⟩
  refine (recommendation_resolves_iff_possible spec (s := s) ?_).mpr
    some_candidate_resolves_the_risk_question
  simpa [compile] using hs

/-! ## §6 The typed quantity graph agrees with the simulation -/

/-- **The charge passed, typed.**  The trajectory's coulomb count over the hold
agrees with the value the typed `Q = I t` edge returns, and that value carries
the dimension of charge. -/
theorem charge_delivered_is_typed :
    (spec.finalState 0).soc - (initial 0).soc = 10 ∧
      chargeLaw.apply [⟨Dim.ampere, 1⟩, ⟨Dim.second, 10⟩] = some ⟨Dim.coulomb, 10⟩ := by
  constructor
  · rw [final_soc]
    show (1 : ℚ) + 10 - 1 = 10
    norm_num
  · norm_num [Law.apply, chargeLaw, dims]

/-- And the amount of lithium that charge would convert is *not* determined by
the charge alone: the model edge's assumptions are load-bearing here too. -/
theorem amount_needs_the_assumptions :
    ¬ Determines CellRun.charge CellRun.amount :=
  amount_does_not_factor_through_charge


/-! ## §7 What the quantified interval does not cover -/

/-- **The uncertainty budget under-covers the envelope, and says so.**  The
reported interval is built from the *quantified* variance — measurement noise
plus parameter uncertainty — and it does not contain the second admissible
prediction of the final temperature.  The missing width is exactly the
unquantified model discrepancy, which the budget records as `none` rather than
as zero.  This is the concrete form of the Lane-2 requirement that the numerical
uncertainty and the dominant unknown be reported separately. -/
theorem reported_interval_does_not_cover_the_envelope :
    (320 : ℚ) ∈ (fun h => (spec.finalState h).temp) '' spec.admissibleSet ∧
      (320 : ℚ) ∉ interval spec.coverage ((spec.finalState spec.nominal).temp)
        spec.budget.quantifiedTotal ∧
      spec.budget.isComplete = false := by
  have m1 : (1 : Fin 3) ∈ spec.admissibleSet := by simp [ExperimentSpec.admissibleSet]
  have v0 : (spec.finalState 0).temp = 310 := by
    rw [final_temperature]; show (300 : ℚ) + 10 * 1 = 310; norm_num
  have v1 : (spec.finalState 1).temp = 320 := by
    rw [final_temperature]; show (300 : ℚ) + 10 * 2 = 320; norm_num
  refine ⟨⟨1, m1, v1⟩, ?_, rfl⟩
  intro hmem
  have hup := (Set.mem_Icc.mp hmem).2
  show False
  have hq : spec.budget.quantifiedTotal = 401 / 100 := by
    show (1 : ℚ) / 100 + 4 + 0 = 401 / 100
    norm_num
  rw [show spec.nominal = (0 : Fin 3) from rfl, v0, hq,
    show spec.coverage = clampCoverage from rfl] at hup
  norm_num [clampCoverage] at hup

/-! ## §8 The epistemic status of this prediction -/

/-- The compiled prediction is **model-conditional**: it is a consequence of the
declared cell model and of nothing stronger, and the status is computed from the
support cone rather than declared in the specification. -/
theorem epistemic_status_is_model_conditional :
    (compile spec).epistemicStatus = .modelConditional := rfl

/-- And an analogical step would weaken it, as the promotion discipline
requires: transporting this prediction to another system by analogy does not
keep its status. -/
theorem analogy_step_weakens_the_status :
    chain (compile spec).epistemicStatus [Step.analogy] = .speculativeAnalogy := rfl


/-! ## §9 A falsification, localised -/

/-- The temperature envelope of the compiled prediction. -/
def temperatureEnvelope : Set ℚ := (fun h => (spec.finalState h).temp) '' spec.admissibleSet

/-- **The derivation behind the envelope**, with its dependencies made explicit.
The prediction is sound provided the true cell is among the admissible
hypotheses and the instrument reports its temperature faithfully; those two
conditions are attached to the `missingStateVariable` and `badMeasurement`
classes respectively, and the soundness field *proves* the implication rather
than assuming it. -/
def temperatureDerivation (trueH : Fin 3) (observed : ℚ) : Derivation ℚ where
  correct := fun c => match c with
    | .missingStateVariable => spec.admissible trueH = true
    | .badMeasurement => observed = (spec.finalState trueH).temp
    | _ => True
  envelope := temperatureEnvelope
  actual := observed
  sound := fun h => ⟨trueH, h .missingStateVariable, (h .badMeasurement).symm⟩

/-- `350` is outside the envelope: the two admissible hypotheses predict `310`
and `320`. -/
theorem threeFifty_outside_envelope : (350 : ℚ) ∉ temperatureEnvelope := by
  rintro ⟨h, ha, he⟩
  have hadm : spec.admissible h = true := ha
  fin_cases h
  · simp only [final_temperature] at he; norm_num [initial] at he
  · simp only [final_temperature] at he; norm_num [initial] at he
  · exact absurd hadm (by decide)

/-- **The loop, closed on this experiment.**  An observed final temperature of
`350` falsifies the compiled prediction, and the falsification localises to a
declared dependency: either the true cell was not among the admissible
hypotheses (a missing state variable or a wrong parameter range) or the
instrument misreported.  It does **not** license "the model is wrong". -/
theorem observing_350_localises (trueH : Fin 3) :
    ∃ c, ¬ (temperatureDerivation trueH 350).correct c :=
  falsification_localises_to_a_dependency _ threeFifty_outside_envelope

/-- **And it does not localise further.**  Two repairs of that falsification
blame different classes and both accommodate the observation, so the next step
is an experiment that discriminates them — which is the measurement-value
question again, now asked of the repair set. -/
theorem two_repairs_of_the_overheat (trueH : Fin 3) :
    ∃ r₁ r₂ : Repair ℚ (temperatureDerivation trueH 350), r₁.target ≠ r₂.target := by
  refine ⟨⟨.wrongParameter, Set.Icc 300 360, ?_⟩, ⟨.missingStateVariable, {350}, rfl⟩, ?_⟩
  · exact Set.mem_Icc.mpr (by norm_num [temperatureDerivation])
  · simp

/-! ## §10 Data-driven model selection on this cell

The admissible flag above was *declared*.  This section derives it instead, by
running the generic selection of `Integration.Experiment.ModelSelection` on an
observed trace, and records what selection can and cannot do here. -/

open Integration.Experiment.ModelSelection

/-- The voltmeter/ammeter pair, compared exactly. -/
def instrument : InstrumentModel (ℚ × ℚ) := exactInstrument _

/-- **Selection keeps the truth.**  Observing the voltage-and-current trace that
the low-resistance cell actually produces keeps that hypothesis in the derived
admissible set. -/
theorem observation_keeps_the_truth :
    (refine spec instrument (spec.traceOf 0)).admissible 0 = true :=
  truth_survives_exact_observation spec instrument 0 (by decide)

/-- **But selection cannot choose.**  Whatever is observed, the two colliding
cells are kept or dropped together: their predicted traces are equal, so no
amount of data from this instrumentation separates them. -/
theorem data_does_not_select (y : List (ℚ × ℚ)) :
    (refine spec instrument y).admissible 0 = (refine spec instrument y).admissible 1 :=
  data_cannot_separate_identical_traces spec instrument y traces_agree (by decide)

/-- **So the derived set is still not a point.**  After the ideal observation,
the surviving family has at least two members, and the thermal-risk question is
still open — which is exactly why the compiler's answer is a new sensor rather
than more data. -/
theorem observing_the_trace_leaves_the_pair :
    ¬ (refine spec instrument (spec.traceOf 0)).admissibleSet.Subsingleton :=
  surviving_pair_is_not_a_selection spec instrument (spec.traceOf 0) (by decide) traces_agree
    (by decide) observation_keeps_the_truth

/-! ## §11 The propagated variance (data only)

The specification now declares, besides the two sensitivities, the independent
input variances they multiply.  The compiler *computes* the propagated variance
from them; the three theorems below record the computed value, identify it with
first-order propagation `J Σ Jᵀ`, and record honestly that the declared
uncertainty budget is still **not** derived from it.
-/

open Integration.Experiment.CertifiedPropagation

/-- **The compiler computes the propagated variance.**  With
`(∂T/∂R, ∂T/∂I) = (10, 20)` and independent input variances `10⁻⁴`, first-order
propagation gives `10² · 10⁻⁴ + 20² · 10⁻⁴ = 1/20`. -/
theorem propagated_variance_is_computed :
    (compile spec).propagatedVariance = 1 / 20 := by
  rw [compile_propagatedVariance]
  norm_num [spec]

/-- **And the number is `Cov.push`**, not a separate formula: it is the `(0,0)`
entry of `J Σ Jᵀ` for the declared row and the diagonal input covariance. -/
theorem propagated_variance_is_the_push :
    (compile spec).propagatedVariance
      = propagatedVariance ![10, 20] ![1 / 10000, 1 / 10000]
          (by intro i; fin_cases i <;> norm_num) := by
  refine compile_propagatedVariance_eq_push spec ![10, 20] ![1 / 10000, 1 / 10000]
    (by intro i; fin_cases i <;> norm_num) ?_
  simp [spec, ofRow, List.ofFn_succ]

/-- **The declared budget is still declared.**  The computed propagated variance
agrees with no entry of the specification's uncertainty budget and with its
quantified total: populating the budget from the graph remains an open
obligation, and nothing here silently does it. -/
theorem propagated_variance_is_not_the_declared_budget :
    (compile spec).propagatedVariance ≠ spec.budget.measurement ∧
      (compile spec).propagatedVariance ≠ spec.budget.parameter ∧
      (compile spec).propagatedVariance ≠ spec.budget.quantifiedTotal := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [propagated_variance_is_computed] <;>
    norm_num [spec, Budget.quantifiedTotal]

end Integration.Experiment.Lithium
