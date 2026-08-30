import Integration.Experiment.Compiler
import Integration.Experiment.Lithium

/-!
# The second domain instance: a heated slab with a hidden interior node

The point of this file is **portability**.  It is a different kind of
experiment — a thermal-diffusion problem with a latent interior state rather
than an electrochemical one with a latent parameter — and it is expressed with
*exactly* the same objects: `ExperimentSpec`, `compile`, `Hazard`, `Sensor`,
`Resolves`, `Budget`.  No lane file was modified to accommodate it, and the
end-to-end results below are obtained by instantiating the same generic theorems
the lithium file instantiates.

## The setup

```
surface'  = surface + P dt                  (heater drives the surface)
interior' = interior + k (surface − interior) dt   (conduction inwards)
```

The instrument reads the **surface only**.  Two candidate slabs start with the
same surface temperature and different interior temperatures; their surface
traces are therefore identical for the whole run, and their interior
temperatures — the thing the hazard is about — differ at the end.

## What comes out

* `traces_agree`, `risks_differ` — the observational collision, in a different
  domain;
* `surface_probe_is_insufficient_for_the_interior_risk` — the same Lane-4
  verdict from the same generic theorem;
* `interior_envelope_is_not_a_point`;
* `recommendation_resolves_the_risk_question` — the same Lane-5 conclusion, with
  a *different* winning sensor: here an interior thermocouple, there a surface
  temperature probe or an impedance measurement;
* `same_calculus_two_domains` — the portability statement itself.

Nothing here is a claim about any real material or apparatus.
-/

namespace Integration.Experiment.ThermalDiffusion

open Integration.CoordinateSufficiency
open Integration.FactorisationCollision
open Integration.Experiment.Intervention
open Integration.Experiment.Uncertainty
open Integration.Experiment.Risk
open Integration.Experiment.MeasurementValue
open Integration.Experiment.Compiler

/-! ## §1 The slab model -/

/-- The state of the slab: the surface node, the hidden interior node, and the
conductivity between them. -/
structure SlabState where
  /-- Temperature of the instrumented surface node. -/
  surface : ℚ
  /-- Temperature of the hidden interior node. -/
  interior : ℚ
  /-- Conduction coefficient between the two nodes. -/
  conductivity : ℚ
  deriving DecidableEq

/-- One time step: the heater drives the surface, the surface drives the
interior. -/
def slabDynamics (dt : ℚ) : Dynamics SlabState ℚ where
  step := fun x p =>
    { surface := x.surface + p * dt,
      interior := x.interior + x.conductivity * (x.surface - x.interior) * dt,
      conductivity := x.conductivity }

/-- **The surface is not affected by the interior.**  Under a constant heater
power the surface temperature has a closed form that does not mention the
interior node or the conductivity — which is exactly why the surface probe
cannot see the hazard. -/
theorem surface_closed_form (x₀ : SlabState) (P : ℚ) (n : ℕ) :
    (trajectory (slabDynamics 1) x₀ (fun _ => P) n).surface = x₀.surface + n * P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [trajectory_succ]
    show (trajectory (slabDynamics 1) x₀ (fun _ => P) n).surface + P * 1 = _
    rw [ih]
    push_cast
    ring

/-! ## §2 The declared hypotheses -/

/-- Three candidate slabs.  `h₀` and `h₁` share a surface temperature and differ
in the interior; `h₂` is ruled out by the data. -/
def initial : Fin 3 → SlabState
  | 0 => ⟨300, 300, 1 / 2⟩
  | 1 => ⟨300, 320, 1 / 2⟩
  | 2 => ⟨350, 300, 1 / 2⟩

/-- The declared hazard: the hidden interior node exceeding its limit. -/
def interiorOverheat : Hazard SlabState :=
  { name := "interior node above 313", quantity := SlabState.interior, threshold := 313 }

/-- **The specification.**  Three steps of a constant heater power, one
prediction consumer (the interior temperature), one hazard, a three-way budget
whose model discrepancy is unquantified, and three candidate sensors. -/
def spec : ExperimentSpec (Fin 3) SlabState ℚ ℚ where
  initialState := initial
  controls := { control := fun _ => 10, horizon := 3 }
  dynamics := fun _ => slabDynamics 1
  observe := SlabState.surface
  admissible := fun h => h ≠ 2
  nominal := 0
  quantities := [{ name := "interior temperature", quantity := SlabState.interior }]
  hazards := [interiorOverheat]
  budget := { measurement := 1 / 4, parameter := 1, modelDiscrepancy := none }
  coverage := clampCoverage
  assumptions :=
    ["two-node lumped discretisation of the slab",
     "conduction coefficient constant over the run",
     "no radiative loss from the surface"]
  sensitivities := [("d(interior)/d(conductivity)", 20)]
  support := { origin := .modelConditional, steps := [] }
  candidateSensors :=
    [{ name := "surface temperature, repeated", readout := fun h => (initial h).surface },
     { name := "conductivity probe", readout := fun h => (initial h).conductivity },
     { name := "interior thermocouple", readout := fun h => (initial h).interior }]

@[simp] theorem spec_observe : spec.observe = SlabState.surface := rfl
@[simp] theorem spec_initialState : spec.initialState = initial := rfl
@[simp] theorem spec_horizon : spec.controls.horizon = 3 := rfl
@[simp] theorem spec_hazards : spec.hazards = [interiorOverheat] := rfl
@[simp] theorem spec_admissible (h : Fin 3) : spec.admissible h = decide (h ≠ 2) := rfl

/-- The interior thermocouple, named for reuse below. -/
def interiorSensor : Sensor (Fin 3) :=
  { name := "interior thermocouple", readout := fun h => (initial h).interior }

/-! ## §3 The observational collision -/

/-- The observation at step `n` is the surface temperature in closed form. -/
theorem spec_observation (h : Fin 3) (n : ℕ) :
    spec.observe (spec.stateAt h n) = (initial h).surface + n * 10 :=
  surface_closed_form (initial h) 10 n

/-- **The two surviving hypotheses produce identical traces.** -/
theorem traces_agree : spec.traceOf 0 = spec.traceOf 1 := by
  unfold ExperimentSpec.traceOf
  refine List.map_congr_left ?_
  intro n _
  rw [spec_observation, spec_observation]
  show (300 : ℚ) + n * 10 = 300 + n * 10
  rfl

/-- The interior temperature at the end of the run, under each hypothesis. -/
theorem final_interior_zero : (spec.finalState 0).interior = 625 / 2 := by
  show (trajectory (slabDynamics 1) (initial 0) (fun _ => (10 : ℚ)) 3).interior = 625 / 2
  norm_num [trajectory, slabDynamics, initial]

theorem final_interior_one : (spec.finalState 1).interior = 315 := by
  show (trajectory (slabDynamics 1) (initial 1) (fun _ => (10 : ℚ)) 3).interior = 315
  norm_num [trajectory, slabDynamics, initial]

/-- **And their risks differ**: the second slab's interior crosses the declared
limit, the first one's does not. -/
theorem risks_differ : spec.riskOf 0 ≠ spec.riskOf 1 := by
  have p0 : ¬ (313 : ℚ) < (spec.finalState 0).interior := by
    rw [final_interior_zero]; norm_num
  have p1 : (313 : ℚ) < (spec.finalState 1).interior := by
    rw [final_interior_one]; norm_num
  simp only [ExperimentSpec.riskOf, profile, spec_hazards, List.map_cons, List.map_nil,
    Hazard.exceeded, interiorOverheat, ne_eq, List.cons.injEq, and_true, decide_eq_decide]
  intro hiff
  exact p0 (hiff.mpr p1)

/-- **The Lane-4 verdict, in the second domain.**  The surface probe is
insufficient instrumentation for the interior hazard, and no post-processing of
its trace repairs that. -/
theorem surface_probe_is_insufficient_for_the_interior_risk :
    ¬ Determines spec.traceOf spec.riskOf ∧
      ∀ f : List ℚ → List Bool, ¬ ∀ h, spec.riskOf h = f (spec.traceOf h) :=
  instrumentation_insufficient_for_the_risk_question
    (by decide : (0 : Fin 3) ≠ 1) traces_agree risks_differ

/-- **The envelope is not a point.** -/
theorem interior_envelope_is_not_a_point :
    ¬ ((fun h => (spec.finalState h).interior) '' spec.admissibleSet).Subsingleton := by
  have m0 : (0 : Fin 3) ∈ spec.admissibleSet := by simp [ExperimentSpec.admissibleSet]
  have m1 : (1 : Fin 3) ∈ spec.admissibleSet := by simp [ExperimentSpec.admissibleSet]
  intro hsub
  have := hsub ⟨0, m0, final_interior_zero⟩ ⟨1, m1, final_interior_one⟩
  norm_num at this

/-- The first entry of a predicted trace is the initial surface temperature. -/
theorem trace_head (h : Fin 3) : (spec.traceOf h)[0]? = some ((initial h).surface) := by
  simp [ExperimentSpec.traceOf, ExperimentSpec.stateAt]

/-! ## §4 Which measurement to take next -/

/-- **An interior thermocouple resolves the risk question.** -/
theorem interior_sensor_resolves :
    Resolves spec.traceOf interiorSensor.readout spec.riskOf := by
  intro x y hxy
  have hread : (initial x).interior = (initial y).interior := congrArg Prod.snd hxy
  have htr : spec.traceOf x = spec.traceOf y := congrArg Prod.fst hxy
  have hsurf : (initial x).surface = (initial y).surface := by
    have h0 : (spec.traceOf x)[0]? = (spec.traceOf y)[0]? := by rw [htr]
    rw [trace_head, trace_head] at h0
    simpa using h0
  have hk : (initial x).conductivity = (initial y).conductivity := by
    fin_cases x <;> fin_cases y <;> rfl
  have hstate : initial x = initial y := by
    cases hx : initial x
    cases hy : initial y
    rw [hx] at hsurf hread hk
    rw [hy] at hsurf hread hk
    simp_all
  have hfin : spec.finalState x = spec.finalState y := by
    show trajectory (slabDynamics 1) (initial x) (fun _ => (10 : ℚ)) 3 =
      trajectory (slabDynamics 1) (initial y) (fun _ => (10 : ℚ)) 3
    rw [hstate]
  simp [ExperimentSpec.riskOf, hfin]

/-- **A repeated surface reading does not.** -/
theorem surface_repeat_does_not_resolve :
    ¬ Resolves spec.traceOf (fun h => (initial h).surface) spec.riskOf := by
  intro hres
  refine risks_differ (hres 0 1 ?_)
  simp only [joint, Prod.mk.injEq]
  exact ⟨traces_agree, rfl⟩

/-- Hence some declared candidate resolves the question. -/
theorem some_candidate_resolves_the_risk_question :
    ∃ t ∈ spec.candidateSensors, Resolves spec.traceOf t.readout spec.riskOf :=
  ⟨interiorSensor, by simp [spec, interiorSensor], interior_sensor_resolves⟩

/-- **The recommendation is adequate** — by the same generic Lane-5 theorem used
in the electrochemical instance. -/
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

/-! ## §5 Portability -/

/-- **The portability statement.**  Two experiments in unrelated domains, with
different state spaces, different dynamics, different observation types and
different winning sensors, are specifications for the *same* compiler and
inherit the *same* guarantees: the truth stays inside the compiled envelope, the
risk verdict is the collision verdict, and the recommendation is adequate
whenever any candidate is. -/
theorem same_calculus_two_domains :
    (∃ s, (compile spec).recommendedMeasurement = some s ∧
        Resolves spec.traceOf s.readout spec.riskOf) ∧
      (∃ s, (compile Integration.Experiment.Lithium.spec).recommendedMeasurement = some s ∧
        Resolves Integration.Experiment.Lithium.spec.traceOf s.readout
          Integration.Experiment.Lithium.spec.riskOf) :=
  ⟨recommendation_resolves_the_risk_question,
    Integration.Experiment.Lithium.recommendation_resolves_the_risk_question⟩

end Integration.Experiment.ThermalDiffusion
