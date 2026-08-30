import Integration.Experiment.ContinuousDynamics
import Integration.Experiment.JacobianSensitivity
import Integration.Experiment.BestReading

/-!
# Stage 4 milestone — a continuously parameterised dynamical lithium experiment

This file is the Stage-4 acceptance instance.  It is **data only**: every
architectural conclusion is an instantiation of a generic theorem from
`Integration.Experiment.ParameterRegion` or
`Integration.Experiment.ContinuousDynamics`.

The experiment:

```
ż = -θ            (state of charge under a galvanostatic hold, θ = η I / Q_cap)
z(0) = 0.9,       T = 10,        y = z
θ ∈ [0.02, 0.04]  (the declared parameter family — a continuum, not a list)
```

The milestone asks the calculus to:

1. take a **continuously parameterised dynamical model** — `cellFamily`, whose
   predictions are proved to be the trajectories of the ODE
   (`predict_is_the_trajectory`);
2. take a **measured series** — one reading at `t = 4` — and derive the
   **surviving parameter region** exactly: `Θ_E = [0.0275, 0.0325]`
   (`surviving_region_after_the_first_reading`), a strict contraction of the
   prior (`first_reading_contracts`);
3. **propagate the region** to a prediction envelope
   (`endpoint_envelope_after_the_first_reading` : `[0.575, 0.625]`) and to a
   risk envelope (`risk_unresolved_after_the_first_reading` : both verdicts are
   still possible, so the safety question is open);
4. **choose the next measurement**: the reading at `t = 10` is steeper in the
   parameter than one at `t = 4`, so it contracts the region more
   (`endpoint_reading_is_more_discriminating`), and it does resolve the risk
   question (`risk_resolved_after_the_endpoint_reading`), which the repeated
   early reading does not;
5. **report family failure** when it occurs: an observation of `0.5` at `t = 4`
   is compatible with no parameter in the declared family, so the family is
   falsified and the calculus reports an empty envelope rather than a
   nearest-parameter answer (`family_is_falsified_by_the_low_reading`,
   `falsified_family_predicts_nothing`).

Two further links: the endpoint consumer's sensitivity to the parameter is a
*certified* derivative (`endpoint_sensitivity_is_certified`), not a declared
number; and the surviving region is a genuine interval, so the envelope has the
reportable shape of `envelope_eq_Icc`.

**Claim boundary.** Nothing here is a claim about lithium cells. `z` is a real
number, `θ` is a real number in a declared interval, the "hazard" is a declared
threshold, and the numbers are chosen to exercise the calculus.  As in Stage 3,
the portability of the machinery — not any number in this file — is the result.
-/

namespace Integration.Experiment.LithiumContinuous

open Set
open Integration.Experiment.ParameterRegion
open Integration.Experiment.ContinuousDynamics
open Integration.Experiment.JacobianSensitivity
open Integration.Experiment.BestReading

/-! ## §1 The declared model family -/

/-- The run length. -/
def horizon : ℝ := 10

/-- The initial state of charge. -/
def soc₀ : ℝ := 0.9

/-- The declared parameter region: the discharge rate `θ = η I / Q_cap` is known
only to lie in this interval. -/
def prior : Set ℝ := Icc 0.02 0.04

/-- The predicted state of charge under parameter `θ`. -/
def soc (θ : ℝ) : ℝ → ℝ := affineSolution soc₀ (-θ)

@[simp] theorem soc_apply (θ t : ℝ) : soc θ t = 0.9 - θ * t := by
  simp [soc, affineSolution, soc₀]; ring

/-- **The model family**, presented as an affine-in-parameter family so that the
quantitative discrimination theorems of lane 1 apply. -/
def cellFamily : ParamFamily ℝ :=
  affineFamily prior (fun _ => soc₀) (fun t => -t)

@[simp] theorem cellFamily_predict (θ t : ℝ) : cellFamily.predict θ t = 0.9 - t * θ := by
  simp [cellFamily, soc₀]; ring

@[simp] theorem cellFamily_prior : cellFamily.prior = prior := rfl

/-- **The family's predictions are the trajectories of the ODE.**  Each `soc θ`
solves `ż = -θ` with `z(0) = 0.9`, and the family's `predict` is that solution
observed directly, so the lane-1 machinery below is applied to a dynamical
model, not to a curve fit. -/
theorem predict_is_the_trajectory (θ : ℝ) :
    (constantRate horizon (by norm_num [horizon]) soc₀ (-θ)).IsTrajectory (soc θ) ∧
      ∀ t, cellFamily.predict θ t = soc θ t := by
  refine ⟨affine_isTrajectory horizon (by norm_num [horizon]) soc₀ (-θ), fun t => ?_⟩
  simp [mul_comm]

/-- And the trajectory is the *only* one, so the prediction is not a modelling
choice. -/
theorem trajectory_is_unique (θ : ℝ) {x : ℝ → ℝ}
    (hx : (constantRate horizon (by norm_num [horizon]) soc₀ (-θ)).IsTrajectory x) :
    EqOn x (soc θ) (Icc 0 horizon) :=
  affineSolution_unique horizon (by norm_num [horizon]) soc₀ (-θ) hx

/-! ## §2 The measured series and the surviving region -/

/-- The measurement at `t = 4`: the state of charge read `0.78`, with a declared
tolerance of `0.01`. -/
def reading4 : Reading := ⟨4, 0.78, 0.01, by norm_num⟩

/-- **The surviving parameter region, exactly.**  One reading turns the declared
interval `[0.02, 0.04]` into `[0.0275, 0.0325]`. -/
theorem surviving_region_after_the_first_reading :
    Compatible cellFamily [reading4] = Icc 0.0275 0.0325 := by
  ext θ
  simp only [mem_compatible, cellFamily_prior, prior, mem_Icc, List.mem_singleton]
  constructor
  · rintro ⟨⟨hp1, hp2⟩, hf⟩
    have h : |(0.78 : ℝ) - (0.9 - 4 * θ)| ≤ 0.01 := by
      have := hf reading4 rfl
      simpa [Fits, reading4] using this
    rw [abs_le] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rintro r rfl
    have : |(0.78 : ℝ) - (0.9 - 4 * θ)| ≤ 0.01 := by
      rw [abs_le]; constructor <;> linarith
    simpa [Fits, reading4] using this

/-- The reading is a strict contraction of the declared family: the region is
smaller, and still contains the parameter that generated the data. -/
theorem first_reading_contracts :
    Compatible cellFamily [reading4] ⊂ cellFamily.prior := by
  rw [surviving_region_after_the_first_reading]
  constructor
  · intro θ hθ
    simp only [cellFamily_prior, prior, mem_Icc] at *
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  · intro hsub
    have : (0.02 : ℝ) ∈ Icc (0.0275 : ℝ) 0.0325 :=
      hsub (Set.mem_Icc.mpr ⟨le_refl _, by norm_num⟩)
    simp at this
    linarith [this]

/-- The true parameter `θ* = 0.03`, which generated the reading, survives. -/
theorem truth_survives_the_first_reading : (0.03 : ℝ) ∈ Compatible cellFamily [reading4] := by
  rw [surviving_region_after_the_first_reading]
  constructor <;> norm_num

/-- The surviving region is a genuine interval, so
`Integration.Experiment.ParameterRegion.envelope_eq_Icc` applies to it. -/
theorem surviving_region_is_an_interval :
    (Compatible cellFamily [reading4]).OrdConnected ∧
      IsCompact (Compatible cellFamily [reading4]) ∧
      (Compatible cellFamily [reading4]).Nonempty := by
  rw [surviving_region_after_the_first_reading]
  exact ⟨ordConnected_Icc, isCompact_Icc, ⟨0.03, by constructor <;> norm_num⟩⟩

/-! ## §3 Propagating the region: prediction and risk envelopes -/

/-- The prediction consumer: the state of charge at the end of the run. -/
def endpointSoc (θ : ℝ) : ℝ := 0.9 - 10 * θ

/-- **The prediction envelope.**  The surviving region maps onto the interval
`[0.575, 0.625]` of end-of-run states of charge. -/
theorem endpoint_envelope_after_the_first_reading :
    envelope cellFamily [reading4] endpointSoc = Icc 0.575 0.625 := by
  rw [envelope, surviving_region_after_the_first_reading]
  ext y
  simp only [mem_image, mem_Icc, endpointSoc]
  constructor
  · rintro ⟨θ, ⟨h1, h2⟩, rfl⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    exact ⟨(0.9 - y) / 10, ⟨by linarith, by linarith⟩, by ring⟩

/-- The declared hazard: the cell ends the run below `0.58` state of charge. -/
noncomputable def deepDischarge (θ : ℝ) : Bool := decide (0.9 - 10 * θ < 0.58)

/-- **The risk envelope is not a verdict.**  After the first reading both
outcomes are still possible, so the safety question is open: this is the
continuous-parameter form of the Stage-3 "instrumentation insufficient for the
risk question". -/
theorem risk_unresolved_after_the_first_reading :
    riskEnvelope cellFamily [reading4] deepDischarge = {true, false} := by
  rw [riskEnvelope, surviving_region_after_the_first_reading]
  ext b
  simp only [mem_image, mem_insert_iff, mem_singleton_iff, mem_Icc]
  constructor
  · rintro ⟨θ, -, rfl⟩
    cases hb : deepDischarge θ
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact ⟨0.0325, ⟨by norm_num, by norm_num⟩, by norm_num [deepDischarge]⟩
    · exact ⟨0.0275, ⟨by norm_num, by norm_num⟩, by norm_num [deepDischarge]⟩

/-! ## §4 Which measurement next? -/

/-- A candidate follow-up: repeat the measurement at `t = 4` (predicted `0.78`
under the true parameter). -/
def repeat4 : Reading := ⟨4, 0.78, 0.01, by norm_num⟩

/-- A candidate follow-up: measure at the end of the run, `t = 10` (predicted
`0.6` under the true parameter). -/
def reading10 : Reading := ⟨10, 0.6, 0.01, by norm_num⟩

/-- **The endpoint measurement is the more discriminating one.**  Both readings
are what the true parameter `0.03` predicts, and both carry the same tolerance;
the endpoint reading's prediction depends more steeply on `θ`, so — by the
generic `steeper_reading_contracts_more` — every parameter it leaves alive is
also left alive by the repeat, and the region it produces is contained in the
other. -/
theorem endpoint_reading_is_more_discriminating :
    Compatible cellFamily (reading10 :: [reading4]) ⊆
      Compatible cellFamily (repeat4 :: [reading4]) :=
  steeper_reading_leaves_smaller_region prior (fun _ => soc₀) (fun t => -t) [reading4]
    repeat4 reading10 0.03
    (by norm_num [repeat4, soc₀]) (by norm_num [reading10, soc₀]) (by norm_num [repeat4, reading10])
    (by norm_num [repeat4, reading10])

/-- **And it resolves the risk question.**  After the endpoint reading every
surviving parameter gives the same safety verdict — the hazard does *not* occur
— so the risk envelope is a point. -/
theorem risk_resolved_after_the_endpoint_reading :
    riskEnvelope cellFamily [reading10, reading4] deepDischarge = {false} := by
  have hsub : Compatible cellFamily [reading10, reading4] ⊆ Icc (0.029 : ℝ) 0.031 := by
    rintro θ ⟨-, hf⟩
    have h : |(0.6 : ℝ) - (0.9 - 10 * θ)| ≤ 0.01 := by
      have := hf reading10 (by simp)
      simpa [Fits, reading10] using this
    rw [abs_le] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hmem : (0.03 : ℝ) ∈ Compatible cellFamily [reading10, reading4] := by
    refine ⟨by simp [prior]; constructor <;> norm_num, ?_⟩
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · have : |(0.6 : ℝ) - (0.9 - 10 * 0.03)| ≤ 0.01 := by norm_num
      simpa [Fits, reading10] using this
    · rcases List.mem_singleton.mp hr with rfl
      have : |(0.78 : ℝ) - (0.9 - 4 * 0.03)| ≤ 0.01 := by norm_num
      simpa [Fits, reading4] using this
  ext b
  simp only [riskEnvelope, mem_image, mem_singleton_iff]
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    obtain ⟨h1, h2⟩ := hsub hθ
    simp only [deepDischarge, decide_eq_false_iff_not, not_lt]
    linarith
  · rintro rfl
    exact ⟨0.03, hmem, by norm_num [deepDischarge]⟩

/-- The repeated early measurement, by contrast, leaves the region it already
had: re-observing what the surviving parameters already predict removes
nothing. -/
theorem repeating_the_early_reading_adds_nothing :
    Compatible cellFamily (repeat4 :: [reading4]) = Compatible cellFamily [reading4] := by
  ext θ
  constructor
  · exact fun h => compatible_cons_subset cellFamily repeat4 [reading4] h
  · rintro ⟨hp, hf⟩
    refine ⟨hp, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hf reading4 (by simp [reading4])
    · exact hf r hr

/-! ## §4b Selecting the best next measurement from a candidate set -/

/-- A third candidate follow-up: measure at `t = 7` (predicted `0.69` under the
true parameter). -/
def reading7 : Reading := ⟨7, 0.69, 0.01, by norm_num⟩

/-- The three candidate follow-up measurements offered to the calculus. -/
def candidates : List Reading := [reading7, reading10]

/-- **The calculus selects the endpoint measurement.**  Given the three
candidates `t = 4, 7, 10`, the generic selector of lane 1b — which maximises the
declared parameter sensitivity `|∂predict/∂θ| = t` — returns the reading at
`t = 10`. -/
theorem best_next_measurement_is_the_endpoint :
    steepest (fun t => -t) repeat4 candidates = reading10 := by
  rw [candidates, steepest, if_pos (by norm_num [repeat4, reading7]), steepest,
    if_pos (by norm_num [reading7, reading10]), steepest_nil]

/-- **And the selection is optimal over the whole candidate set**, not merely
better than one alternative: the region surviving the selected reading is
contained in the region surviving *any* offered candidate. -/
theorem selected_measurement_contracts_most (c : Reading) (hc : c ∈ repeat4 :: candidates) :
    Compatible cellFamily (reading10 :: [reading4]) ⊆ Compatible cellFamily (c :: [reading4]) := by
  have h := steepest_contracts_most (fun t => -t) prior (fun _ => soc₀) [reading4] 0.03
    repeat4 candidates 0.01 ?_ ?_ c hc
  · rwa [best_next_measurement_is_the_endpoint] at h
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · norm_num [repeat4, soc₀]
    · rcases List.mem_cons.mp hd with rfl | hd
      · norm_num [reading7, soc₀]
      · rcases List.mem_singleton.mp hd with rfl
        norm_num [reading10, soc₀]
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · norm_num [repeat4]
    · rcases List.mem_cons.mp hd with rfl | hd
      · norm_num [reading7]
      · rcases List.mem_singleton.mp hd with rfl
        norm_num [reading10]

/-- The same optimality for the prediction envelope: no offered measurement
produces a narrower endpoint prediction than the selected one. -/
theorem selected_measurement_gives_the_narrowest_envelope (c : Reading)
    (hc : c ∈ repeat4 :: candidates) (C : ℝ → ℝ) :
    envelope cellFamily (reading10 :: [reading4]) C ⊆ envelope cellFamily (c :: [reading4]) C :=
  Set.image_mono (selected_measurement_contracts_most c hc)

/-! ## §5 Failure of the whole family -/

/-- A reading at `t = 4` that no parameter in `[0.02, 0.04]` can produce. -/
def lowReading : Reading := ⟨4, 0.5, 0.01, by norm_num⟩

/-- **The declared family is falsified.**  The observation is outside the
tolerance of *every* parameter, so the failure is at the level of the model
family — a new parameter value cannot repair it. -/
theorem family_is_falsified_by_the_low_reading :
    FamilyFalsified cellFamily [lowReading] := by
  refine falsified_of_single_reading cellFamily lowReading (fun θ hp hfit => ?_)
  simp only [cellFamily_prior, prior, mem_Icc] at hp
  have h : |(0.5 : ℝ) - (0.9 - 4 * θ)| ≤ 0.01 := by
    simpa [Fits, lowReading] using hfit
  rw [abs_le] at h
  linarith [h.2, hp.2]

/-- **A falsified family predicts nothing.**  The calculus reports an empty
prediction envelope and an empty risk envelope, rather than the value of the
best-fitting parameter. -/
theorem falsified_family_predicts_nothing :
    envelope cellFamily [lowReading] endpointSoc = ∅ ∧
      riskEnvelope cellFamily [lowReading] deepDischarge = ∅ :=
  ⟨falsified_envelope_empty cellFamily [lowReading] endpointSoc
      family_is_falsified_by_the_low_reading,
   falsified_riskEnvelope_empty cellFamily [lowReading] deepDischarge
      family_is_falsified_by_the_low_reading⟩

/-- And no further data revives it. -/
theorem falsification_is_permanent (E : List Reading) :
    FamilyFalsified cellFamily (lowReading :: E) :=
  falsified_is_permanent cellFamily (E := [lowReading]) (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..)
    family_is_falsified_by_the_low_reading

/-! ## §6 The endpoint sensitivity is a certified derivative -/

/-- The endpoint state of charge as a function of the parameter vector `![θ]`. -/
def endpointLaw : (Fin 1 → ℝ) → ℝ := fun v => 0.9 - 10 * v 0

/-- **The sensitivity of the end-of-run state of charge to the discharge rate is
`-10`, and it is certified**: the number is the partial derivative of the law,
not an annotation travelling beside it. -/
noncomputable def endpointSensitivity (θ : ℝ) : CertifiedSensitivity 1 where
  f := endpointLaw
  point := ![θ]
  declared := ![-10]
  certificate := by
    intro j
    fin_cases j
    have hfun : (fun s : ℝ => endpointLaw (Function.update ![θ] 0 s)) = fun s => 0.9 - 10 * s := by
      funext s; simp [endpointLaw]
    have h : HasDerivAt (fun s : ℝ => endpointLaw (Function.update ![θ] 0 s)) (-10) (![θ] 0) := by
      rw [hfun]
      simpa using ((hasDerivAt_id (![θ] 0)).const_mul (10 : ℝ)).const_sub (0.9 : ℝ)
    simpa using h

/-- Stated as an equation with `deriv`. -/
theorem endpoint_sensitivity_is_certified (θ : ℝ) :
    (endpointSensitivity θ).declared 0 =
      deriv (fun s => endpointLaw (Function.update ![θ] 0 s)) (![θ] 0) :=
  (endpointSensitivity θ).declared_is_the_partial_derivative 0

end Integration.Experiment.LithiumContinuous
