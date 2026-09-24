import Integration.Experiment.ContinuousDynamics

/-!
# Stage 4 portability — a nonlinearly parameterised continuous experiment

`Integration.Experiment.LithiumContinuous` is the Stage-4 milestone instance,
and its parameter enters the prediction *affinely*.  This file is the
portability test for the continuous lane, in the spirit of the Stage-3
`ThermalDiffusion` file: a different domain, a different kind of dynamics
(exponential relaxation rather than a constant rate) and, crucially, a parameter
the prediction depends on **nonlinearly**, so none of the affine machinery of
lane 1 is available.

```
Ṫ = -(T - 300)/τ,     T(0) = 350,     τ ∈ [1, 4]
```

so `T(t) = 300 + 50 e^{-t/τ}`, and the unknown is the relaxation time `τ`.

What is proved, using only the *general* lemmas of
`Integration.Experiment.ParameterRegion` and
`Integration.Experiment.ContinuousDynamics`:

* `relaxation_isTrajectory`, `relaxation_is_the_only_trajectory` — the declared
  solution solves the ODE and is the only solution, so the family's predictions
  are the model's;
* `surviving_region_is_closed`, `surviving_region_is_an_interval`,
  `surviving_region_is_compact` — the surviving parameter region is a compact
  interval, established from `MonotoneOn`/`ContinuousOn` on the prior via
  `compatible_ordConnected_of_monotoneOn` and
  `compatible_isClosed_of_continuousOn`, i.e. without any affine structure;
* `endpoint_envelope_is_a_closed_interval` — hence the prediction envelope of
  the end-of-run temperature is a closed interval, by the generic
  `envelope_eq_Icc`;
* `fast_relaxation_is_excluded` — the measurement does real work: `τ = 1` is
  removed from the family (a genuine numerical exclusion, proved from Mathlib's
  bounds on `e`), while the generating parameter `τ = 2` survives.

**Claim boundary.** No claim about any thermal system: `T` is a real number,
`300`, `350`, `[1,4]` and the tolerance are declared constants, and the point of
the file is that the Stage-4 machinery transfers to a nonlinear parameterisation
unchanged.
-/

namespace Integration.Experiment.ThermalRC

open Set
open Integration.Experiment.ParameterRegion
open Integration.Experiment.ContinuousDynamics

/-! ## §1 The model -/

/-- Ambient temperature. -/
def ambient : ℝ := 300

/-- Initial temperature. -/
def initial : ℝ := 350

/-- Run length. -/
def horizon : ℝ := 10

/-- The declared parameter region: the relaxation time is known only to lie in
`[1, 4]`. -/
def prior : Set ℝ := Icc 1 4

/-- The predicted temperature under relaxation time `τ`. -/
noncomputable def temp (τ : ℝ) (t : ℝ) : ℝ := 300 + 50 * Real.exp (-t / τ)

/-- The relaxation system `Ṫ = -(T - 300)/τ`. -/
noncomputable def rcSystem (τ : ℝ) : ContinuousSystem Unit where
  horizon := horizon
  horizon_nonneg := by norm_num [horizon]
  init := initial
  control := fun _ => ()
  vf := fun _ x _ => -(x - 300) / τ

@[simp] theorem rcSystem_field (τ t x : ℝ) : (rcSystem τ).field t x = -(x - 300) / τ := rfl

/-- **The declared solution solves the equation.** -/
theorem relaxation_isTrajectory {τ : ℝ} (hτ : 0 < τ) :
    (rcSystem τ).IsTrajectory (temp τ) where
  init := by simp [temp, rcSystem, initial]; norm_num
  cont := by
    apply Continuous.continuousOn
    unfold temp
    fun_prop
  deriv := by
    intro t _
    have hd : HasDerivAt (fun s : ℝ => 300 + 50 * Real.exp (-s / τ))
        (50 * (Real.exp (-t / τ) * (-1 / τ))) t := by
      have h1 : HasDerivAt (fun s : ℝ => -s / τ) (-1 / τ) t := by
        simpa [neg_div] using (((hasDerivAt_id t).neg).div_const τ)
      exact ((h1.exp).const_mul (50 : ℝ)).const_add 300
    have hfield : (rcSystem τ).field t (temp τ t) = 50 * (Real.exp (-t / τ) * (-1 / τ)) := by
      simp only [rcSystem_field, temp]
      field_simp
      ring
    rw [hfield]
    exact (hd.congr_deriv rfl).hasDerivWithinAt

/-- The closed-loop field is Lipschitz for `τ ≥ 1`. -/
theorem rc_field_lipschitz {τ : ℝ} (hτ : 1 ≤ τ) (t : ℝ) :
    LipschitzWith 1 ((rcSystem τ).field t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hτ0 : 0 < τ := lt_of_lt_of_le zero_lt_one hτ
  simp only [rcSystem_field, Real.dist_eq]
  have h : -(x - 300) / τ - -(y - 300) / τ = -(x - y) / τ := by ring
  rw [h, abs_div, abs_neg, abs_of_pos hτ0, div_le_iff₀ hτ0]
  push_cast
  nlinarith [abs_nonneg (x - y)]

/-- **And it is the only solution**, so the prediction is the model's, not a
modelling choice. -/
theorem relaxation_is_the_only_trajectory {τ : ℝ} (hτ : 1 ≤ τ) {x : ℝ → ℝ}
    (hx : (rcSystem τ).IsTrajectory x) : EqOn x (temp τ) (Icc 0 horizon) :=
  trajectory_unique (K := 1) (fun t _ => rc_field_lipschitz hτ t) hx
    (relaxation_isTrajectory (lt_of_lt_of_le zero_lt_one hτ))

/-- The model family. -/
noncomputable def thermalFamily : ParamFamily ℝ where
  prior := prior
  predict := temp

@[simp] theorem thermalFamily_predict (τ t : ℝ) : thermalFamily.predict τ t = temp τ t := rfl

@[simp] theorem thermalFamily_prior : thermalFamily.prior = prior := rfl

/-! ## §2 Structure of the surviving region, without affine structure -/

/-- The prediction is monotone in the relaxation time, on the prior region, for
any nonnegative measurement time: a slower cell is hotter. -/
theorem temp_monotoneOn {t : ℝ} (ht : 0 ≤ t) : MonotoneOn (fun τ => temp τ t) prior := by
  intro a ha b hb hab
  have ha1 : (1 : ℝ) ≤ a := ha.1
  have hb1 : (1 : ℝ) ≤ b := hb.1
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha1
  have hdiv : -t / a ≤ -t / b := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    gcongr
  have := Real.exp_le_exp.mpr hdiv
  simp only [temp]
  linarith

/-- And it is continuous in the relaxation time on the prior region. -/
theorem temp_continuousOn (t : ℝ) : ContinuousOn (fun τ => temp τ t) prior := by
  have hne : ∀ τ ∈ prior, τ ≠ 0 := by
    intro τ hτ
    have : (1 : ℝ) ≤ τ := hτ.1
    linarith
  have hdiv : ContinuousOn (fun τ : ℝ => -t / τ) prior :=
    continuousOn_const.div continuousOn_id hne
  exact continuousOn_const.add (continuousOn_const.mul (Real.continuous_exp.comp_continuousOn hdiv))

/-- The measurement: at `t = 1` the temperature read exactly what `τ = 2`
predicts, with a declared tolerance of `1`. -/
noncomputable def reading1 : Reading :=
  ⟨1, 300 + 50 * Real.exp (-(1 : ℝ) / 2), 1, by norm_num⟩

/-- The generating parameter survives. -/
theorem truth_survives_the_reading : (2 : ℝ) ∈ Compatible thermalFamily [reading1] := by
  refine truth_survives_exact thermalFamily [reading1] 2 (by constructor <;> norm_num [prior]) ?_
  rintro r hr
  rcases List.mem_singleton.mp hr with rfl
  simp [reading1, temp]

/-- **The surviving region is closed** — from continuity alone. -/
theorem surviving_region_is_closed : IsClosed (Compatible thermalFamily [reading1]) := by
  refine compatible_isClosed_of_continuousOn thermalFamily [reading1] isClosed_Icc ?_
  intro r hr
  exact temp_continuousOn r.time

/-- **The surviving region is an interval** — from monotonicity alone, with no
affine structure available. -/
theorem surviving_region_is_an_interval : (Compatible thermalFamily [reading1]).OrdConnected := by
  refine compatible_ordConnected_of_monotoneOn thermalFamily [reading1] ordConnected_Icc ?_
  intro r hr
  rcases List.mem_singleton.mp hr with rfl
  exact Or.inl (temp_monotoneOn (by norm_num [reading1]))

/-- Hence it is compact. -/
theorem surviving_region_is_compact : IsCompact (Compatible thermalFamily [reading1]) :=
  IsCompact.of_isClosed_subset isCompact_Icc surviving_region_is_closed
    (compatible_subset_prior thermalFamily [reading1])

/-- The end-of-run temperature, as a consumer of the parameter. -/
noncomputable def endpointTemp (τ : ℝ) : ℝ := temp τ horizon

/-- **The prediction envelope is a closed interval**, by the generic
`envelope_eq_Icc`: the continuous lane reports the same shape of answer for a
nonlinear parameterisation as for the affine one. -/
theorem endpoint_envelope_is_a_closed_interval :
    envelope thermalFamily [reading1] endpointTemp =
      Icc (sInf (envelope thermalFamily [reading1] endpointTemp))
          (sSup (envelope thermalFamily [reading1] endpointTemp)) := by
  refine envelope_eq_Icc thermalFamily [reading1] endpointTemp
    ⟨2, truth_survives_the_reading⟩ surviving_region_is_compact surviving_region_is_an_interval ?_
  exact (temp_continuousOn horizon).mono (compatible_subset_prior thermalFamily [reading1])

/-! ## §3 The measurement does real work -/

/-- The numerical fact behind the exclusion: at `t = 1`, the `τ = 2` prediction
and the `τ = 1` prediction differ by more than the instrument's tolerance. -/
theorem predictions_differ_by_more_than_the_tolerance :
    |(300 + 50 * Real.exp (-(1:ℝ)/2)) - (300 + 50 * Real.exp (-(1:ℝ)/1))| > 1 := by
  have hE1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hE2 : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hu : Real.exp (-(1:ℝ)/2) * Real.exp (1/2) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hsq : Real.exp (1/2 : ℝ) * Real.exp (1/2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have he : Real.exp (-(1:ℝ)/1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]; norm_num
  have hupos : 0 < Real.exp (1/2 : ℝ) := Real.exp_pos _
  have hnpos : 0 < Real.exp (-(1:ℝ)/2) := Real.exp_pos _
  have hepos : 0 < Real.exp (-(1:ℝ)/1) := Real.exp_pos _
  have hult : Real.exp (1/2 : ℝ) < 1.65 := by nlinarith
  have h1 : Real.exp (-(1:ℝ)/2) > 0.606 := by nlinarith
  have h2 : Real.exp (-(1:ℝ)/1) < 0.368 := by nlinarith
  rw [abs_of_pos (by nlinarith)]
  nlinarith

/-- **The fast relaxation time is excluded by the data.**  `τ = 1` was in the
declared family and is not in the surviving region: the measurement is not
decorative. -/
theorem fast_relaxation_is_excluded : (1 : ℝ) ∉ Compatible thermalFamily [reading1] := by
  rintro ⟨-, hf⟩
  have h := hf reading1 (List.mem_singleton_self _)
  have hbad : |(300 + 50 * Real.exp (-(1:ℝ)/2)) - (300 + 50 * Real.exp (-(1:ℝ)/1))| ≤ 1 := by
    simpa [Fits, reading1, temp] using h
  exact absurd hbad (not_le.mpr predictions_differ_by_more_than_the_tolerance)

/-- So the region is a proper subset of the declared family. -/
theorem surviving_region_is_a_proper_subset :
    Compatible thermalFamily [reading1] ⊂ thermalFamily.prior := by
  refine ⟨compatible_subset_prior thermalFamily [reading1], fun hsub => ?_⟩
  exact fast_relaxation_is_excluded (hsub (by constructor <;> norm_num [prior]))

end Integration.Experiment.ThermalRC
