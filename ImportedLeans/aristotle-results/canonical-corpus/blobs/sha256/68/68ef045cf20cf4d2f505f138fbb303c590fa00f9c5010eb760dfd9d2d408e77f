import Mathlib
import Integration.Experiment.LithiumContinuous
import Integration.Experiment.CoverageSemantics
import Integration.Experiment.ContinuousBayes
import Integration.Experiment.VarianceBudget
import Integration.Experiment.TrajectorySensitivity
import Integration.Experiment.RepairObligations

/-!
# Stage 6 milestone — one synthetic dynamical experiment, calibrated end to end

This file is the Stage-6 acceptance instance.  It is **data only**: every
conclusion is an instantiation of a generic theorem from one of the Stage-4/5/6
lanes, applied to the single dynamical experiment of
`Integration.Experiment.LithiumContinuous`:

```
ż = -θ,   z(0) = 0.9,   T = 10,   y = z,   θ ∈ [0.02, 0.04]
```

with one reading at `t = 4` of value `0.78` and declared tolerance `0.01`.

The milestone asks that a continuous dynamical model with a continuous parameter
family, a measurement model and certified derivatives should yield, in one pass:

| Milestone item | Theorem here |
|---|---|
| certified trajectory sensitivity | `cell_trajectory_sensitivity`, `cell_sensitivity_is_the_theta_derivative` |
| confidence region | `cell_region_is_a_coverage_one_procedure` |
| posterior over a continuous parameter | `cell_evidence_pos`, `cell_posterior_is_a_density` |
| posterior support inside the deterministic region | `cell_posterior_support_subset_surviving_region` |
| prediction interval | `endpoint_envelope_after_the_first_reading` (Stage 4, reused) |
| derived uncertainty budget with shares | `cell_budget_total`, `initial_state_dominates` |
| optimal next measurement | `endpoint_is_the_most_sensitive_time`, `perfecting_the_initial_state_helps_most` |
| model-family refutation | `family_is_falsified_by_the_low_reading` (Stage 4, reused) |
| a *classified*, refutable repair | `cellRepairProposal` |

## Claim boundary

Nothing here is a claim about a real lithium cell.  A "cell" is an affine
function of two rationals, a "measurement" is a real number with a declared
tolerance, and the noise model is a two-point distribution chosen to illustrate
the coverage statement.  The content is that the Stage-6 machinery composes on a
single instance, not any number in it.
-/

namespace Integration.Experiment.CalibratedCell

open Set
open Integration.Experiment.ParameterRegion
open Integration.Experiment.LithiumContinuous
open Integration.Experiment.CoverageSemantics
open Integration.Experiment.JacobianSensitivity
open Integration.Experiment.VarianceBudget
open Integration.Experiment.RepairObligations

/-! ## §1 The certified trajectory sensitivity -/

/-- The cell as a parameterised system with certified field partials:
`f = -θ`, `f_x = 0`, `f_θ = -1`. -/
noncomputable def cellSystem : TrajectorySensitivity.ParamSystem :=
  TrajectorySensitivity.constantRate 10 (by norm_num) 0.9

/-- **The trajectory sensitivity of the cell is `s(t) = -t`**, as the solution of
the variational equation — not as a declared number. -/
theorem cell_trajectory_sensitivity (θ : ℝ) :
    cellSystem.IsSensitivity θ (fun t => 0.9 - θ * t) (fun t => -t) :=
  TrajectorySensitivity.constantRate_isSensitivity 10 (by norm_num) 0.9 θ

/-- And in this instance it really is `∂z/∂θ`. -/
theorem cell_sensitivity_is_the_theta_derivative (θ t : ℝ) :
    HasDerivAt (fun p : ℝ => soc p t) (-t) θ := by
  simp only [soc_apply]
  simpa using (((hasDerivAt_id θ).mul_const t).const_sub (0.9 : ℝ))

/-! ## §2 The surviving region is a coverage-one confidence procedure -/

/-- The two possible readings under a `±0.01` noise model at the true parameter
`θ* = 0.03`, whose noiseless prediction at `t = 4` is `0.78`. -/
noncomputable def cellObs : Bool → ℝ := fun w => cond w 0.79 0.77

/-- The sampling law of the experiment: the two noise outcomes are equally
likely. -/
noncomputable def cellSampling : SamplingModel ℝ Bool where
  law := fun _ =>
    { mass := fun _ => 1/2
      nonneg := by intro w; norm_num
      total := by rw [Fintype.sum_bool]; norm_num }

/-- **The deterministic surviving region is a coverage-one procedure at the
generating parameter.**  Whichever of the two noise outcomes occurs, the region
compatible with the observed reading contains `θ* = 0.03`.

This is the instance of `tolerance_procedure_has_full_coverage`: the set-valued
admissibility shell of Stage 4 carries a frequentist guarantee once the noise is
known to be inside the declared tolerance. -/
theorem cell_region_is_a_coverage_one_procedure :
    coverageProb cellSampling
      (toleranceProcedure cellFamily 4 0.01 (by norm_num) cellObs) 0.03 = 1 := by
  refine tolerance_procedure_has_full_coverage cellSampling cellFamily 4 0.01
    (by norm_num) cellObs 0.03 ?_ ?_
  · show (0.03 : ℝ) ∈ prior
    constructor <;> norm_num
  · intro w _
    cases w <;> · simp only [cellObs, cellFamily_predict, Bool.cond_true, Bool.cond_false]
                  rw [abs_le]; constructor <;> norm_num

/-! ## §3 A posterior density over the continuous parameter -/

/-- The uniform prior on the declared parameter interval `[0.02, 0.04]`. -/
noncomputable def cellPrior : ContinuousBayes.ParamPrior where
  lo := 0.02
  hi := 0.04
  hlo := by norm_num
  density := fun _ => 50
  nonneg := fun _ => by norm_num
  total := by
    rw [intervalIntegral.integral_const]
    norm_num

/-- A tolerance-shaped likelihood for the reading at `t = 4`: it is positive
exactly on the parameters strictly inside the declared tolerance, and continuous,
so the evidence integral is an honest Riemann integral. -/
noncomputable def cellLikelihood : ℝ → ℝ := fun θ => max 0 (0.01 - 4 * |θ - 0.03|)

theorem cellLikelihood_nonneg (θ : ℝ) : 0 ≤ cellLikelihood θ := le_max_left _ _

theorem cellLikelihood_continuous : Continuous cellLikelihood := by
  unfold cellLikelihood
  fun_prop

/-- A positive likelihood confines the parameter to the open tolerance
interval. -/
theorem cellLikelihood_pos_abs {θ : ℝ} (h : 0 < cellLikelihood θ) : |θ - 0.03| < 0.0025 := by
  have h' : 0 < 0.01 - 4 * |θ - 0.03| := by
    rcases max_cases (0 : ℝ) (0.01 - 4 * |θ - 0.03|) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [cellLikelihood, he] at h; exact absurd h (lt_irrefl 0)
    · rw [cellLikelihood, he] at h; exact h
  linarith

/-- A positive likelihood means the reading is fitted in the Stage-4 sense. -/
theorem cellLikelihood_pos_fits {θ : ℝ} (h : 0 < cellLikelihood θ) :
    Fits cellFamily θ reading4 := by
  have habs := abs_lt.1 (cellLikelihood_pos_abs h)
  show |reading4.value - cellFamily.predict θ reading4.time| ≤ reading4.tol
  simp only [reading4, cellFamily_predict]
  rw [abs_le]
  constructor <;> linarith [habs.1, habs.2]

/-- And to a parameter the declaration already allowed. -/
theorem cellLikelihood_pos_prior {θ : ℝ} (h : 0 < cellLikelihood θ) : θ ∈ cellFamily.prior := by
  have habs := abs_lt.1 (cellLikelihood_pos_abs h)
  show θ ∈ prior
  constructor <;> [linarith [habs.1]; linarith [habs.2]]

/-- **There is evidence**: the normalising constant is positive, so the posterior
density exists. -/
theorem cell_evidence_pos : 0 < ContinuousBayes.evidence cellPrior cellLikelihood := by
  have hcont : Continuous (fun θ => cellLikelihood θ * cellPrior.density θ) := by
    exact cellLikelihood_continuous.mul continuous_const
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun θ => cellLikelihood θ * cellPrior.density θ)
      MeasureTheory.volume a b := fun a b => hcont.intervalIntegrable a b
  have hnn : ∀ θ, 0 ≤ cellLikelihood θ * cellPrior.density θ := fun θ =>
    mul_nonneg (cellLikelihood_nonneg θ) (cellPrior.nonneg θ)
  have hmid : 0 < ∫ θ in (0.0275 : ℝ)..0.0325, cellLikelihood θ * cellPrior.density θ := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hint _ _) (fun θ hθ => ?_) (by norm_num)
    have h1 : |θ - 0.03| < 0.0025 := by
      rw [abs_lt]
      constructor <;> [linarith [hθ.1]; linarith [hθ.2]]
    have : 0 < 0.01 - 4 * |θ - 0.03| := by linarith
    have hL : 0 < cellLikelihood θ := lt_of_lt_of_le this (le_max_right _ _)
    exact mul_pos hL (by show (0:ℝ) < 50; norm_num)
  have hleft : 0 ≤ ∫ θ in (0.02 : ℝ)..0.0275, cellLikelihood θ * cellPrior.density θ :=
    intervalIntegral.integral_nonneg (by norm_num) (fun θ _ => hnn θ)
  have hright : 0 ≤ ∫ θ in (0.0325 : ℝ)..0.04, cellLikelihood θ * cellPrior.density θ :=
    intervalIntegral.integral_nonneg (by norm_num) (fun θ _ => hnn θ)
  have hsplit : ContinuousBayes.evidence cellPrior cellLikelihood
      = (∫ θ in (0.02 : ℝ)..0.0275, cellLikelihood θ * cellPrior.density θ)
        + (∫ θ in (0.0275 : ℝ)..0.0325, cellLikelihood θ * cellPrior.density θ)
        + (∫ θ in (0.0325 : ℝ)..0.04, cellLikelihood θ * cellPrior.density θ) := by
    rw [ContinuousBayes.evidence]
    show (∫ θ in (0.02 : ℝ)..0.04, cellLikelihood θ * cellPrior.density θ) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0.02 0.0275) (hint 0.0275 0.04),
      ← intervalIntegral.integral_add_adjacent_intervals (hint 0.0275 0.0325) (hint 0.0325 0.04)]
    ring
  rw [hsplit]
  linarith

/-- The posterior is a genuine probability density on the parameter interval. -/
theorem cell_posterior_is_a_density :
    ∫ θ in cellPrior.lo..cellPrior.hi, ContinuousBayes.posterior cellPrior cellLikelihood θ = 1 :=
  ContinuousBayes.posterior_integral_eq_one cellPrior cellLikelihood (ne_of_gt cell_evidence_pos)

/-- **The architecture is preserved**: the support of the posterior density lies
inside the surviving parameter region, which is the deterministic
`[0.0275, 0.0325]` that one reading already produced.  Probability adds weights
*inside* the admissibility shell rather than replacing it. -/
theorem cell_posterior_support_subset_compatible :
    {θ | 0 < ContinuousBayes.posterior cellPrior cellLikelihood θ}
      ⊆ Compatible cellFamily [reading4] := by
  intro θ hθ
  have hpos := (ContinuousBayes.posterior_pos_iff cellPrior cellLikelihood
    cellLikelihood_nonneg cell_evidence_pos θ).1 hθ
  refine ⟨cellLikelihood_pos_prior hpos.1, ?_⟩
  rintro r hr
  rcases List.mem_singleton.1 hr with rfl
  exact cellLikelihood_pos_fits hpos.1

theorem cell_posterior_support_subset_surviving_region :
    {θ | 0 < ContinuousBayes.posterior cellPrior cellLikelihood θ} ⊆ Icc 0.0275 0.0325 := by
  rw [← surviving_region_after_the_first_reading]
  exact cell_posterior_support_subset_compatible

/-! ## §4 The derived uncertainty budget of the endpoint prediction -/

/-- The endpoint state of charge as a function of the two uncertain inputs: the
initial state of charge and the discharge rate. -/
def endpointLaw2 : (Fin 2 → ℝ) → ℝ := fun v => v 0 - 10 * v 1

/-- Its certified sensitivity row `(∂y/∂z₀, ∂y/∂θ) = (1, -10)`. -/
noncomputable def endpointSensitivity2 (z θ : ℝ) : CertifiedSensitivity 2 where
  f := endpointLaw2
  point := ![z, θ]
  declared := ![1, -10]
  certificate := by
    intro j
    fin_cases j
    · have hfun : (fun s : ℝ => endpointLaw2 (Function.update ![z, θ] 0 s))
          = fun s => s - 10 * θ := by
        funext s; simp [endpointLaw2]
      have h : HasDerivAt (fun s : ℝ => endpointLaw2 (Function.update ![z, θ] 0 s)) 1 z := by
        rw [hfun]
        simpa using (hasDerivAt_id z).sub_const (10 * θ)
      simpa using h
    · have hfun : (fun s : ℝ => endpointLaw2 (Function.update ![z, θ] 1 s))
          = fun s => z - 10 * s := by
        funext s; simp [endpointLaw2]
      have h : HasDerivAt (fun s : ℝ => endpointLaw2 (Function.update ![z, θ] 1 s)) (-10) θ := by
        rw [hfun]
        simpa using ((hasDerivAt_id θ).const_mul (10 : ℝ)).const_sub z
      simpa using h

/-- The declared input variances: the initial state of charge is known to
`0.02` (variance `4·10⁻⁴`), the rate to `10⁻³` (variance `10⁻⁶`). -/
def inputVar : Fin 2 → ℝ := ![0.0004, 0.000001]

theorem inputVar_nonneg : ∀ i, 0 ≤ inputVar i := by
  intro i; fin_cases i <;> norm_num [inputVar]

/-- **The uncertainty budget of the endpoint prediction, derived from the graph**
rather than declared: `1²·(4·10⁻⁴) + (-10)²·10⁻⁶ = 5·10⁻⁴`. -/
theorem cell_budget_total (z θ : ℝ) :
    totalVariance (endpointSensitivity2 z θ).declared (RCov.diag inputVar inputVar_nonneg)
      = 0.0005 := by
  rw [totalVariance_diag]
  simp [ownShare, RCov.diag, Fin.sum_univ_two, endpointSensitivity2, inputVar]
  norm_num

/-- **Contribution shares: the initial state of charge dominates.**  Its share is
`4·10⁻⁴` against the rate's `10⁻⁴`. -/
theorem initial_state_dominates (z θ : ℝ) :
    ownShare (endpointSensitivity2 z θ).declared (RCov.diag inputVar inputVar_nonneg) 1
      ≤ ownShare (endpointSensitivity2 z θ).declared (RCov.diag inputVar inputVar_nonneg) 0 := by
  simp [ownShare, RCov.diag, endpointSensitivity2, inputVar]
  norm_num

/-- **Which measurement to improve**: perfecting the dominant input leaves the
smaller residual variance, so the next effort should go to the initial state of
charge and not to the rate.  This is a decision derived from the certified
derivatives and the input covariance, not from a declared modulus. -/
theorem perfecting_the_initial_state_helps_most (z θ : ℝ) :
    totalVariance (endpointSensitivity2 z θ).declared
        (RCov.diag (perfect inputVar 0) (perfect_nonneg inputVar_nonneg 0))
      ≤ totalVariance (endpointSensitivity2 z θ).declared
        (RCov.diag (perfect inputVar 1) (perfect_nonneg inputVar_nonneg 1)) :=
  reducing_the_dominant_helps_most _ _ inputVar_nonneg 0 1 (initial_state_dominates z θ)

/-! ## §5 The next measurement, chosen by the computed trajectory sensitivity -/

/-- **The endpoint is the most sensitive time.**  Ranking the candidate readings
by the *computed* trajectory sensitivity `s(t) = -t` selects the reading at
`t = 10`, agreeing with the Stage-4 selection that used the family's declared
slope. -/
theorem endpoint_is_the_most_sensitive_time (c : Reading)
    (hc : c ∈ [repeat4, reading7, reading10]) :
    |(-c.time)| ≤ |(-reading10.time)| := by
  fin_cases hc <;> norm_num [repeat4, reading7, reading10]

/-! ## §6 Refutation, and a classified refutable repair -/

/-- The measurement-model repair for the refuting low reading: the same dynamics
read through an instrument with a `-0.28` offset. -/
def offsetCellFamily : ParamFamily ℝ where
  prior := Icc 0.02 0.04
  predict := fun θ t => 0.9 - θ * t - 0.28

theorem offsetCellFamily_fits : (Compatible offsetCellFamily [lowReading]).Nonempty := by
  refine ⟨0.03, ⟨by constructor <;> norm_num, ?_⟩⟩
  rintro r hr
  rcases List.mem_singleton.1 hr with rfl
  show |lowReading.value - offsetCellFamily.predict 0.03 lowReading.time| ≤ lowReading.tol
  simp only [lowReading, offsetCellFamily]
  rw [abs_le]
  constructor <;> norm_num

/-- The repair is itself refutable: an exact reading of `0.9` at `t = 0` would
leave no parameter, so it risks something. -/
theorem offsetCellFamily_refutable : Refutable offsetCellFamily := by
  refine ⟨[⟨0, 0.9, 0, le_refl 0⟩], ?_, ?_⟩
  · intro r hr r' hr' _
    fin_cases hr; fin_cases hr'; rfl
  · ext θ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, hfits⟩
    have h : |(0.9 : ℝ) - (0.9 - θ * 0 - 0.28)| ≤ 0 := hfits ⟨0, 0.9, 0, le_refl 0⟩ (by simp)
    rw [show (0.9 : ℝ) - (0.9 - θ * 0 - 0.28) = 0.28 by ring] at h
    rw [abs_le] at h
    linarith [h.2]

/-- **The repair, classified and gated.**  The refuted family is repaired in the
*measurement-model* class, the repair restores fit, and — the field that makes
fit into evidence — it remains refutable.  Contrast
`RepairObligations.saturated_repair_is_no_proposal`: an unrestricted repair
would fit too, and would be rejected here. -/
def cellRepairProposal : RepairProposal ℝ where
  klass := RepairClass.measurementModel
  family := offsetCellFamily
  data := [lowReading]
  restoresFit := offsetCellFamily_fits
  isRefutable := offsetCellFamily_refutable

end Integration.Experiment.CalibratedCell
