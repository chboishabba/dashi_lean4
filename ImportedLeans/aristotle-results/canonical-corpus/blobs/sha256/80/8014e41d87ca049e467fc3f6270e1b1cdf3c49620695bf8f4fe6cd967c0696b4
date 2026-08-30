/-
# How far the energy budget alone pushes concentration inward

`A_dyn` asks for a defect at the *velocity* scale `r ≍ M⁻¹`.  This file settles
exactly what the energy budget by itself can and cannot deliver.

* `ClayNS.oscOn_ge_of_local_energy` — the positive half.  If `‖u(x₀)‖ ≥ M` and
  the local energy on `B_r(x₀)` is at most `E`, then a plateau is impossible as
  soon as `(M/2)²·|B_r| > E`, and the oscillation on `B_r(x₀)` is at least
  `M/2`.
* `ClayNS.energy_scale_defect` — the sharp scale that this reaches:
  `r = A·M^{-2/3}`, with `A` depending only on the energy budget and **not** on
  `M`.  So a first singularity always has a defect at scale `M^{-2/3}`.
* `ClayNS.energy_criterion_vacuous_at_velocity_scale` — the negative half at the
  level of the criterion: at `r = c/M` the plateau budget is
  `c³·|B₁|/(4M) → 0`, so the hypothesis of the positive theorem fails for every
  fixed `E > 0` once `M` is large.
* `ClayNS.exists_velocity_scale_plateau` — the negative half as an explicit
  counterexample: for every `c, E > 0` and all large `M` there is a continuous
  field with `‖u(x₀)‖ = M`, local energy `≤ E` on *every* ball, and **zero**
  oscillation on `B_{c/M}(x₀)`.

So the gap between what is proved and what `A_dyn` asks for is exactly the
factor `M^{1/3}` in the radius, and it is a real gap, not an artifact of the
argument: closing it requires the Navier–Stokes dynamics near the singular
time.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.BlowupOscillation

open MeasureTheory Metric Filter Topology Set

noncomputable section

namespace ClayNS

/-! ## The volume of a ball in `E3` -/

/-- The volume of the unit ball of `E3`. -/
def unitBallVol : ℝ := (volume (ball (0 : E3) 1)).toReal

lemma unitBallVol_pos : 0 < unitBallVol := by
  refine ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne

lemma volume_ball_toReal (x0 : E3) {r : ℝ} (hr : 0 ≤ r) :
    (volume (ball x0 r)).toReal = r ^ 3 * unitBallVol := by
  have hfr : Module.finrank ℝ E3 = 3 := by simp
  rw [Measure.addHaar_ball volume x0 hr, hfr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr 3)]
  rfl

lemma measureReal_ball (x0 : E3) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball x0 r) = r ^ 3 * unitBallVol := by
  rw [measureReal_def]
  exact volume_ball_toReal x0 hr

/-! ## The positive half: energy forbids plateaus that are too wide -/

/-- **Energy-scale reverse concentration.**  A field that reaches size `M` at
`x₀` cannot be nearly constant on a ball whose plateau energy would exceed the
budget. -/
theorem oscOn_ge_of_local_energy {u : E3 → E3} {x0 : E3} {M r E : ℝ}
    (hu : Continuous u) (hM : 0 < M) (hux : M ≤ ‖u x0‖) (hr : 0 < r)
    (hint : IntegrableOn (fun y => ‖u y‖ ^ 2) (ball x0 r) volume)
    (hE : ∫ y in ball x0 r, ‖u y‖ ^ 2 ≤ E)
    (hbig : E < (M / 2) ^ 2 * (r ^ 3 * unitBallVol)) :
    M / 2 ≤ oscOn u (ball x0 r) := by
  by_contra hcon
  push_neg at hcon
  have hbdd : Bornology.IsBounded (u '' ball x0 r) :=
    ((isCompact_closedBall x0 r).image hu).isBounded.subset
      (Set.image_mono ball_subset_closedBall)
  have hx0 : x0 ∈ ball x0 r := mem_ball_self hr
  have hlow : ∀ y ∈ ball x0 r, (M / 2) ^ 2 ≤ ‖u y‖ ^ 2 := by
    intro y hy
    have h1 : ‖u x0 - u y‖ ≤ oscOn u (ball x0 r) := norm_sub_le_oscOn hbdd hx0 hy
    have h2 : ‖u x0‖ - ‖u y‖ ≤ ‖u x0 - u y‖ := norm_sub_norm_le _ _
    have h3 : M / 2 ≤ ‖u y‖ := by linarith
    exact pow_le_pow_left₀ (by positivity) h3 2
  have hkey := setIntegral_ge_of_const_le (μ := volume) (f := fun y => ‖u y‖ ^ 2)
    measurableSet_ball measure_ball_lt_top.ne hlow hint
  rw [smul_eq_mul, measureReal_ball x0 hr.le] at hkey
  nlinarith [hkey, hE, hbig]

/-- **The scale the energy method reaches is `M^{-2/3}`.**  The radius
`A·M^{-2/3}` works with `A` depending only on the energy budget, uniformly in
`M`. -/
theorem energy_scale_defect {u : E3 → E3} {x0 : E3} {M A E : ℝ}
    (hu : Continuous u) (hM : 0 < M) (hux : M ≤ ‖u x0‖) (hA : 0 < A)
    (hint : IntegrableOn (fun y => ‖u y‖ ^ 2) (ball x0 (A / M ^ ((2 : ℝ) / 3))) volume)
    (hE : ∫ y in ball x0 (A / M ^ ((2 : ℝ) / 3)), ‖u y‖ ^ 2 ≤ E)
    (hbudget : E < A ^ 3 * unitBallVol / 4) :
    M / 2 ≤ oscOn u (ball x0 (A / M ^ ((2 : ℝ) / 3))) := by
  have hp : (0 : ℝ) < M ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hM _
  have hcube : (M ^ ((2 : ℝ) / 3)) ^ 3 = M ^ 2 := by
    rw [← Real.rpow_natCast (M ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul hM.le]
    norm_num
  have hr : 0 < A / M ^ ((2 : ℝ) / 3) := div_pos hA hp
  refine oscOn_ge_of_local_energy hu hM hux hr hint hE ?_
  have hden : (A / M ^ ((2 : ℝ) / 3)) ^ 3 = A ^ 3 / M ^ 2 := by
    rw [div_pow, hcube]
  have hval : (M / 2) ^ 2 * ((A / M ^ ((2 : ℝ) / 3)) ^ 3 * unitBallVol)
      = A ^ 3 * unitBallVol / 4 := by
    rw [hden]
    field_simp
    ring
  rw [hval]
  exact hbudget

/-! ## The negative half at the level of the criterion -/

/-- At the velocity scale the plateau budget is `c³·|B₁|/(4M)`. -/
lemma plateau_budget_velocity_scale {c M : ℝ} (hM : 0 < M) :
    (M / 2) ^ 2 * ((c / M) ^ 3 * unitBallVol) = c ^ 3 * unitBallVol / 4 / M := by
  field_simp
  ring

/-- **The energy criterion is vacuous at the velocity scale.**  For every fixed
energy budget `E > 0` the hypothesis of `oscOn_ge_of_local_energy` fails at
`r = c/M` for all large `M`.  No energy bookkeeping can produce `A_dyn`. -/
theorem energy_criterion_vacuous_at_velocity_scale {c E : ℝ} (hE : 0 < E) :
    ∀ᶠ M : ℝ in atTop, (M / 2) ^ 2 * ((c / M) ^ 3 * unitBallVol) < E := by
  have htend : Tendsto (fun M : ℝ => c ^ 3 * unitBallVol / 4 / M) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  filter_upwards [eventually_gt_atTop (0 : ℝ), htend.eventually_lt_const hE] with M hM hlt
  rw [plateau_budget_velocity_scale hM]
  exact hlt

/-! ## The negative half as an explicit plateau -/

/-- A continuous radial plateau of height `M` on `B_ρ(x₀)`, vanishing outside
`B_{2ρ}(x₀)`. -/
def plateauField (M rho : ℝ) (x0 e : E3) : E3 → E3 :=
  fun y => (M * min 1 (max 0 (2 - ‖y - x0‖ / rho))) • e

lemma continuous_plateauField (M rho : ℝ) (x0 e : E3) :
    Continuous (plateauField M rho x0 e) := by
  refine Continuous.smul ?_ continuous_const
  fun_prop

lemma plateauField_of_mem_ball {M rho : ℝ} (hrho : 0 < rho) (x0 e : E3) {y : E3}
    (hy : y ∈ ball x0 rho) : plateauField M rho x0 e y = M • e := by
  have h1 : ‖y - x0‖ < rho := mem_ball_iff_norm.1 hy
  have h2 : ‖y - x0‖ / rho < 1 := (div_lt_one hrho).2 h1
  have h3 : (1 : ℝ) < 2 - ‖y - x0‖ / rho := by linarith
  have h4 : max 0 (2 - ‖y - x0‖ / rho) = 2 - ‖y - x0‖ / rho :=
    max_eq_right (by linarith)
  simp only [plateauField, h4, min_eq_left h3.le, mul_one]

lemma plateauField_zero_of_far {M rho : ℝ} (hrho : 0 < rho) (x0 e : E3) {y : E3}
    (hy : 2 * rho ≤ ‖y - x0‖) : plateauField M rho x0 e y = 0 := by
  have h2 : (2 : ℝ) ≤ ‖y - x0‖ / rho := (le_div_iff₀ hrho).2 (by linarith)
  have h4 : max 0 (2 - ‖y - x0‖ / rho) = 0 := max_eq_left (by linarith)
  simp [plateauField, h4]

lemma norm_plateauField_le {M rho : ℝ} (hM : 0 ≤ M) {e : E3} (he : ‖e‖ = 1)
    (x0 : E3) (y : E3) : ‖plateauField M rho x0 e y‖ ≤ M := by
  have h0 : 0 ≤ max 0 (2 - ‖y - x0‖ / rho) := le_max_left _ _
  have h1 : min 1 (max 0 (2 - ‖y - x0‖ / rho)) ≤ 1 := min_le_left _ _
  have h2 : 0 ≤ min 1 (max 0 (2 - ‖y - x0‖ / rho)) := le_min zero_le_one h0
  rw [plateauField, norm_smul, he, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hM h2)]
  nlinarith

/-- The plateau field is constant, hence has zero oscillation, on `B_ρ(x₀)`. -/
theorem oscOn_plateauField {M rho : ℝ} (hrho : 0 < rho) (x0 e : E3) :
    oscOn (plateauField M rho x0 e) (ball x0 rho) = 0 := by
  have hsub : plateauField M rho x0 e '' ball x0 rho ⊆ {M • e} := by
    rintro p ⟨y, hy, rfl⟩
    exact plateauField_of_mem_ball hrho x0 e hy
  have := Metric.diam_mono hsub (Bornology.isBounded_singleton (x := M • e))
  rw [Metric.diam_singleton] at this
  exact le_antisymm this (oscOn_nonneg _ _)

/-- The local energy of the plateau field on any ball is at most
`M²·(3ρ)³·|B₁|`. -/
theorem plateau_local_energy_le {M rho : ℝ} (hM : 0 ≤ M) (hrho : 0 < rho) {e : E3}
    (he : ‖e‖ = 1) (x0 : E3) (R : ℝ) :
    ∫ y in ball x0 R, ‖plateauField M rho x0 e y‖ ^ 2
      ≤ M ^ 2 * ((3 * rho) ^ 3 * unitBallVol) := by
  have hzero : ∀ y ∈ ball x0 R \ (ball x0 R ∩ ball x0 (3 * rho)),
      ‖plateauField M rho x0 e y‖ ^ 2 = 0 := by
    rintro y ⟨hyR, hys⟩
    have hnot : y ∉ ball x0 (3 * rho) := fun h => hys ⟨hyR, h⟩
    have hfar : 3 * rho ≤ ‖y - x0‖ := le_of_not_gt fun h => hnot (mem_ball_iff_norm.2 h)
    rw [plateauField_zero_of_far hrho x0 e (by linarith)]
    simp
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_ball
    Set.inter_subset_left hzero]
  have hfin : volume (ball x0 R ∩ ball x0 (3 * rho)) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_ball_lt_top
  have hbound : ∀ y ∈ ball x0 R ∩ ball x0 (3 * rho),
      ‖‖plateauField M rho x0 e y‖ ^ 2‖ ≤ M ^ 2 := by
    intro y _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_plateauField_le hM he x0 y) 2
  have h1 : ∫ y in ball x0 R ∩ ball x0 (3 * rho), ‖plateauField M rho x0 e y‖ ^ 2
      ≤ M ^ 2 * volume.real (ball x0 R ∩ ball x0 (3 * rho)) :=
    le_trans (Real.le_norm_self _) (norm_setIntegral_le_of_norm_le_const hfin hbound)
  have h2 : volume.real (ball x0 R ∩ ball x0 (3 * rho))
      ≤ volume.real (ball x0 (3 * rho)) :=
    measureReal_mono Set.inter_subset_right measure_ball_lt_top.ne
  have h3 : volume.real (ball x0 (3 * rho)) = (3 * rho) ^ 3 * unitBallVol :=
    measureReal_ball x0 (by positivity)
  refine le_trans h1 ?_
  rw [← h3]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **A velocity-scale plateau is compatible with any fixed energy budget.**
For every `c, E > 0` and all large `M` there is a continuous field of size `M`
at `x₀`, with local energy at most `E` on every ball, whose oscillation on the
velocity-scale ball `B_{c/M}(x₀)` is exactly `0`.  Hence `A_dyn` does not follow
from the energy budget. -/
theorem exists_velocity_scale_plateau {c E : ℝ} (hc : 0 < c) (hE : 0 < E) (x0 e : E3)
    (he : ‖e‖ = 1) :
    ∀ᶠ M : ℝ in atTop, ∃ u : E3 → E3, Continuous u ∧ ‖u x0‖ = M ∧
      (∀ R : ℝ, ∫ y in ball x0 R, ‖u y‖ ^ 2 ≤ E) ∧
      oscOn u (ball x0 (c / M)) = 0 := by
  have htend : Tendsto (fun M : ℝ => 27 * c ^ 3 * unitBallVol / M) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  filter_upwards [eventually_gt_atTop (0 : ℝ), htend.eventually_le_const hE] with M hM hle
  have hrho : 0 < c / M := div_pos hc hM
  refine ⟨plateauField M (c / M) x0 e, continuous_plateauField _ _ _ _, ?_, ?_,
    oscOn_plateauField hrho x0 e⟩
  · rw [plateauField_of_mem_ball hrho x0 e (mem_ball_self hrho), norm_smul, he, mul_one,
      Real.norm_eq_abs, abs_of_nonneg hM.le]
  · intro R
    refine le_trans (plateau_local_energy_le hM.le hrho he x0 R) (le_trans (le_of_eq ?_) hle)
    field_simp
    ring

end ClayNS
