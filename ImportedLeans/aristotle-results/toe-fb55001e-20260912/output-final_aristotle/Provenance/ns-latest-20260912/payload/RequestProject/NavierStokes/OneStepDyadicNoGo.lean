/-
# The one-dyadic-step question is not kinematic

`DyadicCascade.lean` reduces `A_cascade` to a one-dyadic-step inequality
`Q_∇(r/2) ≥ Ψ(Q_∇(r))`, iterated `cascadeSteps M ≍ (1/3)log₂ M` times, and
`FrequencyDoubling.lean` / `FrequencyAlmostMonotone.lean` say exactly which
shapes of `Ψ` survive the iteration.  This file settles the prior question:
*can such a step inequality hold for purely measure-theoretic reasons?*

It cannot, and the failure is total.  For every radius `r > 0` there is a
nonnegative, continuous, time-independent density supported in the annulus
`{13r/16 ≤ |y| ≤ 15r/16}` whose scale-invariant cylinder energy at radius `r` is
any prescribed `ε > 0`, and **exactly zero** at radius `r/2`.  So no function
`Ψ` with `Ψ(ε) > 0` can satisfy the one-step inequality for all nonnegative
densities: the defect can sit entirely in the discarded annulus.

Together with `GradientEnergyScaling.lean` (`Q_∇ ≤ A|B₁|r⁴`, so the zero-loss
monotonicity gate is false for *regular* fields) this pins down what
`A_cascade` must consume.  A one-step persistence lemma has to use the
Navier–Stokes evolution — a local energy/Caccioppoli inequality with its
dissipation term, or a monotonicity formula — and cannot come from the
geometry of the shrinking cylinders.  This is the `A`-side analogue of the
sparse-island no-go on the `C` side.

## What is proved here

* `ClayNS.annulusBump`, `ClayNS.annulusDensity` — the witness.
* `ClayNS.annulusBump_eq_zero_of_norm_lt_half` — it vanishes on `B_{r/2}`.
* `ClayNS.annulusBump_integral_pos` — but it has positive mass on `B_r`.
* `ClayNS.QgradCyl_const_mul` — `Q_∇` is linear in the density, so the mass can
  be normalised to any prescribed level.
* `ClayNS.qgradCyl_annulusDensity_half_eq_zero`,
  `ClayNS.qgradCyl_annulusDensity_eq` — the two values.
* `ClayNS.exists_density_with_prescribed_defect_and_vanishing_half` — the
  witness with `Q_∇(r) = ε` and `Q_∇(r/2) = 0`.
* `ClayNS.no_kinematic_one_step_persistence` — the conclusion: any `Ψ` valid for
  all nonnegative continuous densities is nonpositive on `(0,∞)`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GradientEnergyScaling

open MeasureTheory Metric Set

noncomputable section

namespace ClayNS

/-! ## The annular witness -/

/-- The centre of the annular bump: distance `7r/8` from the origin. -/
def bumpCenter (r : ℝ) : E3 := (7 * r / 8) • ee 0

lemma norm_ee_zero : ‖ee (0 : Fin 3)‖ = 1 := by
  simp [ee]

lemma norm_bumpCenter {r : ℝ} (hr : 0 ≤ r) : ‖bumpCenter r‖ = 7 * r / 8 := by
  rw [bumpCenter, norm_smul, norm_ee_zero, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 7 * r / 8)]

/-- A continuous nonnegative bump of radius `r/16` centred at distance `7r/8`
from the origin: supported in the annulus `13r/16 ≤ |y| ≤ 15r/16`. -/
def annulusBump (r : ℝ) : E3 → ℝ := fun y => max 0 (r / 16 - dist y (bumpCenter r))

/-- The associated time-independent spacetime density. -/
def annulusDensity (r : ℝ) : ℝ → E3 → ℝ := fun _ y => annulusBump r y

lemma annulusBump_nonneg (r : ℝ) (y : E3) : 0 ≤ annulusBump r y := le_max_left _ _

lemma continuous_annulusBump (r : ℝ) : Continuous (annulusBump r) :=
  continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))

lemma integrableOn_annulusBump (r : ℝ) (x : E3) (rho : ℝ) :
    IntegrableOn (annulusBump r) (ball x rho) volume :=
  (((continuous_annulusBump r).continuousOn).integrableOn_compact
    (isCompact_closedBall x rho)).mono_set ball_subset_closedBall

/-- The bump vanishes on the half-radius ball. -/
lemma annulusBump_eq_zero_of_norm_lt_half {r : ℝ} (hr : 0 < r) {y : E3}
    (hy : ‖y‖ < r / 2) : annulusBump r y = 0 := by
  have hc : ‖bumpCenter r‖ = 7 * r / 8 := norm_bumpCenter hr.le
  have htri : dist (bumpCenter r) (0 : E3) ≤ dist (bumpCenter r) y + dist y 0 :=
    dist_triangle _ _ _
  have h1 : dist (bumpCenter r) (0 : E3) = 7 * r / 8 := by
    rw [dist_zero_right, hc]
  have h2 : dist y (0 : E3) = ‖y‖ := dist_zero_right y
  have h3 : 7 * r / 8 - ‖y‖ ≤ dist y (bumpCenter r) := by
    rw [dist_comm]
    rw [h1, h2] at htri
    linarith
  have h4 : r / 16 - dist y (bumpCenter r) ≤ 0 := by
    have : r / 16 < 7 * r / 8 - ‖y‖ := by linarith
    linarith
  simpa [annulusBump] using max_eq_left h4

/-- The bump carries strictly positive mass on the full ball. -/
lemma annulusBump_integral_pos {r : ℝ} (hr : 0 < r) :
    0 < ∫ y in ball (0 : E3) r, annulusBump r y := by
  set c := bumpCenter r with hcdef
  have hc : ‖c‖ = 7 * r / 8 := norm_bumpCenter hr.le
  -- the small ball on which the bump is bounded below
  have hsub : ball c (r / 32) ⊆ ball (0 : E3) r := by
    intro y hy
    have hdy : dist y c < r / 32 := mem_ball.mp hy
    have : ‖y‖ ≤ ‖c‖ + dist y c := by
      have := dist_triangle y c (0 : E3)
      rw [dist_zero_right, dist_zero_right] at this
      linarith [this]
    have hlt : ‖y‖ < r := by
      rw [hc] at this
      linarith
    exact mem_ball.mpr (by rwa [dist_zero_right])
  have hlow : ∀ y ∈ ball c (r / 32), r / 32 ≤ annulusBump r y := by
    intro y hy
    have hdy : dist y c < r / 32 := mem_ball.mp hy
    have : r / 32 ≤ r / 16 - dist y c := by linarith
    exact this.trans (le_max_right _ _)
  have hconstint : IntegrableOn (fun _ : E3 => r / 32) (ball c (r / 32)) volume :=
    integrableOn_const (μ := volume) (s := ball c (r / 32)) (C := r / 32)
      measure_ball_lt_top.ne
  have hsmall : (r / 32) * ((r / 32) ^ 3 * unitBallVol)
      ≤ ∫ y in ball c (r / 32), annulusBump r y := by
    have hmono := setIntegral_mono_on hconstint
      (integrableOn_annulusBump r c (r / 32)) measurableSet_ball hlow
    rw [setIntegral_const, smul_eq_mul, measureReal_ball c (by positivity : (0:ℝ) ≤ r / 32)] at hmono
    linarith [hmono]
  have hbig : (∫ y in ball c (r / 32), annulusBump r y)
      ≤ ∫ y in ball (0 : E3) r, annulusBump r y := by
    refine setIntegral_mono_set (integrableOn_annulusBump r 0 r) ?_
      (HasSubset.Subset.eventuallyLE hsub)
    filter_upwards with y using annulusBump_nonneg r y
  have hpos : (0:ℝ) < (r / 32) * ((r / 32) ^ 3 * unitBallVol) := by
    have := unitBallVol_pos
    positivity
  linarith

/-! ## The two cylinder values -/

/-- `Q_∇` is linear in the density. -/
lemma QgradCyl_const_mul (c : ℝ) (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3) (r : ℝ) :
    QgradCyl (fun s y => c * G s y) t0 x0 r = c * QgradCyl G t0 x0 r := by
  have hinner : ∀ s : ℝ, (∫ y in ball x0 r, c * G s y) = c * ∫ y in ball x0 r, G s y :=
    fun s => integral_const_mul c _
  simp only [QgradCyl]
  rw [show (∫ s in (t0 - r ^ 2)..t0, ∫ y in ball x0 r, c * G s y)
      = ∫ s in (t0 - r ^ 2)..t0, c * ∫ y in ball x0 r, G s y from by
        simp_rw [hinner],
    intervalIntegral.integral_const_mul]
  ring

/-- At the half radius the annular density contributes nothing. -/
theorem qgradCyl_annulusDensity_half_eq_zero (t0 : ℝ) {r : ℝ} (hr : 0 < r) :
    QgradCyl (annulusDensity r) t0 0 (r / 2) = 0 := by
  have hinner : ∀ s : ℝ, (∫ y in ball (0 : E3) (r / 2), annulusDensity r s y) = 0 := by
    intro s
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    have : ‖y‖ < r / 2 := by
      have := mem_ball.mp hy
      rwa [dist_zero_right] at this
    exact annulusBump_eq_zero_of_norm_lt_half hr this
  simp only [QgradCyl]
  simp_rw [hinner]
  simp

/-- At the full radius the annular density has cylinder energy `r·∫B_r`. -/
theorem qgradCyl_annulusDensity_eq (t0 : ℝ) {r : ℝ} (hr : 0 < r) :
    QgradCyl (annulusDensity r) t0 0 r = r * ∫ y in ball (0 : E3) r, annulusBump r y := by
  simp only [QgradCyl, annulusDensity]
  rw [intervalIntegral.integral_const, smul_eq_mul,
    show t0 - (t0 - r ^ 2) = r ^ 2 by ring]
  field_simp

/-! ## The no-go -/

/-- **A defect at radius `r` of any prescribed size, and none at `r/2`.** -/
theorem exists_density_with_prescribed_defect_and_vanishing_half (t0 : ℝ) {r eps : ℝ}
    (hr : 0 < r) (heps : 0 < eps) :
    ∃ G : ℝ → E3 → ℝ, (∀ s y, 0 ≤ G s y) ∧ (∀ s, Continuous (G s)) ∧
      QgradCyl G t0 0 r = eps ∧ QgradCyl G t0 0 (r / 2) = 0 := by
  set I : ℝ := ∫ y in ball (0 : E3) r, annulusBump r y with hI
  have hIpos : 0 < I := annulusBump_integral_pos hr
  set c : ℝ := eps / (r * I) with hc
  have hcpos : 0 < c := by
    rw [hc]; positivity
  refine ⟨fun s y => c * annulusDensity r s y, fun s y =>
    mul_nonneg hcpos.le (annulusBump_nonneg r y),
    fun s => continuous_const.mul (continuous_annulusBump r), ?_, ?_⟩
  · rw [QgradCyl_const_mul, qgradCyl_annulusDensity_eq t0 hr, ← hI, hc]
    field_simp
  · rw [QgradCyl_const_mul, qgradCyl_annulusDensity_half_eq_zero t0 hr, mul_zero]

/-- **No kinematic one-dyadic-step persistence.**  If `Ψ` were a valid one-step
gain function for *all* nonnegative continuous densities, it would be
nonpositive at every positive level: the defect can hide entirely in the annulus
discarded by halving the radius.  Hence any genuine one-step lemma must consume
the Navier–Stokes evolution. -/
theorem no_kinematic_one_step_persistence (t0 : ℝ) {r : ℝ} (hr : 0 < r) (Psi : ℝ → ℝ)
    (hPsi : ∀ G : ℝ → E3 → ℝ, (∀ s y, 0 ≤ G s y) → (∀ s, Continuous (G s)) →
      ∀ eps, 0 < eps → eps ≤ QgradCyl G t0 0 r → Psi eps ≤ QgradCyl G t0 0 (r / 2)) :
    ∀ eps, 0 < eps → Psi eps ≤ 0 := by
  intro eps heps
  obtain ⟨G, hGnn, hGc, hfull, hhalf⟩ :=
    exists_density_with_prescribed_defect_and_vanishing_half t0 hr heps
  have := hPsi G hGnn hGc eps heps (le_of_eq hfull.symm)
  rwa [hhalf] at this

end ClayNS
