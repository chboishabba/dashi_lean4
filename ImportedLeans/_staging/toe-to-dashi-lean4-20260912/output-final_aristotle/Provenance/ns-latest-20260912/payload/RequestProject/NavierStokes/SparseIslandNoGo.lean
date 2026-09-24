/-
# The sparse-island obstruction to `C_sparse`

`LinearSkeletonPropagation.lean` shows that the viscous skeleton of the
increment equation gives *no* polynomial anti-concentration.  This file makes
the verdict two-sided and draws the structural consequence.

* `ClayNS.heatGauss_ball_integral_ge` — the propagator does satisfy a *Gaussian*
  anti-concentration bound `∫_{B_R} S ≥ A·e^{−bR²}·R³·|B_1|`, and by
  `ClayNS.heatGauss_ball_integral_le` this shape is essentially attained.  So
  the propagation law of the linear skeleton is exactly Gaussian in the
  separation: not polynomial loss, not worse than Gaussian either.
* `ClayNS.gaussian_lower_bound_has_vanishing_density` — a Gaussian lower bound
  carries *no* mean density at all: `R^{-3}·(cR³e^{−bR²}) → 0`.  Hence it can
  never contradict a dilution budget of the form `mean density → 0`, whatever
  the constants.
* `ClayNS.linear_skeleton_hosts_sparse_defect_island` — the packaged no-go: a
  single strictly positive exact solution of the skeleton simultaneously has a
  positive central defect and vanishing mean density on every polynomial scale.
  Both clauses of the `C_sparse` contradiction can therefore hold at once for
  the diffusive part, so `C_sparse` is *false* for the linear skeleton and must
  be proved, if at all, from the nonlinear Kármán–Howarth structure.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.OpenGates

open scoped BigOperators
open MeasureTheory Filter Topology Metric

noncomputable section

namespace ClayNS

/-! ## The Gaussian anti-concentration bound is attained -/

/-- **Gaussian lower bound for the ball mass of the propagator.**  On `B_R` the
kernel is at least its value at separation `R`, so the ball mass is at least
`A·e^{−bR²}·R³·|B_1|` with `A = S(t,0)` and `b = 1/(4κt)`. -/
theorem heatGauss_ball_integral_ge (kap : ℝ) (hkap : 0 < kap) {t : ℝ} (ht : 0 < t) {R : ℝ}
    (hR : 0 ≤ R) :
    heatGauss kap (t, 0) * Real.exp (-(((4 * kap)⁻¹ * t⁻¹) * R ^ 2))
        * (R ^ 3 * (volume (ball (0 : E3) 1)).toReal)
      ≤ ∫ h in ball (0 : E3) R, heatGauss kap (t, h) := by
  set A : ℝ := heatGauss kap (t, 0) with hA
  set b : ℝ := (4 * kap)⁻¹ * t⁻¹ with hb
  have hbpos : 0 < b := by rw [hb]; positivity
  have hAnn : 0 ≤ A := heatGauss_nonneg kap _
  have hvol : (volume (ball (0 : E3) R)).toReal = R ^ 3 * (volume (ball (0 : E3) 1)).toReal :=
    volume_ball_real R hR
  have hfin : volume (ball (0 : E3) R) ≠ ⊤ := measure_ball_lt_top.ne
  -- the pointwise lower bound on the ball
  have hpt : ∀ h ∈ ball (0 : E3) R, A * Real.exp (-(b * R ^ 2)) ≤ heatGauss kap (t, h) := by
    intro h hh
    have hnorm : ‖h‖ ≤ R := by
      have := mem_ball_zero_iff.mp hh
      exact this.le
    rw [heatGauss_slice_eq kap t h, ← hb]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hAnn
    have hsq : ‖h‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg h]
    nlinarith
  have hint : IntegrableOn (fun h : E3 => heatGauss kap (t, h)) (ball (0 : E3) R) :=
    integrableOn_heatGauss_ball kap t R
  have hconst : IntegrableOn (fun _ : E3 => A * Real.exp (-(b * R ^ 2))) (ball (0 : E3) R) :=
    integrableOn_const hfin
  have hmono : (∫ _h in ball (0 : E3) R, A * Real.exp (-(b * R ^ 2)))
      ≤ ∫ h in ball (0 : E3) R, heatGauss kap (t, h) :=
    setIntegral_mono_on hconst hint measurableSet_ball hpt
  have hcalc : (∫ _h in ball (0 : E3) R, A * Real.exp (-(b * R ^ 2)))
      = A * Real.exp (-(b * R ^ 2)) * (R ^ 3 * (volume (ball (0 : E3) 1)).toReal) := by
    rw [setIntegral_const, measureReal_def, hvol, smul_eq_mul, mul_comm]
  rw [hcalc] at hmono
  exact hmono

/-- **A Gaussian lower bound has vanishing mean density.**  Whatever the
constants, `R^{-3}(c·R³·e^{−bR²}) → 0`: a Gaussian anti-concentration statement
cannot contradict a vanishing-density budget. -/
theorem gaussian_lower_bound_has_vanishing_density (c b : ℝ) (hb : 0 < b) :
    Tendsto (fun R : ℝ => (c * R ^ 3 * Real.exp (-(b * R ^ 2))) / R ^ 3) atTop (𝓝 0) := by
  have hlim : Tendsto (fun R : ℝ => c * Real.exp (-(b * R ^ 2))) atTop (𝓝 (c * 0)) := by
    refine Tendsto.const_mul c ?_
    have h0 : Tendsto (fun R : ℝ => R ^ (0 : ℝ) * Real.exp (-b * R ^ (2 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_mul_exp_neg_rpow 0 b 2 hb two_pos
    refine Tendsto.congr' ?_ h0
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [Real.rpow_zero, one_mul, Real.rpow_two]
    ring_nf
  rw [mul_zero] at hlim
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have h3 : (R : ℝ) ^ 3 ≠ 0 := by positivity
  field_simp

/-! ## The packaged sparse-island no-go -/

/-- **The linear skeleton hosts a sparse defect island.**  The propagator is a
strictly positive exact solution of `∂_t S = κΔ_h S` which has a positive
central defect at every time and, at the same time, vanishing mean density on
every polynomial scale.  So the two clauses that `C_sparse` wants to play off
against each other — "a positive local defect" and "globally diluted density" —
are simultaneously satisfiable within the diffusive part of the increment
equation.  Any proof of `C_sparse` must therefore use the nonlinear
Kármán–Howarth flux; no amount of parabolic regularity for the viscous part can
supply it. -/
theorem linear_skeleton_hosts_sparse_defect_island (kap : ℝ) (hkap : 0 < kap) :
    ∃ S : STime → ℝ,
      (∀ z : STime, 0 < S z)
        ∧ (∀ z : STime, 0 < z.1 → dtime S z = kap * lap S z)
        ∧ (∀ d : ℝ, 0 < d →
            Tendsto (fun R : ℝ => (∫ h in ball (0 : E3) R, S (1, h)) / R ^ d) atTop (𝓝 0)) := by
  refine ⟨heatGauss kap, heatGauss_pos kap, fun z hz => heatGauss_heat_equation kap hkap.ne' hz,
    fun d hd => heatGauss_ball_subpolynomial kap hkap one_pos hd⟩

/-! ## The no-go extends to the whole bounded-drift class -/

/-- The class of objects that the ancient/increment route actually has to work
with: a nonnegative structure defect obeying the Kármán–Howarth-type inequality
`∂_t S + ∇_h·(bS) ≤ 2νΔ_h S` with the drift bound `|b| ≤ 2` supplied by
`‖U‖_∞ ≤ 1`. -/
structure BoundedDriftDefect (nu : ℝ) (S : STime → ℝ) (b : Fin 3 → STime → ℝ) : Prop where
  nonneg : ∀ z : STime, 0 ≤ S z
  driftBound : ∀ (z : STime) (j : Fin 3), |b j z| ≤ 2
  subsolution : ∀ z : STime, 0 < z.1 →
    dtime S z + ∑ j, dvec (0, ee j) (fun w => b j w * S w) z ≤ 2 * nu * lap S z

/-- **The propagator is a member of the class.**  With zero drift the heat
kernel of diffusivity `2ν` satisfies the increment inequality with equality. -/
theorem boundedDriftDefect_heatGauss (nu : ℝ) (hnu : 0 < nu) :
    BoundedDriftDefect nu (heatGauss (2 * nu)) (fun _ _ => 0) where
  nonneg := heatGauss_nonneg (2 * nu)
  driftBound := by intro z j; norm_num
  subsolution := by
    intro z hz
    have hkap : (2 * nu) ≠ 0 := by positivity
    have hzero : ∀ j : Fin 3,
        dvec (0, ee j) (fun w : STime => (0 : ℝ) * heatGauss (2 * nu) w) z = 0 := by
      intro j
      simp [dvec]
    have heq := heatGauss_heat_equation (2 * nu) hkap hz
    simp only [hzero, Finset.sum_const_zero, add_zero]
    exact le_of_eq heq

/-- **The sparse-island no-go for the full bounded-drift class.**  There is a
member of the class which is strictly positive everywhere — so it has a positive
local defect at the centre — and whose ball mass grows slower than every power
of the radius.  Consequently no anti-concentration statement of the form
`∫_{B_R} S ≥ c·R^d` can be deduced from nonnegativity, the drift bound and the
differential inequality alone: `C_sparse` genuinely requires the extra ancestry
of the ancient limit, not just the structure of the inequality. -/
theorem boundedDriftClass_admits_sparse_defect_island (nu : ℝ) (hnu : 0 < nu) :
    ∃ (S : STime → ℝ) (b : Fin 3 → STime → ℝ),
      BoundedDriftDefect nu S b ∧ (∀ z : STime, 0 < S z)
        ∧ ∀ (c d : ℝ), 0 < c → 0 < d → ¬ PolynomialSparsePropagation S 1 c d := by
  refine ⟨heatGauss (2 * nu), fun _ _ => 0, boundedDriftDefect_heatGauss nu hnu,
    heatGauss_pos (2 * nu), ?_⟩
  intro c d hc hd
  exact polynomialSparsePropagation_fails_for_linear_skeleton (2 * nu) (by positivity)
    one_pos hc hd

end ClayNS
