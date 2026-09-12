/-
# The scale-invariant local gradient energy `Q_∇` and the KNSŠ scale (§5, §6)

The route's most flexible candidate for a constant-excluding defect is the
parabolic-cylinder gradient energy

  `Q_∇(u; x, t, r) = r⁻¹ ∫_{t-r²}^{t} ∫_{B_r(x)} |∇u|² dx ds`,

which is invariant under the Navier–Stokes scaling and vanishes on constants.
This file proves that invariance *exactly*, in the form the route needs
(§5–§6):

* `ClayNS.integral_ball_comp_blowup` — the spatial change of variables
  `∫_{B_R(0)} g(x₀ + M⁻¹y) dy = M³ ∫_{B_{R/M}(x₀)} g(x) dx`;
* `ClayNS.QgradCyl_blowupDensity` — the boxed identity
  `Q_∇(rescaled; 0, 0, 1) = Q_∇(original; x₀, t₀, M⁻¹)`:  the unit-scale
  gradient energy of the rescaled field is the physical gradient energy *at the
  velocity scale* `r = M⁻¹`;
* `ClayNS.gradDensity_blowupSpace` — that the density of the rescaled velocity
  field is indeed the rescaled density, so the previous item applies to
  `|∇u|²`;
* `ClayNS.QgradCyl_of_density_zero` — `Q_∇` vanishes for a field with vanishing
  gradient, i.e. `Q_∇ > 0` does exclude constants;
* `ClayNS.unit_scale_defect_of_velocity_scale_defect` — therefore the
  hypothesis (R1-Q) `Q_∇(u; x_k, t_k, M_k⁻¹) ≥ ε₀` transfers verbatim to the
  rescaled fields at unit scale.  This is exactly the seam identified in §6:
  what remains unproved is the *analytic* statement that a singularity forces
  `Q_∇ ≥ ε₀` at the velocity scale `r = c/M_k`
  (`SingularScaleVelocityScaleMatching`), not any of the scaling bookkeeping.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.BlowupOscillation

open scoped Pointwise
open MeasureTheory Metric Set

noncomputable section

namespace ClayNS

/-! ## Spatial change of variables under the rescaling -/

/-- The dilation-translation change of variables on balls:
`∫_{B_R(0)} g(x₀ + M⁻¹y) dy = M³ ∫_{B_{R/M}(x₀)} g(x) dx`.  (The Jacobian is
`M⁻³` in three dimensions.) -/
theorem integral_ball_comp_blowup {M : ℝ} (hM : 0 < M) (x0 : E3) (R : ℝ) (g : E3 → ℝ) :
    ∫ y in Metric.ball (0:E3) R, g (x0 + M⁻¹ • y)
      = M ^ 3 * ∫ x in Metric.ball x0 (M⁻¹ * R), g x := by
  have himg : (fun y : E3 => x0 + M⁻¹ • y) '' Metric.ball 0 R = Metric.ball x0 (M⁻¹ * R) :=
    image_affine_ball hM x0 R
  have hf' : ∀ y ∈ Metric.ball (0:E3) R,
      HasFDerivWithinAt (fun y : E3 => x0 + M⁻¹ • y) (M⁻¹ • ContinuousLinearMap.id ℝ E3)
        (Metric.ball 0 R) y := by
    intro y _
    have h : HasFDerivAt (fun y : E3 => x0 + M⁻¹ • y) (M⁻¹ • ContinuousLinearMap.id ℝ E3) y := by
      simpa using ((hasFDerivAt_id y).const_smul M⁻¹).const_add x0
    exact h.hasFDerivWithinAt
  have hinj : InjOn (fun y : E3 => x0 + M⁻¹ • y) (Metric.ball 0 R) := by
    intro a _ b _ hab
    have h : M⁻¹ • a = M⁻¹ • b := by
      simpa using congrArg (fun z => z - x0) hab
    exact smul_right_injective E3 (by simp [ne_of_gt hM]) h
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_ball hf' hinj g
  rw [himg] at hcov
  have hdet : ((M⁻¹ • ContinuousLinearMap.id ℝ E3).det) = (M⁻¹) ^ 3 := by
    simp [ContinuousLinearMap.det, LinearMap.det_smul]
  simp only [hdet, abs_of_pos (by positivity : (0:ℝ) < (M⁻¹) ^ 3), smul_eq_mul] at hcov
  rw [hcov, integral_const_mul, ← mul_assoc]
  have : M ^ 3 * (M⁻¹) ^ 3 = 1 := by field_simp
  rw [this, one_mul]

/-! ## The scale-invariant cylinder quantity -/

/-- `Q_∇(G; x₀, t₀, r) = r⁻¹ ∫_{t₀-r²}^{t₀} ∫_{B_r(x₀)} G`, for a spacetime
density `G` (the intended density being `|∇u|²`). -/
def QgradCyl (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3) (r : ℝ) : ℝ :=
  r⁻¹ * ∫ s in (t0 - r ^ 2)..t0, ∫ y in Metric.ball x0 r, G s y

/-- The rescaled density: `|∇u|²` picks up the factor `M⁻⁴` under the KNSŠ
rescaling about `(x₀, t₀)` at velocity scale `M`. -/
def blowupDensity (G : ℝ → E3 → ℝ) (M t0 : ℝ) (x0 : E3) : ℝ → E3 → ℝ :=
  fun s y => (M ^ 4)⁻¹ * G (t0 + (M ^ 2)⁻¹ * s) (x0 + M⁻¹ • y)

/-- **The §5 scale invariance.**  The unit-scale cylinder gradient energy of the
rescaled field equals the physical cylinder gradient energy at the *velocity
scale* `r = M⁻¹`. -/
theorem QgradCyl_blowupDensity (G : ℝ → E3 → ℝ) {M : ℝ} (hM : 0 < M) (t0 : ℝ) (x0 : E3) :
    QgradCyl (blowupDensity G M t0 x0) 0 0 1 = QgradCyl G t0 x0 M⁻¹ := by
  have hMne : M ≠ 0 := ne_of_gt hM
  set F : ℝ → ℝ := fun tau => ∫ x in Metric.ball x0 M⁻¹, G tau x with hF
  have hinner : ∀ s : ℝ,
      (∫ y in Metric.ball (0:E3) 1, blowupDensity G M t0 x0 s y)
        = M⁻¹ * F (t0 + (M ^ 2)⁻¹ * s) := by
    intro s
    have h1 : (∫ y in Metric.ball (0:E3) 1, blowupDensity G M t0 x0 s y)
        = (M ^ 4)⁻¹ * ∫ y in Metric.ball (0:E3) 1, G (t0 + (M ^ 2)⁻¹ * s) (x0 + M⁻¹ • y) := by
      simp only [blowupDensity]
      rw [integral_const_mul]
    rw [h1, integral_ball_comp_blowup hM x0 1 _]
    simp only [mul_one, hF]
    field_simp
  have hLHS : QgradCyl (blowupDensity G M t0 x0) 0 0 1
      = ∫ s in (-1 : ℝ)..0, M⁻¹ * F (t0 + (M ^ 2)⁻¹ * s) := by
    simp only [QgradCyl, inv_one, one_mul, one_pow, zero_sub]
    exact intervalIntegral.integral_congr (fun s _ => hinner s)
  rw [hLHS]
  have h2 : (∫ s in (-1 : ℝ)..0, M⁻¹ * F (t0 + (M ^ 2)⁻¹ * s))
      = M⁻¹ * ∫ s in (-1 : ℝ)..0, (fun z => F (t0 + z)) ((M ^ 2)⁻¹ * s) := by
    rw [intervalIntegral.integral_const_mul]
  rw [h2, intervalIntegral.integral_comp_mul_left (fun z => F (t0 + z))
      (by positivity : ((M : ℝ) ^ 2)⁻¹ ≠ 0),
    intervalIntegral.integral_comp_add_left F t0]
  simp only [QgradCyl, inv_inv, smul_eq_mul, mul_zero, mul_neg, mul_one, add_zero]
  rw [hF]
  have hsq : (M⁻¹ : ℝ) ^ 2 = (M ^ 2)⁻¹ := by field_simp
  rw [hsq]
  ring_nf
  rw [show (M : ℝ) ^ 2 * M⁻¹ = M by field_simp]

/-- The gradient density of the *rescaled velocity field* is the rescaled
density: `|∇u_M|²(y) = M⁻⁴ |∇u|²(x₀ + M⁻¹y)`. -/
theorem gradDensity_blowupSpace (u : ℝ → E3 → E3) {M : ℝ} (hM : 0 < M)
    (hu : ∀ t, Differentiable ℝ (u t)) (t0 : ℝ) (x0 : E3) :
    (fun s y => ‖fderiv ℝ (blowupSpace (u (t0 + (M ^ 2)⁻¹ * s)) M x0) y‖ ^ 2)
      = blowupDensity (fun s y => ‖fderiv ℝ (u s) y‖ ^ 2) M t0 x0 := by
  funext s y
  rw [norm_fderiv_blowupSpace (u (t0 + (M ^ 2)⁻¹ * s)) hM (hu _) x0 y]
  simp only [blowupDensity]
  rw [mul_pow]
  congr 1
  field_simp

/-- `Q_∇` vanishes on a field with vanishing gradient; in particular the
quantity does exclude constants. -/
theorem QgradCyl_of_density_zero (G : ℝ → E3 → ℝ) (hG : ∀ s y, G s y = 0)
    (t0 : ℝ) (x0 : E3) (r : ℝ) : QgradCyl G t0 x0 r = 0 := by
  simp [QgradCyl, hG]

/-- **The transfer of the (R1-Q) hypothesis.**  A physical gradient-energy
defect at the *velocity scale* `M⁻¹` is literally a unit-scale defect for the
rescaled field.  (What is *not* proved — the frontier item `A` — is that a
singularity forces the left-hand side.) -/
theorem unit_scale_defect_of_velocity_scale_defect (G : ℝ → E3 → ℝ) {M eps : ℝ}
    (hM : 0 < M) (t0 : ℝ) (x0 : E3) (h : eps ≤ QgradCyl G t0 x0 M⁻¹) :
    eps ≤ QgradCyl (blowupDensity G M t0 x0) 0 0 1 := by
  rw [QgradCyl_blowupDensity G hM t0 x0]
  exact h

end ClayNS
