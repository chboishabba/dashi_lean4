/-
# The linear skeleton of the increment equation: how far does positivity travel?

The ancient/increment route needs a *sparse defect propagation* statement of the
shape

  `S(h₀,0) ≥ ε  ⟹  ∫_{B_R} S ≥ c·Ψ(R)`  with `Ψ` growing (ideally `Ψ(R) ≍ R³`),

for the nonnegative structure defect `S` obeying

  `∂_t S + ∇_h·(bS) ≤ 2ν Δ_h S`,  `|b| ≤ 2`.

Before attacking the nonlinear problem it is worth asking what the *linear*
skeleton — drop the drift `b`, keep the viscous part — already does.  This file
answers that question with an exact witness rather than a heuristic.

`ClayNS.heatGauss κ (t,h) = t^{-3/2} exp(−|h|²/(4κt))` is a genuine, strictly
positive solution of `∂_t S = κ Δ_h S` for `t > 0`
(`ClayNS.heatGauss_heat_equation`, `ClayNS.heatGauss_pos`), and it is the
propagator: it is what a point defect turns into.  Two consequences are proved
here.

* `ClayNS.heatGauss_ratio` and `ClayNS.heatGauss_superpolynomial_decay` — the
  loss in separation is Gaussian: the value at separation `h` is the value at
  `0` times `exp(−|h|²/(4κt))`, which decays faster than every inverse power of
  the distance.  So positivity does *not* propagate outward with polynomial
  loss in the linear skeleton.
* `ClayNS.heatGauss_ball_average_tendsto_zero` — the mean density on `B_R`
  tends to `0`: `R^{-3}∫_{B_R} S → 0`.  Hence no lower bound of the hoped-for
  form `∫_{B_R} S ≥ c·R³` can be derived from the linear part alone
  (`ClayNS.no_cubic_growth_for_linear_skeleton`).

Verdict: the polynomial-loss hope must come *entirely* from the nonlinear
structure of the Kármán–Howarth flux; the viscous skeleton is against it.  This
is exactly the falsifiable test asked for, and it comes out negative.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ExactSolution
import RequestProject.NavierStokes.Vorticity

open scoped BigOperators
open MeasureTheory Filter Topology Metric

noncomputable section

namespace ClayNS

/-! ## Coordinates and the Gaussian -/

/-- The `j`-th space coordinate as a continuous linear functional on spacetime. -/
def xc (j : Fin 3) : STime →L[ℝ] ℝ :=
  (EuclideanSpace.proj j).comp (ContinuousLinearMap.snd ℝ ℝ E3)

@[simp] lemma xc_apply (j : Fin 3) (z : STime) : xc j z = z.2 j := rfl

/-- The squared Euclidean length `|h|² = ∑ h_j²`. -/
def sq3 (h : E3) : ℝ := ∑ j, h j * h j

@[simp] lemma sq3_zero : sq3 (0 : E3) = 0 := by simp [sq3]

lemma sq3_nonneg (h : E3) : 0 ≤ sq3 h :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

lemma sq3_eq_norm_sq (h : E3) : sq3 h = ‖h‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  simp [sq3, sq, abs_mul_abs_self]

/-- The exponent of the heat kernel, `−(3/2)log t − |h|²/(4κt)`. -/
def gaussArg (kap : ℝ) : STime → ℝ :=
  fun z => -((3 : ℝ) / 2) * Real.log z.1 - (4 * kap)⁻¹ * (sq3 z.2 * (z.1)⁻¹)

/-- The heat kernel `t^{-3/2}·exp(−|h|²/(4κt))` for the diffusion `∂_t = κΔ`. -/
def heatGauss (kap : ℝ) : STime → ℝ := fun z => Real.exp (gaussArg kap z)

lemma heatGauss_pos (kap : ℝ) (z : STime) : 0 < heatGauss kap z := Real.exp_pos _

lemma heatGauss_nonneg (kap : ℝ) (z : STime) : 0 ≤ heatGauss kap z := (heatGauss_pos kap z).le

/-- The Gaussian factorization: at a fixed time the value at separation `h` is
the value at `h = 0` multiplied by `exp(−|h|²/(4κt))`. -/
theorem heatGauss_ratio (kap : ℝ) (t : ℝ) (h : E3) :
    heatGauss kap (t, h) = heatGauss kap (t, 0) * Real.exp (-((4 * kap)⁻¹ * (sq3 h * t⁻¹))) := by
  simp only [heatGauss, gaussArg, sq3_zero]
  rw [← Real.exp_add]
  ring_nf

/-! ## The Gaussian is an exact solution of the linear skeleton -/

lemma hasFDerivAt_logTime {z : STime} (hz : z.1 ≠ 0) :
    HasFDerivAt (fun w : STime => Real.log w.1) ((z.1)⁻¹ • tc) z :=
  (Real.hasDerivAt_log hz).comp_hasFDerivAt z tc.hasFDerivAt

lemma hasFDerivAt_invTime {z : STime} (hz : z.1 ≠ 0) :
    HasFDerivAt (fun w : STime => (w.1)⁻¹) ((-((z.1) ^ 2)⁻¹) • tc) z :=
  (hasDerivAt_inv hz).comp_hasFDerivAt z tc.hasFDerivAt

lemma hasFDerivAt_sq3 (z : STime) :
    HasFDerivAt (fun w : STime => sq3 w.2) (∑ j, (2 * z.2 j) • xc j) z := by
  have h : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      HasFDerivAt (fun w : STime => w.2 j * w.2 j) ((2 * z.2 j) • xc j) z := by
    intro j _
    have hj : HasFDerivAt (fun w : STime => w.2 j) (xc j) z := (xc j).hasFDerivAt
    have := hj.mul hj
    simpa [two_mul, add_smul] using this
  exact HasFDerivAt.sum h

/-- The Fréchet derivative of the Gaussian exponent. -/
def gaussArgD (kap : ℝ) (z : STime) : STime →L[ℝ] ℝ :=
  (-((3 : ℝ) / 2)) • ((z.1)⁻¹ • tc)
    - (4 * kap)⁻¹ • (sq3 z.2 • ((-((z.1) ^ 2)⁻¹) • tc) + (z.1)⁻¹ • (∑ j, (2 * z.2 j) • xc j))

lemma hasFDerivAt_gaussArg (kap : ℝ) {z : STime} (hz : z.1 ≠ 0) :
    HasFDerivAt (gaussArg kap) (gaussArgD kap z) z := by
  have h1 : HasFDerivAt (fun w : STime => -((3 : ℝ) / 2) * Real.log w.1)
      ((-((3 : ℝ) / 2)) • ((z.1)⁻¹ • tc)) z := (hasFDerivAt_logTime hz).const_mul _
  have h2 : HasFDerivAt (fun w : STime => sq3 w.2 * (w.1)⁻¹)
      (sq3 z.2 • ((-((z.1) ^ 2)⁻¹) • tc) + (z.1)⁻¹ • (∑ j, (2 * z.2 j) • xc j)) z :=
    (hasFDerivAt_sq3 z).mul (hasFDerivAt_invTime hz)
  exact h1.sub (h2.const_mul _)

lemma hasFDerivAt_heatGauss (kap : ℝ) {z : STime} (hz : z.1 ≠ 0) :
    HasFDerivAt (heatGauss kap) (heatGauss kap z • gaussArgD kap z) z :=
  (Real.hasDerivAt_exp _).comp_hasFDerivAt z (hasFDerivAt_gaussArg kap hz)

lemma differentiableAt_heatGauss (kap : ℝ) {z : STime} (hz : z.1 ≠ 0) :
    DifferentiableAt ℝ (heatGauss kap) z := (hasFDerivAt_heatGauss kap hz).differentiableAt

lemma gaussArgD_space (kap : ℝ) {z : STime} (hkap : kap ≠ 0) (hz : z.1 ≠ 0) (i : Fin 3) :
    gaussArgD kap z (0, ee i) = -((2 * kap * z.1)⁻¹ * z.2 i) := by
  have hsum : (∑ j, ((2 * z.2 j) • xc j)) ((0 : ℝ), ee i) = 2 * z.2 i := by
    simp [ee, EuclideanSpace.single_apply, Finset.sum_ite_eq' Finset.univ i]
  simp only [gaussArgD, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hsum, tc_apply]
  field_simp
  ring

lemma gaussArgD_time (kap : ℝ) (z : STime) :
    gaussArgD kap z ((1 : ℝ), (0 : E3))
      = -((3 : ℝ) / 2) * (z.1)⁻¹ + (4 * kap)⁻¹ * (sq3 z.2 * ((z.1) ^ 2)⁻¹) := by
  have hsum : (∑ j, ((2 * z.2 j) • xc j)) ((1 : ℝ), (0 : E3)) = 0 := by simp
  simp only [gaussArgD, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hsum, tc_apply]
  ring

/-- The space derivative of the Gaussian: `∂_i S = −S·h_i/(2κt)`. -/
lemma dspace_heatGauss (kap : ℝ) {z : STime} (hkap : kap ≠ 0) (hz : z.1 ≠ 0) (i : Fin 3) :
    dspace (heatGauss kap) i z = heatGauss kap z * (-((2 * kap * z.1)⁻¹ * z.2 i)) := by
  rw [dspace, (hasFDerivAt_heatGauss kap hz).fderiv]
  rw [ContinuousLinearMap.smul_apply, gaussArgD_space kap hkap hz i, smul_eq_mul]

/-- The time derivative of the Gaussian: `∂_t S = S(−3/(2t) + |h|²/(4κt²))`. -/
lemma dtime_heatGauss (kap : ℝ) {z : STime} (hz : z.1 ≠ 0) :
    dtime (heatGauss kap) z
      = heatGauss kap z * (-((3 : ℝ) / 2) * (z.1)⁻¹ + (4 * kap)⁻¹ * (sq3 z.2 * ((z.1) ^ 2)⁻¹)) := by
  rw [dtime, (hasFDerivAt_heatGauss kap hz).fderiv]
  rw [ContinuousLinearMap.smul_apply, gaussArgD_time kap z, smul_eq_mul]

/-- The open half space `t > 0`, on which the kernel formulas hold. -/
lemma eventually_pos_time {z : STime} (hz : 0 < z.1) : ∀ᶠ w : STime in 𝓝 z, 0 < w.1 := by
  have hopen : IsOpen {w : STime | 0 < w.1} := isOpen_lt continuous_const continuous_fst
  exact hopen.mem_nhds hz

/-- The scalar factor of the first space derivative, `−h_i/(2κt)`. -/
def gaussSpaceFactor (kap : ℝ) (i : Fin 3) : STime → ℝ :=
  fun w => -((2 * kap * w.1)⁻¹ * w.2 i)

lemma hasFDerivAt_gaussSpaceFactor (kap : ℝ) {z : STime} (hkap : kap ≠ 0) (hz : z.1 ≠ 0)
    (i : Fin 3) :
    HasFDerivAt (gaussSpaceFactor kap i)
      (-((2 * kap * z.1)⁻¹ • xc i
        + z.2 i • ((-((2 * kap * z.1) ^ 2)⁻¹) • ((2 * kap) • tc)))) z := by
  have hlin : HasFDerivAt (fun w : STime => 2 * kap * w.1) ((2 * kap) • tc) z := by
    simpa using tc.hasFDerivAt.const_mul (2 * kap)
  have hne : 2 * kap * z.1 ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hkap) hz
  have hinv : HasFDerivAt (fun w : STime => (2 * kap * w.1)⁻¹)
      ((-((2 * kap * z.1) ^ 2)⁻¹) • ((2 * kap) • tc)) z :=
    (hasDerivAt_inv hne).comp_hasFDerivAt z hlin
  have hxi : HasFDerivAt (fun w : STime => w.2 i) (xc i) z := (xc i).hasFDerivAt
  exact (hinv.mul hxi).neg

lemma dvec_gaussSpaceFactor (kap : ℝ) {z : STime} (hkap : kap ≠ 0) (hz : z.1 ≠ 0) (i : Fin 3) :
    dvec (0, ee i) (gaussSpaceFactor kap i) z = -((2 * kap * z.1)⁻¹) := by
  rw [dvec, (hasFDerivAt_gaussSpaceFactor kap hkap hz i).fderiv]
  have hxci : (xc i) ((0 : ℝ), ee i) = 1 := by simp [ee, EuclideanSpace.single_apply]
  simp [hxci]

/-- The second space derivative of the Gaussian:
`∂_i∂_i S = S(h_i²/(4κ²t²) − 1/(2κt))`. -/
lemma dspace_dspace_heatGauss (kap : ℝ) {z : STime} (hkap : kap ≠ 0) (hz : 0 < z.1) (i : Fin 3) :
    dspace (fun w => dspace (heatGauss kap) i w) i z
      = heatGauss kap z * ((2 * kap * z.1)⁻¹ * z.2 i * ((2 * kap * z.1)⁻¹ * z.2 i)
          - (2 * kap * z.1)⁻¹) := by
  have hz' : z.1 ≠ 0 := ne_of_gt hz
  have hEq : (fun w => dspace (heatGauss kap) i w)
      =ᶠ[𝓝 z] fun w => heatGauss kap w * gaussSpaceFactor kap i w := by
    filter_upwards [eventually_pos_time hz] with w hw
    exact dspace_heatGauss kap hkap (ne_of_gt hw) i
  rw [dspace_eq_dvec, dvec, hEq.fderiv_eq, ← dvec]
  rw [dvec_mul (heatGauss kap) (gaussSpaceFactor kap i) z (differentiableAt_heatGauss kap hz')
      (hasFDerivAt_gaussSpaceFactor kap hkap hz' i).differentiableAt (0, ee i),
    ← dspace_eq_dvec, dspace_heatGauss kap hkap hz' i, dvec_gaussSpaceFactor kap hkap hz' i]
  simp only [gaussSpaceFactor]
  ring

/-- **The heat kernel solves the linear skeleton** `∂_t S = κ Δ_h S` on `t > 0`. -/
theorem heatGauss_heat_equation (kap : ℝ) (hkap : kap ≠ 0) {z : STime} (hz : 0 < z.1) :
    dtime (heatGauss kap) z = kap * lap (heatGauss kap) z := by
  have hz' : z.1 ≠ 0 := ne_of_gt hz
  have hlap : lap (heatGauss kap) z
      = ∑ i, heatGauss kap z * ((2 * kap * z.1)⁻¹ * z.2 i * ((2 * kap * z.1)⁻¹ * z.2 i)
          - (2 * kap * z.1)⁻¹) :=
    Finset.sum_congr rfl fun i _ => dspace_dspace_heatGauss kap hkap hz i
  rw [dtime_heatGauss kap hz', hlap, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hsum1 : (∑ i, (2 * kap * z.1)⁻¹ * z.2 i * ((2 * kap * z.1)⁻¹ * z.2 i))
      = ((2 * kap * z.1)⁻¹) ^ 2 * sq3 z.2 := by
    rw [sq3, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsum2 : (∑ _i : Fin 3, (2 * kap * z.1)⁻¹) = 3 * (2 * kap * z.1)⁻¹ := by
    simp [mul_comm]
  rw [hsum1, hsum2]
  field_simp
  ring

/-! ## No polynomial-loss propagation: Gaussian decay in the separation -/

/-- The value of the kernel at separation `r·e` decays faster than every inverse
power of `r`: propagation of positivity in the linear skeleton costs
`exp(−|h|²/4κt)`, not a polynomial. -/
theorem heatGauss_superpolynomial_decay (kap : ℝ) (hkap : 0 < kap) {t : ℝ} (ht : 0 < t)
    (n : ℕ) (e : E3) (he : ‖e‖ = 1) :
    Tendsto (fun r : ℝ => r ^ n * heatGauss kap (t, r • e)) atTop (𝓝 0) := by
  set b : ℝ := (4 * kap)⁻¹ * t⁻¹ with hbdef
  have hb : 0 < b := by rw [hbdef]; positivity
  have hval : ∀ r : ℝ, r ^ n * heatGauss kap (t, r • e)
      = heatGauss kap (t, 0) * (r ^ n * Real.exp (-(b * r ^ 2))) := by
    intro r
    have hsq : sq3 (r • e) = r ^ 2 := by
      rw [sq3_eq_norm_sq, norm_smul, he, Real.norm_eq_abs]
      simp [sq_abs]
    rw [heatGauss_ratio kap t (r • e), hsq, hbdef]
    ring_nf
  simp only [hval]
  have hkey : Tendsto (fun r : ℝ => r ^ n * Real.exp (-(b * r ^ 2))) atTop (𝓝 0) := by
    have hg : Tendsto (fun r : ℝ => r ^ (n : ℝ) * Real.exp (-b * r)) atTop (𝓝 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) b hb
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
      have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr
      have hpow : r ^ n = r ^ (n : ℝ) := (Real.rpow_natCast r n).symm
      have hexp : Real.exp (-(b * r ^ 2)) ≤ Real.exp (-b * r) := by
        refine Real.exp_le_exp.mpr ?_
        have hrr : r ≤ r ^ 2 := by nlinarith
        have := mul_le_mul_of_nonneg_left hrr hb.le
        linarith
      rw [hpow]
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
  simpa using hkey.const_mul (heatGauss kap (t, 0))

/-! ## No cubic growth: the mean density of the kernel vanishes -/

lemma continuous_sq3 : Continuous sq3 :=
  continuous_finset_sum _ fun j _ =>
    ((EuclideanSpace.proj j).continuous).mul ((EuclideanSpace.proj j).continuous)

lemma continuous_heatGauss_slice (kap t : ℝ) : Continuous fun h : E3 => heatGauss kap (t, h) := by
  refine Real.continuous_exp.comp ?_
  simp only [gaussArg]
  exact continuous_const.sub (continuous_const.mul (continuous_sq3.mul continuous_const))

/-- The kernel at a fixed positive time, in Gaussian form with the rate
`b = 1/(4κt)`. -/
lemma heatGauss_slice_eq (kap t : ℝ) (h : E3) :
    heatGauss kap (t, h)
      = heatGauss kap (t, 0) * Real.exp (-(((4 * kap)⁻¹ * t⁻¹) * ‖h‖ ^ 2)) := by
  rw [heatGauss_ratio kap t h, sq3_eq_norm_sq]
  congr 2
  ring

lemma heatGauss_slice_le_center (kap : ℝ) (hkap : 0 < kap) {t : ℝ} (ht : 0 < t) (h : E3) :
    heatGauss kap (t, h) ≤ heatGauss kap (t, 0) := by
  rw [heatGauss_slice_eq kap t h]
  have hb : 0 ≤ ((4 * kap)⁻¹ * t⁻¹) * ‖h‖ ^ 2 := by positivity
  calc heatGauss kap (t, 0) * Real.exp (-(((4 * kap)⁻¹ * t⁻¹) * ‖h‖ ^ 2))
      ≤ heatGauss kap (t, 0) * 1 :=
        mul_le_mul_of_nonneg_left (by simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr hb))
          (heatGauss_nonneg kap _)
    _ = heatGauss kap (t, 0) := mul_one _

lemma heatGauss_slice_le_far (kap : ℝ) (hkap : 0 < kap) {t : ℝ} (ht : 0 < t) {R0 : ℝ}
    (hR0 : 0 ≤ R0) {h : E3} (hh : R0 ≤ ‖h‖) :
    heatGauss kap (t, h)
      ≤ heatGauss kap (t, 0) * Real.exp (-(((4 * kap)⁻¹ * t⁻¹) * R0 ^ 2)) := by
  rw [heatGauss_slice_eq kap t h]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (heatGauss_nonneg kap _)
  have hb : 0 < (4 * kap)⁻¹ * t⁻¹ := by positivity
  have : R0 ^ 2 ≤ ‖h‖ ^ 2 := by nlinarith [norm_nonneg h]
  nlinarith

/-- The (real) volume of a ball of `E3` scales cubically. -/
lemma volume_ball_real (R : ℝ) (hR : 0 ≤ R) :
    (volume (ball (0 : E3) R)).toReal = R ^ 3 * (volume (ball (0 : E3) 1)).toReal := by
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  rw [Measure.addHaar_ball (volume : Measure E3) (0 : E3) hR, hdim,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

lemma integrableOn_heatGauss_ball (kap t R : ℝ) :
    IntegrableOn (fun h : E3 => heatGauss kap (t, h)) (ball (0 : E3) R) :=
  ((continuous_heatGauss_slice kap t).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : E3) R)).mono_set ball_subset_closedBall

/-- **The kernel integral over `B_R` grows strictly slower than `R³`.** -/
theorem heatGauss_ball_integral_le (kap : ℝ) (hkap : 0 < kap) {t : ℝ} (ht : 0 < t) {R R0 : ℝ}
    (h0 : 0 ≤ R0) (hR : R0 ≤ R) :
    (∫ h in ball (0 : E3) R, heatGauss kap (t, h))
      ≤ heatGauss kap (t, 0) * (R0 ^ 3 * (volume (ball (0 : E3) 1)).toReal)
        + heatGauss kap (t, 0) * Real.exp (-(((4 * kap)⁻¹ * t⁻¹) * R0 ^ 2))
            * (R ^ 3 * (volume (ball (0 : E3) 1)).toReal) := by
  have hR0R : ball (0 : E3) R0 ⊆ ball (0 : E3) R := ball_subset_ball hR
  have hunion : ball (0 : E3) R0 ∪ (ball (0 : E3) R \ ball (0 : E3) R0) = ball (0 : E3) R :=
    Set.union_diff_cancel hR0R
  have hint : IntegrableOn (fun h : E3 => heatGauss kap (t, h)) (ball (0 : E3) R) :=
    integrableOn_heatGauss_ball kap t R
  have hint1 : IntegrableOn (fun h : E3 => heatGauss kap (t, h)) (ball (0 : E3) R0) :=
    hint.mono_set hR0R
  have hint2 : IntegrableOn (fun h : E3 => heatGauss kap (t, h))
      (ball (0 : E3) R \ ball (0 : E3) R0) := hint.mono_set Set.diff_subset
  have hsplit : (∫ h in ball (0 : E3) R, heatGauss kap (t, h))
      = (∫ h in ball (0 : E3) R0, heatGauss kap (t, h))
        + ∫ h in ball (0 : E3) R \ ball (0 : E3) R0, heatGauss kap (t, h) := by
    rw [← setIntegral_union Set.disjoint_sdiff_right
      (measurableSet_ball.diff measurableSet_ball) hint1 hint2, hunion]
  have hfin1 : (volume (ball (0 : E3) R0)) < ⊤ := measure_ball_lt_top
  have hfin2 : (volume (ball (0 : E3) R)) < ⊤ := measure_ball_lt_top
  -- the inner ball: bound by the central value
  have hb1 : (∫ h in ball (0 : E3) R0, heatGauss kap (t, h))
      ≤ heatGauss kap (t, 0) * (R0 ^ 3 * (volume (ball (0 : E3) 1)).toReal) := by
    have hmono := setIntegral_mono_on hint1
      (integrableOn_const hfin1.ne) measurableSet_ball
      (fun x _ => heatGauss_slice_le_center kap hkap ht x)
    rw [setIntegral_const, smul_eq_mul, Measure.real, volume_ball_real R0 h0] at hmono
    calc (∫ h in ball (0 : E3) R0, heatGauss kap (t, h))
        ≤ R0 ^ 3 * (volume (ball (0 : E3) 1)).toReal * heatGauss kap (t, 0) := hmono
      _ = heatGauss kap (t, 0) * (R0 ^ 3 * (volume (ball (0 : E3) 1)).toReal) := by ring
  -- the outer annulus: the Gaussian factor is already small there
  have hb2 : (∫ h in ball (0 : E3) R \ ball (0 : E3) R0, heatGauss kap (t, h))
      ≤ heatGauss kap (t, 0) * Real.exp (-(((4 * kap)⁻¹ * t⁻¹) * R0 ^ 2))
          * (R ^ 3 * (volume (ball (0 : E3) 1)).toReal) := by
    have hRnn : 0 ≤ R := le_trans h0 hR
    have hmeas : MeasurableSet (ball (0 : E3) R \ ball (0 : E3) R0) :=
      measurableSet_ball.diff measurableSet_ball
    have hfin3 : volume (ball (0 : E3) R \ ball (0 : E3) R0) < ⊤ :=
      lt_of_le_of_lt (measure_mono Set.diff_subset) hfin2
    have hmono := setIntegral_mono_on hint2
      (integrableOn_const hfin3.ne) hmeas
      (fun x hx => heatGauss_slice_le_far kap hkap ht h0
        (by
          have hx2 : ¬ ‖x‖ < R0 := by simpa [mem_ball_zero_iff] using hx.2
          exact not_lt.mp hx2))
    rw [setIntegral_const, smul_eq_mul, Measure.real] at hmono
    have hle : (volume (ball (0 : E3) R \ ball (0 : E3) R0)).toReal
        ≤ R ^ 3 * (volume (ball (0 : E3) 1)).toReal := by
      rw [← volume_ball_real R hRnn]
      exact ENNReal.toReal_mono (ne_of_lt hfin2) (measure_mono Set.diff_subset)
    refine hmono.trans ?_
    have hpos : 0 ≤ heatGauss kap (t, 0) * Real.exp (-(((4 * kap)⁻¹ * t⁻¹) * R0 ^ 2)) :=
      mul_nonneg (heatGauss_nonneg kap _) (Real.exp_nonneg _)
    calc (volume (ball (0 : E3) R \ ball (0 : E3) R0)).toReal
          * (heatGauss kap (t, 0) * Real.exp (-(((4 * kap)⁻¹ * t⁻¹) * R0 ^ 2)))
        ≤ (R ^ 3 * (volume (ball (0 : E3) 1)).toReal)
          * (heatGauss kap (t, 0) * Real.exp (-(((4 * kap)⁻¹ * t⁻¹) * R0 ^ 2))) :=
          mul_le_mul_of_nonneg_right hle hpos
      _ = heatGauss kap (t, 0) * Real.exp (-(((4 * kap)⁻¹ * t⁻¹) * R0 ^ 2))
            * (R ^ 3 * (volume (ball (0 : E3) 1)).toReal) := by ring
  rw [hsplit]
  linarith

/-- **The mean density of the linear propagator vanishes**: `R^{-3}∫_{B_R} S → 0`.
The heat semigroup spreads a defect, it does not create bulk. -/
theorem heatGauss_ball_average_tendsto_zero (kap : ℝ) (hkap : 0 < kap) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun R : ℝ => (∫ h in ball (0 : E3) R, heatGauss kap (t, h)) / R ^ 3)
      atTop (𝓝 0) := by
  set A : ℝ := heatGauss kap (t, 0) with hA
  set v : ℝ := (volume (ball (0 : E3) 1)).toReal with hv
  set b : ℝ := (4 * kap)⁻¹ * t⁻¹ with hbdef
  have hb : 0 < b := by rw [hbdef]; positivity
  have hvnn : 0 ≤ v := ENNReal.toReal_nonneg
  have hAnn : 0 ≤ A := heatGauss_nonneg kap _
  have hmaj : Tendsto (fun R : ℝ => A * v / R + A * Real.exp (-(b * R)) * v) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => A * v / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun R : ℝ => A * Real.exp (-(b * R)) * v) atTop (𝓝 0) := by
      have hlin : Tendsto (fun R : ℝ => b * R) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hb tendsto_id
      have hneg : Tendsto (fun R : ℝ => -(b * R)) atTop atBot := tendsto_neg_atBot_iff.mpr hlin
      have hexp : Tendsto (fun R : ℝ => Real.exp (-(b * R))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hneg
      simpa using (hexp.const_mul A).mul_const v
    simpa using h1.add h2
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hnn : 0 ≤ ∫ h in ball (0 : E3) R, heatGauss kap (t, h) :=
      setIntegral_nonneg measurableSet_ball fun x _ => heatGauss_nonneg kap _
    exact div_nonneg hnn (by positivity)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
    have hsq : Real.sqrt R ≤ R := by
      nlinarith [Real.sq_sqrt hR0.le, Real.sqrt_nonneg R, Real.one_le_sqrt.mpr hR]
    have hsqnn : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
    have hsq2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR0.le
    have hbound := heatGauss_ball_integral_le kap hkap ht hsqnn hsq
    rw [hsq2] at hbound
    have hcube : Real.sqrt R ^ 3 ≤ R ^ 2 := by
      have : Real.sqrt R ^ 3 = R * Real.sqrt R := by
        rw [pow_succ, hsq2]
      rw [this]
      nlinarith
    have hstep : (∫ h in ball (0 : E3) R, heatGauss kap (t, h))
        ≤ A * (R ^ 2 * v) + A * Real.exp (-(b * R)) * (R ^ 3 * v) := by
      refine hbound.trans ?_
      have : A * (Real.sqrt R ^ 3 * v) ≤ A * (R ^ 2 * v) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcube hvnn) hAnn
      linarith
    rw [div_le_iff₀ (pow_pos hR0 3)]
    have hexpand : (A * v / R + A * Real.exp (-(b * R)) * v) * R ^ 3
        = A * (R ^ 2 * v) + A * Real.exp (-(b * R)) * (R ^ 3 * v) := by
      field_simp
    rw [hexpand]
    exact hstep

/-- **The hoped-for cubic lower bound fails for the linear skeleton.**  There is
no constant `c > 0` with `∫_{B_R} S ≥ c·R³` for the propagator `S`, at any
positive time — even though `S` is everywhere strictly positive. -/
theorem no_cubic_growth_for_linear_skeleton (kap : ℝ) (hkap : 0 < kap) {t : ℝ} (ht : 0 < t)
    {c : ℝ} (hc : 0 < c) :
    ¬ ∀ R : ℝ, 1 ≤ R → c * R ^ 3 ≤ ∫ h in ball (0 : E3) R, heatGauss kap (t, h) := by
  intro hall
  have hlim := heatGauss_ball_average_tendsto_zero kap hkap ht
  have hev : ∀ᶠ R : ℝ in atTop,
      (∫ h in ball (0 : E3) R, heatGauss kap (t, h)) / R ^ 3 < c :=
    hlim.eventually (gt_mem_nhds hc)
  obtain ⟨R, hRge, hRlt⟩ := ((eventually_ge_atTop (1 : ℝ)).and hev).exists
  have hR0 : (0 : ℝ) < R ^ 3 := by positivity
  have := hall R hRge
  rw [div_lt_iff₀ hR0] at hRlt
  linarith

/-! ## The stronger verdict: sub-polynomial growth of the ball mass -/

/-- `R^m·exp(−b·R^p) → 0` for every `m` and every positive `b, p`. -/
lemma tendsto_rpow_mul_exp_neg_rpow (m b p : ℝ) (hb : 0 < b) (hp : 0 < p) :
    Tendsto (fun R : ℝ => R ^ m * Real.exp (-b * R ^ p)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun y : ℝ => y ^ (m / p) * Real.exp (-b * y)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m / p) b hb
  have hRp : Tendsto (fun R : ℝ => R ^ p) atTop atTop := tendsto_rpow_atTop hp
  refine Tendsto.congr' ?_ (hbase.comp hRp)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have : ((R : ℝ) ^ p) ^ (m / p) = R ^ m := by
    rw [← Real.rpow_mul hR.le]
    congr 1
    field_simp
  simp only [Function.comp_apply, this]

/-- **The ball mass of the linear propagator grows slower than every power.**
For every exponent `d > 0`, `R^{-d}∫_{B_R} S → 0`.  So no anti-concentration
statement of the form `∫_{B_R} S ≥ c·R^d` — polynomial in any degree — can be
extracted from the viscous skeleton. -/
theorem heatGauss_ball_subpolynomial (kap : ℝ) (hkap : 0 < kap) {t : ℝ} (ht : 0 < t)
    {d : ℝ} (hd : 0 < d) :
    Tendsto (fun R : ℝ => (∫ h in ball (0 : E3) R, heatGauss kap (t, h)) / R ^ d)
      atTop (𝓝 0) := by
  set A : ℝ := heatGauss kap (t, 0) with hA
  set v : ℝ := (volume (ball (0 : E3) 1)).toReal with hv
  set b : ℝ := (4 * kap)⁻¹ * t⁻¹ with hbdef
  set al : ℝ := min (d / 6) (1 / 2) with haldef
  have hb : 0 < b := by rw [hbdef]; positivity
  have hvnn : 0 ≤ v := ENNReal.toReal_nonneg
  have hAnn : 0 ≤ A := heatGauss_nonneg kap _
  have hal : 0 < al := lt_min (by positivity) (by norm_num)
  have hal2 : al ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have hald : 3 * al - d < 0 := by
    have : al ≤ d / 6 := min_le_left _ _
    linarith
  -- the majorant
  have hmaj : Tendsto
      (fun R : ℝ => A * v * R ^ (3 * al - d) + A * v * (R ^ (3 - d) * Real.exp (-b * R ^ (2 * al))))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => A * v * R ^ (3 * al - d)) atTop (𝓝 0) := by
      have hneg : Tendsto (fun R : ℝ => R ^ (-(d - 3 * al))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by linarith)
      have : Tendsto (fun R : ℝ => R ^ (3 * al - d)) atTop (𝓝 0) := by
        simpa [neg_sub] using hneg
      simpa using this.const_mul (A * v)
    have h2 : Tendsto
        (fun R : ℝ => A * v * (R ^ (3 - d) * Real.exp (-b * R ^ (2 * al)))) atTop (𝓝 0) := by
      have := tendsto_rpow_mul_exp_neg_rpow (3 - d) b (2 * al) hb (by linarith)
      simpa using this.const_mul (A * v)
    simpa using h1.add h2
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hnn : 0 ≤ ∫ h in ball (0 : E3) R, heatGauss kap (t, h) :=
      setIntegral_nonneg measurableSet_ball fun x _ => heatGauss_nonneg kap _
    exact div_nonneg hnn (Real.rpow_nonneg hR.le d)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
    set R0 : ℝ := R ^ al with hR0def
    have hR0nn : 0 ≤ R0 := Real.rpow_nonneg hR0.le al
    have hR0le : R0 ≤ R := by
      calc R0 = R ^ al := rfl
        _ ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR hal2
        _ = R := Real.rpow_one R
    have hcube : R0 ^ 3 = R ^ (3 * al) := by
      rw [hR0def, ← Real.rpow_natCast (R ^ al) 3, ← Real.rpow_mul hR0.le]
      norm_num [mul_comm]
    have hsquare : R0 ^ 2 = R ^ (2 * al) := by
      rw [hR0def, ← Real.rpow_natCast (R ^ al) 2, ← Real.rpow_mul hR0.le]
      norm_num [mul_comm]
    have hbound := heatGauss_ball_integral_le kap hkap ht hR0nn hR0le
    rw [hcube, hsquare] at hbound
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hR0 d)]
    have hRcube : (R : ℝ) ^ (3 : ℕ) = R ^ (3 : ℝ) := by
      rw [← Real.rpow_natCast R 3]
      norm_num
    have hexpand :
        (A * v * R ^ (3 * al - d) + A * v * (R ^ (3 - d) * Real.exp (-b * R ^ (2 * al)))) * R ^ d
          = A * (R ^ (3 * al) * v)
            + A * Real.exp (-(b * R ^ (2 * al))) * (R ^ (3 : ℕ) * v) := by
      have e1 : R ^ (3 * al - d) * R ^ d = R ^ (3 * al) := by
        rw [← Real.rpow_add hR0]
        congr 1
        ring
      have e2 : R ^ ((3 : ℝ) - d) * R ^ d = R ^ (3 : ℝ) := by
        rw [← Real.rpow_add hR0]
        congr 1
        ring
      calc (A * v * R ^ (3 * al - d)
              + A * v * (R ^ (3 - d) * Real.exp (-b * R ^ (2 * al)))) * R ^ d
          = A * v * (R ^ (3 * al - d) * R ^ d)
            + A * v * ((R ^ ((3 : ℝ) - d) * R ^ d) * Real.exp (-b * R ^ (2 * al))) := by ring
        _ = A * v * R ^ (3 * al)
            + A * v * (R ^ (3 : ℝ) * Real.exp (-b * R ^ (2 * al))) := by rw [e1, e2]
        _ = A * (R ^ (3 * al) * v)
            + A * Real.exp (-(b * R ^ (2 * al))) * (R ^ (3 : ℕ) * v) := by
              rw [hRcube]; ring_nf
    rw [hexpand]
    exact hbound

/-- **No polynomial anti-concentration for the linear skeleton**, in any degree. -/
theorem no_polynomial_growth_for_linear_skeleton (kap : ℝ) (hkap : 0 < kap) {t : ℝ} (ht : 0 < t)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ¬ ∀ R : ℝ, 1 ≤ R → c * R ^ d ≤ ∫ h in ball (0 : E3) R, heatGauss kap (t, h) := by
  intro hall
  have hlim := heatGauss_ball_subpolynomial kap hkap ht hd
  have hev : ∀ᶠ R : ℝ in atTop,
      (∫ h in ball (0 : E3) R, heatGauss kap (t, h)) / R ^ d < c :=
    hlim.eventually (gt_mem_nhds hc)
  obtain ⟨R, hRge, hRlt⟩ := ((eventually_ge_atTop (1 : ℝ)).and hev).exists
  have hR0 : (0 : ℝ) < R ^ d := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hRge) d
  have := hall R hRge
  rw [div_lt_iff₀ hR0] at hRlt
  linarith

end ClayNS
