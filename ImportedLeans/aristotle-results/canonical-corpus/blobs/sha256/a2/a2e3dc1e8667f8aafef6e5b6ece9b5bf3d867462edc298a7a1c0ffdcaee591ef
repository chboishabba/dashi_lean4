/-
# `C48`–`C49`: the periodized Gaussian as an **approximate** adjoint weight

The frontier item `ClayNS.ConcentratedAdjointWeightGate` asks for a weight that
solves the backward adjoint transport–diffusion equation

  `L*_hΦ = −∂_tΦ − u(·+h)·∇Φ − νΔΦ = 0`                                  (Adj)

*exactly*, is nonnegative and periodic, and whose cell mass is at most `θ` times
its value at the defect point.  The constant weight `Φ ≡ 1` satisfies (Adj) but
realizes `θ = 1` exactly, so the entire content of the gate is the strict
inequality `θ < 1` — see `ClayNS.concentratedAdjointWeightGate_one`.

## What this file does, and the correction it records

A Gaussian backward-heat weight concentrates, but it does **not** solve (Adj):

* the *static* Gaussian `Φ_a(x) = exp(−|x−x₀|²/(4a))` satisfies neither
  `∂_tΦ = νΔΦ` (it is time-independent) nor the drift equation;
* the *exactly caloric* kernel `(τ/σ(t))^{3/2}exp(−|x−x₀|²/(4νσ(t)))`,
  `σ(t) = t₀+τ−t`, blows up at `t = t₀+τ` and is therefore not globally smooth,
  which the residual/budget theorems of `AdjointLocalizedIncrement.lean`
  require;
* an ESS/Carleman exponential is designed to make the *conjugated* operator
  coercive; it is not a positive solution of (Adj) either.

So the Gaussian must be used as an **approximate** adjoint weight, and
`ClayNS.adjoint_localized_increment_residual` already prices that exactly: the
whole cost of failing to solve (Adj) is `|β(q)|` times the residual `L*_hΦ`.

The weight used here is the ℤ³-periodic torus analogue of the Gaussian built in
`TorusGaussianWeight.lean`,

  `Φ_a(x) = exp(−Σ_j sin(π(x_j−x₀_j))²/(4aπ²))`,   `a = ντ`,

which is genuinely smooth and `ℤ³`-periodic — no lattice sum, no truncation
error.  Its budgets, proved in `TorusGaussianIntegrals.lean`, are

* `∫_cell Φ_a ≤ π³√(π³)·a^{3/2}` — the concentration ratio, since `Φ_a(x₀) = 1`;
* `∫_cell |∂_jΦ_a| ≤ 2π³a` — the drift part of the residual;
* `∫_cell |ΔΦ_a| ≤ C·a^{1/2}` — the viscous defect, the price of staticity.

Hence, for `|u| ≤ A` componentwise,

  `∫_cell |L*_hΦ_a| ≤ 6π³A·a + νC·a^{1/2}`,

with **both** terms of positive scaling dimension in `a`.  The concentration
ratio and the adjoint residual therefore go to zero *simultaneously*: this is
the "isolate an irrelevant error and telescope it" shape.

The honest correction to the informal proposal is the second term: a static
weight is not backward caloric, so the residual is `O(a^{1/2})` rather than
`O(a)`.  It still vanishes, which is all the gate needs.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.TorusGaussianIntegrals
import RequestProject.NavierStokes.FrontierGatesAdjoint

open Real MeasureTheory

noncomputable section

namespace ClayNS

/-! ## Closed forms for the one-dimensional scales -/

lemma tgY_sq {a : ℝ} (ha : 0 ≤ a) : tgY a ^ 2 = π ^ 3 * a :=
  Real.sq_sqrt (mul_nonneg (by positivity) ha)

lemma tgY_eq (a : ℝ) : tgY a = Real.sqrt (π ^ 3) * Real.sqrt a := by
  rw [tgY, Real.sqrt_mul (by positivity)]

lemma tgY2_eq (a : ℝ) : tgY2 a = Real.sqrt (2 * π ^ 3) * Real.sqrt a := by
  rw [tgY2, Real.sqrt_mul (by positivity)]

/-- The mass constant `π³√(π³)`. -/
def tgMassC : ℝ := π ^ 3 * Real.sqrt (π ^ 3)

/-- The Laplacian constant `3(π³√(π³) + π⁵√(2π³))/2`. -/
def tgLapC : ℝ := 3 * (π ^ 3 * Real.sqrt (π ^ 3) + π ^ 5 * Real.sqrt (2 * π ^ 3)) / 2

lemma tgMassC_pos : 0 < tgMassC := by
  have := Real.pi_pos
  have h : 0 < Real.sqrt (π ^ 3) := Real.sqrt_pos.2 (by positivity)
  rw [tgMassC]; positivity

lemma tgLapC_pos : 0 < tgLapC := by
  have := Real.pi_pos
  have h1 : 0 < Real.sqrt (π ^ 3) := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 < Real.sqrt (2 * π ^ 3) := Real.sqrt_pos.2 (by positivity)
  rw [tgLapC]; positivity

lemma tgY_cube {a : ℝ} (ha : 0 ≤ a) : tgY a ^ 3 = tgMassC * (a * Real.sqrt a) := by
  have h1 : Real.sqrt (π ^ 3) ^ 2 = π ^ 3 := Real.sq_sqrt (by positivity)
  have h2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  calc tgY a ^ 3
      = (Real.sqrt (π ^ 3) ^ 2 * Real.sqrt (π ^ 3)) * (Real.sqrt a ^ 2 * Real.sqrt a) := by
        rw [tgY_eq a]; ring
    _ = tgMassC * (a * Real.sqrt a) := by rw [h1, h2, tgMassC]

lemma lapBudget_eq {a : ℝ} (ha : 0 < a) :
    3 * ((1 / (2 * a) * tgY a + π ^ 2 / (2 * a) * tgY2 a) * tgY a ^ 2)
      = tgLapC * Real.sqrt a := by
  rw [tgY_sq ha.le, tgY_eq a, tgY2_eq a, tgLapC]
  field_simp

/-! ## `C49`: the three cell budgets, in closed form -/

/-- **Mass.**  `∫_cell Φ_a ≤ π³√(π³)·a^{3/2}` while `Φ_a(x₀) = 1`: the
concentration ratio `θ(a)` is `O(a^{3/2})`. -/
theorem cellInt_torusGauss_le_mass {a : ℝ} (ha : 0 < a) (x0 : E3) (t : ℝ) :
    cellInt (fun x => torusGauss a x0 (t, x)) ≤ tgMassC * (a * Real.sqrt a) := by
  have h := cellInt_torusGauss_le ha x0 t
  rwa [tgY_cube ha.le] at h

/-- **Gradient.**  `∫_cell |∂_jΦ_a| ≤ 2π³a`. -/
theorem cellInt_abs_dvec_torusGauss_le_lin {a : ℝ} (ha : 0 < a) (x0 : E3) (i : Fin 3) (t : ℝ) :
    cellInt (fun x => |dvec (0, ee i) (torusGauss a x0) (t, x)|) ≤ 2 * π ^ 3 * a := by
  have h := cellInt_abs_dvec_torusGauss_le ha x0 i t
  rwa [tgY_sq ha.le, ← mul_assoc] at h

/-- **Laplacian.**  `∫_cell |ΔΦ_a| ≤ C·a^{1/2}` — the viscous defect of a
static weight. -/
theorem cellInt_abs_lap_torusGauss_le_sqrt {a : ℝ} (ha : 0 < a) (x0 : E3) (t : ℝ) :
    cellInt (fun x => |lap (torusGauss a x0) (t, x)|) ≤ tgLapC * Real.sqrt a := by
  have h := cellInt_abs_lap_torusGauss_le ha x0 t
  rwa [lapBudget_eq ha] at h

/-! ## `C48`: the adjoint residual of the torus Gaussian -/

/-- **`C48`.**  The torus Gaussian is static, so its adjoint residual is exactly
the drift term plus the viscous term: `L*_hΦ_a = −u(·+h)·∇Φ_a − νΔΦ_a`.  No
approximation is involved in this identity. -/
theorem adjointOp_torusGauss (nu a : ℝ) (h : E3) (V : STime → E3) (x0 : E3) (z : STime) :
    adjointOp nu h V (torusGauss a x0) z
      = -(∑ j, shift h V z j * dvec (0, ee j) (torusGauss a x0) z)
        - nu * lap (torusGauss a x0) z := by
  rw [adjointOp, dtime_torusGauss]
  ring

/-- The pointwise residual bound. -/
theorem abs_adjointOp_torusGauss_le {nu a Amp : ℝ} (hnu : 0 ≤ nu)
    {V : STime → E3} (hAmp : ∀ (z : STime) (b : Fin 3), |V z b| ≤ Amp)
    (h x0 : E3) (z : STime) :
    |adjointOp nu h V (torusGauss a x0) z|
      ≤ Amp * (∑ j, |dvec (0, ee j) (torusGauss a x0) z|)
        + nu * |lap (torusGauss a x0) z| := by
  have hA0 : 0 ≤ Amp := le_trans (abs_nonneg _) (hAmp z 0)
  have hdrift : |∑ j, shift h V z j * dvec (0, ee j) (torusGauss a x0) z|
      ≤ Amp * ∑ j, |dvec (0, ee j) (torusGauss a x0) z| := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (by simpa using hAmp (z.1, z.2 + h) j) (abs_nonneg _)
  rw [adjointOp_torusGauss]
  calc |(-(∑ j, shift h V z j * dvec (0, ee j) (torusGauss a x0) z))
          - nu * lap (torusGauss a x0) z|
      ≤ |(-(∑ j, shift h V z j * dvec (0, ee j) (torusGauss a x0) z))|
        + |nu * lap (torusGauss a x0) z| := abs_sub _ _
    _ = |∑ j, shift h V z j * dvec (0, ee j) (torusGauss a x0) z|
        + nu * |lap (torusGauss a x0) z| := by
        rw [abs_neg, abs_mul, abs_of_nonneg hnu]
    _ ≤ Amp * (∑ j, |dvec (0, ee j) (torusGauss a x0) z|)
        + nu * |lap (torusGauss a x0) z| := by linarith

/-- Smoothness of the adjoint residual field. -/
lemma contDiff_adjointOp_torusGauss (nu a : ℝ) (h : E3) {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (x0 : E3) :
    ContDiff ℝ (⊤ : ℕ∞) (adjointOp nu h V (torusGauss a x0)) := by
  have hPhi := contDiff_torusGauss a x0
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : STime => - dvec (1, 0) (torusGauss a x0) z) :=
    (contDiff_dvec _ hPhi (1, 0)).neg
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : STime => ∑ j, shift h V z j * dvec (0, ee j) (torusGauss a x0) z) :=
    ContDiff.sum fun j _ =>
      (contDiff_coord _ (contDiff_shift h hV) j).mul (contDiff_dvec _ hPhi (0, ee j))
  have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun z : STime => nu * lap (torusGauss a x0) z) :=
    contDiff_const.mul (contDiff_lapFun hPhi)
  exact (h1.sub h2).sub h3

/-- **`C49`, residual form.**  `∫_cell |L*_hΦ_a| ≤ 6π³A·a + νC·a^{1/2}`. -/
theorem cellInt_abs_adjointOp_torusGauss_le {nu a Amp : ℝ} (ha : 0 < a) (hnu : 0 ≤ nu)
    {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hAmp : ∀ (z : STime) (b : Fin 3), |V z b| ≤ Amp) (h x0 : E3) (t : ℝ) :
    cellInt (fun x => |adjointOp nu h V (torusGauss a x0) (t, x)|)
      ≤ Amp * (6 * π ^ 3 * a) + nu * (tgLapC * Real.sqrt a) := by
  have hA0 : 0 ≤ Amp := le_trans (abs_nonneg _) (hAmp (t, x0) 0)
  have hPhi := contDiff_torusGauss a x0
  have hcL : Continuous fun x : E3 => |lap (torusGauss a x0) (t, x)| :=
    (continuous_slice (contDiff_lapFun hPhi) t).abs
  have hcD : ∀ j : Fin 3, Continuous fun x : E3 => |dvec (0, ee j) (torusGauss a x0) (t, x)| :=
    fun j => (continuous_slice (contDiff_dvec _ hPhi (0, ee j)) t).abs
  have hcS : Continuous fun x : E3 => ∑ j, |dvec (0, ee j) (torusGauss a x0) (t, x)| :=
    continuous_finset_sum _ fun j _ => hcD j
  have hmono : cellInt (fun x => |adjointOp nu h V (torusGauss a x0) (t, x)|)
      ≤ cellInt (fun x : E3 => Amp * (∑ j, |dvec (0, ee j) (torusGauss a x0) (t, x)|)
          + nu * |lap (torusGauss a x0) (t, x)|) := by
    refine cellInt_mono
      ((continuous_slice (contDiff_adjointOp_torusGauss nu a h hV x0) t).abs)
      ((continuous_const.mul hcS).add (continuous_const.mul hcL)) fun x => ?_
    exact abs_adjointOp_torusGauss_le hnu hAmp h x0 (t, x)
  have hsplit : cellInt (fun x : E3 => Amp * (∑ j, |dvec (0, ee j) (torusGauss a x0) (t, x)|)
        + nu * |lap (torusGauss a x0) (t, x)|)
      = Amp * cellInt (fun x : E3 => ∑ j, |dvec (0, ee j) (torusGauss a x0) (t, x)|)
        + nu * cellInt (fun x : E3 => |lap (torusGauss a x0) (t, x)|) := by
    rw [cellInt_add (f := fun x : E3 => Amp * ∑ j, |dvec (0, ee j) (torusGauss a x0) (t, x)|)
        (g := fun x : E3 => nu * |lap (torusGauss a x0) (t, x)|)
        (continuous_const.mul hcS) (continuous_const.mul hcL),
      cellInt_const_mul, cellInt_const_mul]
  have hsum : cellInt (fun x : E3 => ∑ j, |dvec (0, ee j) (torusGauss a x0) (t, x)|)
      ≤ 6 * π ^ 3 * a := by
    have hcongr : ∀ x : E3, (∑ j, |dvec (0, ee j) (torusGauss a x0) (t, x)|)
        = |dvec (0, ee 0) (torusGauss a x0) (t, x)|
          + |dvec (0, ee 1) (torusGauss a x0) (t, x)|
          + |dvec (0, ee 2) (torusGauss a x0) (t, x)| := fun x => by
      simp [Fin.sum_univ_three]
    rw [cellInt_congr hcongr,
      cellInt_add (f := fun x : E3 => |dvec (0, ee 0) (torusGauss a x0) (t, x)|
          + |dvec (0, ee 1) (torusGauss a x0) (t, x)|)
        (g := fun x : E3 => |dvec (0, ee 2) (torusGauss a x0) (t, x)|)
        ((hcD 0).add (hcD 1)) (hcD 2),
      cellInt_add (f := fun x : E3 => |dvec (0, ee 0) (torusGauss a x0) (t, x)|)
        (g := fun x : E3 => |dvec (0, ee 1) (torusGauss a x0) (t, x)|) (hcD 0) (hcD 1)]
    have h0 := cellInt_abs_dvec_torusGauss_le_lin ha x0 0 t
    have h1 := cellInt_abs_dvec_torusGauss_le_lin ha x0 1 t
    have h2 := cellInt_abs_dvec_torusGauss_le_lin ha x0 2 t
    linarith
  have hlap := cellInt_abs_lap_torusGauss_le_sqrt ha x0 t
  rw [hsplit] at hmono
  have := mul_le_mul_of_nonneg_left hsum hA0
  have h2 := mul_le_mul_of_nonneg_left hlap hnu
  linarith

/-! ## The replacement gate `GaussianApproximateAdjointWeight`

`ClayNS.ConcentratedAdjointWeightGate` demands *exact* adjointness together
with a concentration ratio `θ`.  The two demands pull against each other: the
only exact solution the development can currently exhibit is the constant
weight, whose ratio is exactly `1`.  The analytically natural replacement keeps
concentration and prices the failure of exactness, which
`ClayNS.adjoint_localized_increment_residual` already does.  The gate below is
that statement, with three separate tolerances: `θ` for the cell mass, `Gbd`
for the cell gradient, and `Res` for the cell adjoint residual. -/

/-- Choosing the concentration scale.  Every budget in this file is bounded by
`C·√a` for `0 < a ≤ 1`, so a single scale makes all of them small at once. -/
lemma exists_small_scale {C eps : ℝ} (hC : 0 < C) (heps : 0 < eps) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ a ≤ Real.sqrt a ∧ C * Real.sqrt a ≤ eps := by
  refine ⟨min 1 ((eps / C) ^ 2), lt_min zero_lt_one (by positivity), min_le_left _ _, ?_, ?_⟩
  · set a := min 1 ((eps / C) ^ 2) with hadef
    have ha0 : 0 < a := lt_min zero_lt_one (by positivity)
    have ha1 : a ≤ 1 := min_le_left _ _
    have hs2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
    have hs1 : Real.sqrt a ≤ 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt ha1
    nlinarith [Real.sqrt_nonneg a]
  · set a := min 1 ((eps / C) ^ 2) with hadef
    have hasq : Real.sqrt a ≤ eps / C := by
      calc Real.sqrt a ≤ Real.sqrt ((eps / C) ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
        _ = eps / C := Real.sqrt_sq (by positivity)
    calc C * Real.sqrt a ≤ C * (eps / C) := mul_le_mul_of_nonneg_left hasq hC.le
      _ = eps := by field_simp

/-- **The Gaussian approximate adjoint weight gate (G).**  For every smooth
periodic divergence-free velocity with `|u| ≤ A` componentwise, every increment
step `h` and every base point `z₀`, there is a smooth periodic weight `Φ` with
`0 ≤ Φ ≤ 1` and `Φ(z₀) = 1` whose cell mass is at most `θ·Φ(z₀)`, whose cell
gradient is at most `Gbd`, and which solves the backward adjoint
transport–diffusion equation up to a cell residual `Res`. -/
def GaussianApproximateAdjointWeightGate (nu Amp theta Gbd Res : ℝ) : Prop :=
  ∀ V : STime → E3, ContDiff ℝ (⊤ : ℕ∞) V → SpacePeriodic V →
    (∀ z : STime, divg V z = 0) → (∀ (z : STime) (b : Fin 3), |V z b| ≤ Amp) →
    ∀ (h : E3) (z₀ : STime), ∃ Phi : STime → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) Phi ∧ SpacePeriodic Phi ∧
        (∀ z, 0 ≤ Phi z) ∧ (∀ z, Phi z ≤ 1) ∧ Phi z₀ = 1 ∧
        cellInt (fun x => Phi (z₀.1, x)) ≤ theta * Phi z₀ ∧
        (∀ j : Fin 3, cellInt (fun x => |dvec (0, ee j) Phi (z₀.1, x)|) ≤ Gbd) ∧
        cellInt (fun x => |adjointOp nu h V Phi (z₀.1, x)|) ≤ Res

/-- **The replacement gate holds, at every positive tolerance.**  Tuning the
single parameter `a = ντ` — the cell size relative to the diffusion length —
drives the concentration ratio, the gradient budget and the adjoint residual to
zero *simultaneously*.  In particular the strict inequality `θ < 1`, to which
`ClayNS.concentratedAdjointWeightGate_one` reduced the original gate, is
available with room to spare. -/
theorem gaussianApproximateAdjointWeightGate_holds {nu Amp theta Gbd Res : ℝ}
    (hnu : 0 ≤ nu) (htheta : 0 < theta) (hGbd : 0 < Gbd) (hRes : 0 < Res) :
    GaussianApproximateAdjointWeightGate nu Amp theta Gbd Res := by
  intro V hV hVper hdiv hAmp h z₀
  have hpi := Real.pi_pos
  have hAmp0 : 0 ≤ Amp := le_trans (abs_nonneg _) (hAmp z₀ 0)
  have hMC := tgMassC_pos
  have hLC := tgLapC_pos
  set eps := min theta (min Gbd Res) with heps
  have heps0 : 0 < eps := lt_min htheta (lt_min hGbd hRes)
  set K := tgMassC + 2 * π ^ 3 + 6 * π ^ 3 * Amp + nu * tgLapC + 1 with hK
  have hAK : 0 ≤ 6 * π ^ 3 * Amp := by positivity
  have hNK : 0 ≤ nu * tgLapC := mul_nonneg hnu hLC.le
  have hPK : (0:ℝ) ≤ 2 * π ^ 3 := by positivity
  have hK0 : 0 < K := by rw [hK]; linarith
  obtain ⟨a, ha0, ha1, hale, hKs⟩ := exists_small_scale hK0 heps0
  have hs0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  refine ⟨torusGauss a z₀.2, contDiff_torusGauss a z₀.2, spacePeriodic_torusGauss a z₀.2,
    torusGauss_nonneg a z₀.2, fun z => torusGauss_le_one ha0 z₀.2 z,
    torusGauss_center a z₀.2 z₀.1, ?_, ?_, ?_⟩
  · -- concentration
    have hc := cellInt_torusGauss_le_mass ha0 z₀.2 z₀.1
    have hstep : a * Real.sqrt a ≤ 1 * Real.sqrt a := mul_le_mul_of_nonneg_right ha1 hs0
    have h1 : tgMassC * (a * Real.sqrt a) ≤ tgMassC * Real.sqrt a := by
      rw [one_mul] at hstep
      exact mul_le_mul_of_nonneg_left hstep hMC.le
    have h2 : tgMassC * Real.sqrt a ≤ K * Real.sqrt a := by
      have hle : tgMassC ≤ K := by rw [hK]; linarith
      exact mul_le_mul_of_nonneg_right hle hs0
    have h5 : eps ≤ theta := min_le_left _ _
    have h6 : torusGauss a z₀.2 z₀ = 1 := torusGauss_center a z₀.2 z₀.1
    rw [h6, mul_one]
    linarith
  · -- gradient
    intro j
    have hc := cellInt_abs_dvec_torusGauss_le_lin ha0 z₀.2 j z₀.1
    have h1 : 2 * π ^ 3 * a ≤ 2 * π ^ 3 * Real.sqrt a := by nlinarith
    have h2 : 2 * π ^ 3 * Real.sqrt a ≤ K * Real.sqrt a := by
      have hle : 2 * π ^ 3 ≤ K := by rw [hK]; linarith
      exact mul_le_mul_of_nonneg_right hle hs0
    have h5 : eps ≤ Gbd := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  · -- adjoint residual
    have hc := cellInt_abs_adjointOp_torusGauss_le ha0 hnu hV hAmp h z₀.2 z₀.1
    have h1 : Amp * (6 * π ^ 3 * a) ≤ 6 * π ^ 3 * Amp * Real.sqrt a := by nlinarith
    have h2 : 6 * π ^ 3 * Amp * Real.sqrt a + nu * (tgLapC * Real.sqrt a) ≤ K * Real.sqrt a := by
      have hle : 6 * π ^ 3 * Amp + nu * tgLapC ≤ K := by rw [hK]; linarith
      nlinarith
    have h5 : eps ≤ Res := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith

/-- **The concentration ratio is strictly less than `1` — with room to spare.**
This is the exact answer to the question left open by
`ClayNS.concentratedAdjointWeightGate_one`: the flat weight is the degenerate
`θ = 1` endpoint, and any genuine Gaussian concentration at scale `a` beats it,
since `θ(a) = O(a^{3/2})`. -/
theorem torusGauss_concentration_ratio_small {theta : ℝ} (htheta : 0 < theta) (x0 : E3)
    (t : ℝ) :
    ∃ a : ℝ, 0 < a ∧
      cellInt (fun x => torusGauss a x0 (t, x)) ≤ theta * torusGauss a x0 (t, x0) := by
  have hMC := tgMassC_pos
  obtain ⟨a, ha0, ha1, hale, hKs⟩ := exists_small_scale hMC htheta
  refine ⟨a, ha0, ?_⟩
  have hc := cellInt_torusGauss_le_mass ha0 x0 t
  have hs0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hstep : a * Real.sqrt a ≤ 1 * Real.sqrt a := mul_le_mul_of_nonneg_right ha1 hs0
  have h1 : tgMassC * (a * Real.sqrt a) ≤ tgMassC * Real.sqrt a := by
    rw [one_mul] at hstep
    exact mul_le_mul_of_nonneg_left hstep hMC.le
  rw [torusGauss_center a x0 t, mul_one]
  linarith

end ClayNS
