/-
# The log-heat second variation: the covariance term is a theorem, not an option

Rounds of this programme flirted with identifying the second variation of the
Doob-transformed potential

    V_t(x) = −log 𝔼[e^{−V(x + ξ)}]

with the (tilted) expectation of the static Hessian of `V`.  That identification
is **false**, and this file proves what is actually true, in the finite-noise
model in which the semigroup is an average over a finite family of shifts:

    (d²/ds²)|₀ (−log Σ_ω ρ_ω e^{−V(s,ω)})
        = 𝔼_tilt[∂²_s V] − Var_tilt(∂_s V).

* `hasDerivAt_partition` — the derivative of the partition sum.
* `hasDerivAt_logPartition` — the first variation is the *tilted expectation* of
  the first variation of `V`, `F′(s) = 𝔼_{μ_s}[∂_s V]`, where
  `μ_s = ρ e^{−V(s,·)}/Z(s)` is the Doob/Gibbs tilt.
* `hasDerivAt_tilted_expectation` — the second variation, i.e. the derivative of
  that first variation, is `𝔼_{μ₀}[∂²_s V] − Var_{μ₀}(∂_s V)`.

So the covariance (variance, in a single direction) term is genuine
mathematics: the dynamical curvature is the static one *minus* a gradient
fluctuation, and only the sum of the two shell estimates
(`HeatDoobCurvatureDebt.curvature_shell_of_split`) can be claimed.  This settles,
as a theorem, the question of whether the naive same-object identification
`η = H` could have been used.

**Honest status.**  This is an exact identity in the finite-noise model; it is
not a claim about the continuum Heat/Doob semigroup, and it closes no Clay row.
The frozen research count is unchanged.
-/
import RequestProject.YangMills.HeatDoobCurvatureDebt

namespace YangMills

open Finset

section LogHeat

variable {Ω : Type*} [Fintype Ω]

/-- The Doob/Gibbs tilt of a reference weight by a potential. -/
noncomputable def tiltWeight (rho : Ω → ℝ) (V : Ω → ℝ) (w : Ω) : ℝ :=
  rho w * Real.exp (-V w) / ∑ w', rho w' * Real.exp (-V w')

theorem partition_pos [Nonempty Ω] {rho : Ω → ℝ} (hrho : ∀ w, 0 < rho w) (V : Ω → ℝ) :
    0 < ∑ w, rho w * Real.exp (-V w) := by
  refine Finset.sum_pos (fun w _ => ?_) Finset.univ_nonempty
  exact mul_pos (hrho w) (Real.exp_pos _)

theorem tiltWeight_nonneg {rho : Ω → ℝ} (hrho : ∀ w, 0 ≤ rho w) (V : Ω → ℝ)
    (w : Ω) : 0 ≤ tiltWeight rho V w := by
  refine div_nonneg (mul_nonneg (hrho w) (Real.exp_pos _).le) ?_
  exact Finset.sum_nonneg fun w' _ => mul_nonneg (hrho w') (Real.exp_pos _).le

theorem tiltWeight_sum_one [Nonempty Ω] {rho : Ω → ℝ} (hrho : ∀ w, 0 < rho w) (V : Ω → ℝ) :
    ∑ w, tiltWeight rho V w = 1 := by
  have hZ := partition_pos hrho V
  simp only [tiltWeight]
  rw [← Finset.sum_div, div_self hZ.ne']

/-- The tilted expectation, written as a ratio of partition-type sums. -/
theorem wexp_tilt (rho : Ω → ℝ) (V f : Ω → ℝ) :
    wexp (tiltWeight rho V) f
      = (∑ w, rho w * (f w * Real.exp (-V w))) / ∑ w, rho w * Real.exp (-V w) := by
  rw [wexp]
  calc ∑ w, tiltWeight rho V w * f w
      = ∑ w, (rho w * (f w * Real.exp (-V w))) / ∑ w', rho w' * Real.exp (-V w') :=
        Finset.sum_congr rfl fun w _ => by rw [tiltWeight]; ring
    _ = (∑ w, rho w * (f w * Real.exp (-V w))) / ∑ w, rho w * Real.exp (-V w) := by
        rw [← Finset.sum_div]

/-- Derivative of the partition sum of a differentiable family of potentials. -/
theorem hasDerivAt_partition (rho : Ω → ℝ) {V V1 : ℝ → Ω → ℝ}
    (h1 : ∀ s w, HasDerivAt (fun t => V t w) (V1 s w) s) (s : ℝ) :
    HasDerivAt (fun t => ∑ w, rho w * Real.exp (-V t w))
      (∑ w, rho w * (-V1 s w * Real.exp (-V s w))) s := by
  refine HasDerivAt.fun_sum fun w _ => ?_
  have hexp : HasDerivAt (fun t => Real.exp (-V t w))
      (Real.exp (-V s w) * (-V1 s w)) s := ((h1 s w).neg).exp
  refine (hexp.const_mul (rho w)).congr_deriv ?_
  ring

/-- **First variation of the log-partition function is the tilted expectation.** -/
theorem hasDerivAt_logPartition [Nonempty Ω] {rho : Ω → ℝ} (hrho : ∀ w, 0 < rho w)
    {V V1 : ℝ → Ω → ℝ} (h1 : ∀ s w, HasDerivAt (fun t => V t w) (V1 s w) s) (s : ℝ) :
    HasDerivAt (fun t => -Real.log (∑ w, rho w * Real.exp (-V t w)))
      (wexp (tiltWeight rho (V s)) (V1 s)) s := by
  have hZ := partition_pos hrho (V s)
  refine (((hasDerivAt_partition rho h1 s).log hZ.ne').neg).congr_deriv ?_
  have hD : ∑ w, rho w * (-V1 s w * Real.exp (-V s w))
      = -∑ w, rho w * (V1 s w * Real.exp (-V s w)) := by
    calc ∑ w, rho w * (-V1 s w * Real.exp (-V s w))
        = ∑ w, -(rho w * (V1 s w * Real.exp (-V s w))) :=
          Finset.sum_congr rfl fun w _ => by ring
      _ = -∑ w, rho w * (V1 s w * Real.exp (-V s w)) := Finset.sum_neg_distrib _
  rw [hD, wexp_tilt, neg_div, neg_neg]

/-- **Second variation: the static Hessian minus the gradient fluctuation.**  The
derivative of the tilted expectation of `∂_s V` is
`𝔼_{μ₀}[∂²_s V] − Var_{μ₀}(∂_s V)`. -/
theorem hasDerivAt_tilted_expectation [Nonempty Ω] {rho : Ω → ℝ} (hrho : ∀ w, 0 < rho w)
    {V V1 : ℝ → Ω → ℝ} {V2 : Ω → ℝ}
    (h1 : ∀ s w, HasDerivAt (fun t => V t w) (V1 s w) s)
    (h2 : ∀ w, HasDerivAt (fun t => V1 t w) (V2 w) 0) :
    HasDerivAt (fun s => wexp (tiltWeight rho (V s)) (V1 s))
      (wexp (tiltWeight rho (V 0)) V2 - wvar (tiltWeight rho (V 0)) (V1 0)) 0 := by
  have hZpos : 0 < ∑ w, rho w * Real.exp (-V 0 w) := partition_pos hrho (V 0)
  have hN : HasDerivAt (fun s => ∑ w, rho w * (V1 s w * Real.exp (-V s w)))
      (∑ w, rho w * ((V2 w - V1 0 w * V1 0 w) * Real.exp (-V 0 w))) 0 := by
    refine HasDerivAt.fun_sum fun w _ => ?_
    have hexp : HasDerivAt (fun t => Real.exp (-V t w))
        (Real.exp (-V 0 w) * (-V1 0 w)) 0 := ((h1 0 w).neg).exp
    refine (((h2 w).mul hexp).const_mul (rho w)).congr_deriv ?_
    ring
  have hZ : HasDerivAt (fun s => ∑ w, rho w * Real.exp (-V s w))
      (∑ w, rho w * (-V1 0 w * Real.exp (-V 0 w))) 0 := hasDerivAt_partition rho h1 0
  have hfun : (fun s => wexp (tiltWeight rho (V s)) (V1 s))
      = fun s => (∑ w, rho w * (V1 s w * Real.exp (-V s w)))
          / ∑ w, rho w * Real.exp (-V s w) := by
    funext s
    exact wexp_tilt rho (V s) (V1 s)
  rw [hfun]
  refine (hN.div hZ hZpos.ne').congr_deriv ?_
  -- pure algebra in the four sums
  set SZ : ℝ := ∑ w, rho w * Real.exp (-V 0 w) with hSZ
  set S1 : ℝ := ∑ w, rho w * (V1 0 w * Real.exp (-V 0 w)) with hS1
  set S2 : ℝ := ∑ w, rho w * ((fun w => V1 0 w * V1 0 w) w * Real.exp (-V 0 w)) with hS2
  set SH : ℝ := ∑ w, rho w * (V2 w * Real.exp (-V 0 w)) with hSH
  have hnum : ∑ w, rho w * ((V2 w - V1 0 w * V1 0 w) * Real.exp (-V 0 w)) = SH - S2 := by
    rw [hSH, hS2]
    calc ∑ w, rho w * ((V2 w - V1 0 w * V1 0 w) * Real.exp (-V 0 w))
        = ∑ w, (rho w * (V2 w * Real.exp (-V 0 w))
            - rho w * ((fun w => V1 0 w * V1 0 w) w * Real.exp (-V 0 w))) :=
          Finset.sum_congr rfl fun w _ => by simp only; ring
      _ = SH - S2 := Finset.sum_sub_distrib _ _
  have hden : ∑ w, rho w * (-V1 0 w * Real.exp (-V 0 w)) = -S1 := by
    rw [hS1]
    calc ∑ w, rho w * (-V1 0 w * Real.exp (-V 0 w))
        = ∑ w, -(rho w * (V1 0 w * Real.exp (-V 0 w))) :=
          Finset.sum_congr rfl fun w _ => by ring
      _ = -S1 := Finset.sum_neg_distrib _
  have hE2 : wexp (tiltWeight rho (V 0)) V2 = SH / SZ := by
    rw [wexp_tilt, ← hSZ, ← hSH]
  have hEV : wexp (tiltWeight rho (V 0)) (V1 0) = S1 / SZ := by
    rw [wexp_tilt, ← hSZ, ← hS1]
  have hEsq : wexp (tiltWeight rho (V 0)) (fun w => V1 0 w * V1 0 w) = S2 / SZ := by
    rw [wexp_tilt, ← hSZ, ← hS2]
  have hvar : wvar (tiltWeight rho (V 0)) (V1 0) = S2 / SZ - (S1 / SZ) * (S1 / SZ) := by
    rw [wvar, wcov, hEsq, hEV]
  rw [hnum, hden, hE2, hvar]
  field_simp
  ring

end LogHeat

end YangMills
