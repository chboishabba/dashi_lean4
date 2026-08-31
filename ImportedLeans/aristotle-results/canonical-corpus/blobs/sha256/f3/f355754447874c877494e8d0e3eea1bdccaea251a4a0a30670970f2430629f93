/-
# The covariance row is not a separate estimate

`WeightedInfluenceRows.weighted_row_of_split` reduces the dynamical (Heat/Doob)
weighted influence row to a static row plus a *covariance* row, and
`LogHeatSecondVariation` shows that covariance term cannot be dropped.  This
file removes the covariance row as an independently requestable hypothesis, by
deriving it from the two things stochastic analysis actually produces:

* `weighted_row_of_decay` — exponential decay of the kernel in the lattice
  distance, `M(x,y) ≤ K·θ^{d(x,y)}`, together with a lattice growth bound on
  spheres, `#{y : d(x,y) = r} ≤ G·gʳ`, gives the `(3/2)^d`-weighted row bound

      Σ_y (3/2)^{d(x,y)}·M(x,y) ≤ K·G/(1 − (3/2)gθ)

  whenever `(3/2)·g·θ < 1`, uniformly in the finite volume.  All-order Dyson
  rows and semigroup quasi-locality then follow from `WeightedInfluenceRows`.
* `cov_shell_of_variance_shells` — a geometric *variance* shell for the two
  gradients gives a geometric covariance shell,
  `|Cov(f,g)| ≤ √(A·B)·2⁻ⁿ`, which is exactly the input of
  `HeatDoobCurvatureDebt.curvature_shell_of_split`.  So a first-gradient
  fluctuation (Cauchy) estimate suffices; no separate covariance-decay theorem
  is needed.

**Honest status.**  The decay constant `θ`, the growth constants `G, g` and the
variance shells are hypotheses.  Nothing here closes Row C; the frozen research
count is unchanged.
-/
import RequestProject.YangMills.WeightedInfluenceRows
import RequestProject.YangMills.HeatDoobCurvatureDebt
import RequestProject.YangMills.BetaObserver

namespace YangMills

open Finset

section Row

variable {S : Type*} [Fintype S] [DecidableEq S]

omit [DecidableEq S] in
/-- **A weighted row from exponential decay and lattice growth.** -/
theorem weighted_row_of_decay {d : S → S → ℕ} {M : S → S → ℝ} {K G g theta : ℝ}
    (hdecay : ∀ x y, M x y ≤ K * theta ^ d x y)
    (hsphere : ∀ (x : S) (r : ℕ),
      ((univ.filter fun y => d x y = r).card : ℝ) ≤ G * g ^ r)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hg : 0 ≤ g) (htheta : 0 ≤ theta)
    (hprod : (3 / 2 : ℝ) * g * theta < 1) (x : S) :
    ∑ y, metricWeight d x y * M x y ≤ K * G / (1 - (3 / 2 : ℝ) * g * theta) := by
  set rho : ℝ := (3 / 2 : ℝ) * theta with hrho
  have hrho0 : 0 ≤ rho := by positivity
  set N : ℕ := Finset.sup univ fun y => d x y with hN
  have hle : ∀ y : S, d x y ≤ N := fun y => Finset.le_sup (f := fun y => d x y) (mem_univ y)
  -- step 1: the weighted row is bounded by a distance sum
  have hstep1 : ∑ y, metricWeight d x y * M x y ≤ ∑ y, K * rho ^ d x y := by
    refine Finset.sum_le_sum fun y _ => ?_
    have hw : metricWeight d x y = (3 / 2 : ℝ) ^ d x y := rfl
    calc metricWeight d x y * M x y
        ≤ (3 / 2 : ℝ) ^ d x y * (K * theta ^ d x y) := by
          rw [hw]
          exact mul_le_mul_of_nonneg_left (hdecay x y) (by positivity)
      _ = K * rho ^ d x y := by rw [hrho, mul_pow]; ring
  -- step 2: group the distance sum into spheres
  have hmaps : ∀ y ∈ (univ : Finset S), d x y ∈ range (N + 1) := by
    intro y _
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hle y))
  have hfiber : ∑ r ∈ range (N + 1), ∑ y ∈ univ.filter fun y => d x y = r,
      K * rho ^ d x y = ∑ y, K * rho ^ d x y :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  have hinner : ∀ r ∈ range (N + 1),
      (∑ y ∈ univ.filter fun y => d x y = r, K * rho ^ d x y)
        ≤ (G * g ^ r) * (K * rho ^ r) := by
    intro r _
    have hconst : (∑ y ∈ univ.filter fun y => d x y = r, K * rho ^ d x y)
        = ((univ.filter fun y => d x y = r).card : ℝ) * (K * rho ^ r) := by
      rw [Finset.sum_congr rfl (fun y hy => by
        rw [(Finset.mem_filter.mp hy).2]), Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    exact mul_le_mul_of_nonneg_right (hsphere x r) (by positivity)
  have hstep2 : ∑ y, K * rho ^ d x y
      ≤ ∑ r ∈ range (N + 1), (G * g ^ r) * (K * rho ^ r) := by
    rw [← hfiber]
    exact Finset.sum_le_sum hinner
  -- step 3: the geometric sum
  have hgeom : ∑ r ∈ range (N + 1), (G * g ^ r) * (K * rho ^ r)
      = (K * G) * ∑ r ∈ range (N + 1), (g * rho) ^ r := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [mul_pow]; ring
  have hq0 : 0 ≤ g * rho := by positivity
  have hq1 : g * rho < 1 := by
    rw [hrho]
    nlinarith [hprod]
  have hsum : ∑ r ∈ range (N + 1), (g * rho) ^ r ≤ 1 / (1 - g * rho) :=
    geom_sum_le_inv_one_sub hq0 hq1 (N + 1)
  have hKG : 0 ≤ K * G := mul_nonneg hK hG
  have hident : g * rho = (3 / 2 : ℝ) * g * theta := by rw [hrho]; ring
  calc ∑ y, metricWeight d x y * M x y ≤ ∑ y, K * rho ^ d x y := hstep1
    _ ≤ ∑ r ∈ range (N + 1), (G * g ^ r) * (K * rho ^ r) := hstep2
    _ = (K * G) * ∑ r ∈ range (N + 1), (g * rho) ^ r := hgeom
    _ ≤ (K * G) * (1 / (1 - g * rho)) := mul_le_mul_of_nonneg_left hsum hKG
    _ = K * G / (1 - (3 / 2 : ℝ) * g * theta) := by rw [hident]; ring

end Row

section Shell

variable {Ω : Type*} [Fintype Ω]

/-- **A covariance shell from two variance shells.**  A geometric bound on the
fluctuations of the two gradients gives a geometric covariance shell — the
input consumed by `curvature_shell_of_split`. -/
theorem cov_shell_of_variance_shells {rho : Ω → ℝ} {f g : Ω → ℝ} {A B : ℝ} {n : ℕ}
    (hrho : ∀ w, 0 ≤ rho w) (hnorm : ∑ w, rho w = 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : wvar rho f ≤ A * (1 / 2 : ℝ) ^ n) (hg : wvar rho g ≤ B * (1 / 2 : ℝ) ^ n) :
    |wcov rho f g| ≤ Real.sqrt (A * B) * (1 / 2 : ℝ) ^ n := by
  have hpow : (0:ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
  have hbound := abs_wcov_le_sqrt hrho hnorm f g
  have h1 : Real.sqrt (wvar rho f) ≤ Real.sqrt (A * (1 / 2 : ℝ) ^ n) :=
    Real.sqrt_le_sqrt hf
  have h2 : Real.sqrt (wvar rho g) ≤ Real.sqrt (B * (1 / 2 : ℝ) ^ n) :=
    Real.sqrt_le_sqrt hg
  have hmul : Real.sqrt (wvar rho f) * Real.sqrt (wvar rho g)
      ≤ Real.sqrt (A * (1 / 2 : ℝ) ^ n) * Real.sqrt (B * (1 / 2 : ℝ) ^ n) := by
    refine mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hprod : Real.sqrt (A * (1 / 2 : ℝ) ^ n) * Real.sqrt (B * (1 / 2 : ℝ) ^ n)
      = Real.sqrt (A * B) * (1 / 2 : ℝ) ^ n := by
    rw [← Real.sqrt_mul (by positivity)]
    have hre : A * (1 / 2 : ℝ) ^ n * (B * (1 / 2 : ℝ) ^ n)
        = (A * B) * ((1 / 2 : ℝ) ^ n) ^ 2 := by ring
    rw [hre, Real.sqrt_mul (mul_nonneg hA hB), Real.sqrt_sq hpow]
  calc |wcov rho f g| ≤ Real.sqrt (wvar rho f) * Real.sqrt (wvar rho g) := hbound
    _ ≤ Real.sqrt (A * (1 / 2 : ℝ) ^ n) * Real.sqrt (B * (1 / 2 : ℝ) ^ n) := hmul
    _ = Real.sqrt (A * B) * (1 / 2 : ℝ) ^ n := hprod

end Shell

end YangMills
