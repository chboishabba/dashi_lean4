/-
# Non-vacuity and axiom checks for the response-kernel and curvature-debt rounds

Three things are recorded here.

1. **Row A-ii is non-vacuous.**  An explicit trajectory with a genuinely nonzero
   propagated irrelevant response satisfies every hypothesis of
   `cumulative_lipschitz_of_response`, so the cutoff-uniform sensitivity bound is
   not an empty statement.
2. **Row C spatial is non-vacuous.**  An explicit two-site kernel with a genuine
   off-diagonal entry satisfies the `(3/2)^d`-weighted row hypothesis, so the
   all-order power bound and the exponential clustering bound apply to a
   nontrivial kernel.
3. **The covariance term of the log-heat second variation cannot be dropped.**
   `covariance_term_not_removable` exhibits a two-point noise and a potential
   family with `∂²_s V ≡ 0` whose log-heat second variation equals `−1`.  So the
   identification of the dynamical curvature with the tilted static Hessian is
   *false*, and the split form used in `HeatDoobCurvatureDebt` is the only
   available one.
-/
import RequestProject.YangMills.RowAResponseKernelClosure
import RequestProject.YangMills.WeightedInfluenceRows
import RequestProject.YangMills.LogHeatSecondVariation

namespace YangMills

namespace ResponseChecks

open Finset

open scoped Nat

/-! ## 1. Row A-ii: an inhabited response package -/

/-- A linear trajectory with unit shell coefficient. -/
noncomputable def wU (j : ℕ) : ℝ := 1 + j

/-- The quartic source injection, saturating its own budget. -/
noncomputable def wS (j : ℕ) : ℝ := couplingSq wU j ^ 2

/-- The propagated irrelevant response, saturating the one-step recurrence. -/
noncomputable def wR : ℕ → ℝ
  | 0 => 0
  | (j + 1) => wS j + wR j / 2

/-- The marginal (current-coupling) shell sensitivity. -/
noncomputable def wM (j : ℕ) : ℝ := couplingSq wU j ^ 2

theorem wU_pos (j : ℕ) : 0 < wU j := by
  have : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  simp only [wU]
  linarith

theorem wS_nonneg (j : ℕ) : 0 ≤ wS j := by
  simp only [wS]
  positivity

theorem wR_nonneg : ∀ j, 0 ≤ wR j
  | 0 => le_refl 0
  | (j + 1) => by
      have := wR_nonneg j
      have := wS_nonneg j
      simp only [wR]
      linarith

theorem wR_one_pos : 0 < wR 1 := by
  have h : wR 1 = wS 0 + wR 0 / 2 := rfl
  have h0 : wS 0 = 1 := by
    simp [wS, couplingSq, wU]
  rw [h, h0]
  simp [wR]

/-- **The Row A-ii response package is inhabited**: the cutoff-uniform
cumulative sensitivity bound holds for a family whose propagated irrelevant
response is genuinely nonzero. -/
theorem response_package_inhabited (K : ℕ) :
    ∑ j ∈ range K, (wM j + wR j)
      ≤ (1 + 2 * 1 * 1) * (((wU 0 + 1) / wU 0) * (1:ℝ)⁻¹ * couplingSq wU 0) := by
  refine cumulative_lipschitz_of_response (u := wU) (beta := fun _ => 1)
    (L := fun j => wM j + wR j) (m := wM) (r := wR) (s := wS)
    (bm := 1) (bp := 1) (Cm := 1) (R := 1) (D := 1)
    (fun j => by simp [wU]; ring) (fun _ => le_refl 1) (fun _ => le_refl 1)
    one_pos (wU_pos 0) zero_le_one zero_le_one zero_le_one
    (fun j => le_refl _) (fun j => by simp [wM]) rfl wR_nonneg
    (fun j => by simp only [wR]; linarith) (fun j => by simp [wS]) K

/-! ## 2. Row C spatial: an inhabited weighted-row package -/

/-- Two sites at distance one. -/
def twoSiteDist : Bool → Bool → ℕ := fun x y => if x = y then 0 else 1

/-- A kernel with a genuine off-diagonal influence. -/
noncomputable def twoSiteKernel : Bool → Bool → ℝ := fun x y => if x = y then 0 else 1 / 2

theorem twoSiteDist_self (x : Bool) : twoSiteDist x x = 0 := by simp [twoSiteDist]

theorem twoSiteDist_tri (x y z : Bool) :
    twoSiteDist x z ≤ twoSiteDist x y + twoSiteDist y z := by
  revert x y z
  decide

theorem twoSiteKernel_nonneg (x y : Bool) : 0 ≤ twoSiteKernel x y := by
  by_cases h : x = y <;> simp [twoSiteKernel, h]

theorem twoSiteKernel_off_diag : twoSiteKernel true false = 1 / 2 := by
  simp [twoSiteKernel]

theorem twoSite_row (x : Bool) :
    ∑ y, metricWeight twoSiteDist x y * twoSiteKernel x y ≤ 3 / 4 := by
  cases x <;>
    simp [metricWeight, twoSiteDist, twoSiteKernel] <;> norm_num

/-- **The Row C spatial package is inhabited**: exponential clustering of the
semigroup of a kernel with a genuinely nonzero off-diagonal entry. -/
theorem clustering_package_inhabited (t : ℝ) (ht : 0 ≤ t) (x y : Bool) :
    ∑' n : ℕ, t ^ n / n ! * iterKernel twoSiteKernel n x y
      ≤ (2 / 3 : ℝ) ^ twoSiteDist x y * Real.exp (3 / 4 * t) :=
  exp_series_cluster twoSiteDist_self twoSiteDist_tri twoSiteKernel_nonneg
    twoSite_row (by norm_num) ht x y

/-! ## 3. The covariance term is genuine -/

/-- A symmetric two-point noise. -/
def signOf : Bool → ℝ := fun w => if w then 1 else -1

/-- The linear potential family `V(s,ω) = s·ξ_ω`, whose second variation in `s`
vanishes identically. -/
noncomputable def linV : ℝ → Bool → ℝ := fun s w => s * signOf w

theorem linV_deriv (s : ℝ) (w : Bool) :
    HasDerivAt (fun t => linV t w) (signOf w) s := by
  simpa [linV, mul_comm] using (hasDerivAt_id s).mul_const (signOf w)

theorem linV_second_deriv (w : Bool) :
    HasDerivAt (fun _ : ℝ => signOf w) (0 : ℝ) 0 := hasDerivAt_const 0 (signOf w)

/-- **The naive identification is false.**  For the two-point noise and the
linear family `V(s,ω) = s·ξ_ω` the static second variation vanishes, yet the
second variation of the log-heat potential equals `−1`: it is exactly minus the
gradient variance. -/
theorem covariance_term_not_removable :
    HasDerivAt (fun s => wexp (tiltWeight (fun _ : Bool => (1:ℝ)) (linV s)) (fun w => signOf w))
      (-1 : ℝ) 0 := by
  have h := hasDerivAt_tilted_expectation (rho := fun _ : Bool => (1:ℝ))
    (V := linV) (V1 := fun _ w => signOf w) (V2 := fun _ => 0)
    (fun _ => one_pos) linV_deriv linV_second_deriv
  have hval : wexp (tiltWeight (fun _ : Bool => (1:ℝ)) (linV 0)) (fun _ => 0)
      - wvar (tiltWeight (fun _ : Bool => (1:ℝ)) (linV 0)) (fun w => signOf w) = -1 := by
    simp [wexp, wvar, wcov, tiltWeight, linV, signOf]
    norm_num
  rwa [hval] at h

#print axioms cumulative_lipschitz_of_response
#print axioms tuned_bare_coupling_canonical
#print axioms weighted_iter_row_le
#print axioms exp_series_cluster
#print axioms curvature_debt_total
#print axioms hasDerivAt_tilted_expectation
#print axioms covariance_term_not_removable

end ResponseChecks

end YangMills
