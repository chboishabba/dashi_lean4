/-
# Coarse-grained resolution of the gradient defect (`A-res`), and the weight cut

Two independent items on the `A` side.

## 1. `GradientDefectCoarseResolution`

For any splitting `u = U^ℓ + (u − U^ℓ)` of the velocity into a resolved
(mollified) part and a subfilter remainder, the *gradient* density splits
subadditively,

  `|∇u|² ≤ 2|∇U^ℓ|² + 2|∇(u − U^ℓ)|²`,

hence, cylinder by cylinder,

  `Q_∇(u; r) ≤ 2 Q_∇(U^ℓ; r) + 2 Q_∇(u − U^ℓ; r)`.        (A-res)

Consequently a gradient defect `Q_∇(u; r) ≥ ε` forces a *dichotomy*: either the
resolved viscous dissipation carries `ε/4`, or the subfilter gradient does.  No
signed detector, and no "large resolved velocity–pressure quantity must be seen
by signed work" bridge, is needed for this step: `Q_∇` is already
constant-excluding, so both branches are genuine defects.

## 2. Geometric weights do not exclude a bad scale at every dyadic radius

A telescope with dyadic weights `w_k = r_k/r_0 ≍ 2^{-k}` is *summable*, so a
bound `∑_k w_k D_k ≤ B` is compatible with `D_k = ε` at **every** scale as soon
as `B ≥ 2ε`, uniformly in the number of scales.  What the almost-monotonicity
route needs is a bound in *logarithmic* scale, i.e. a roughly unweighted cost
per dyadic step, and that is a strictly stronger requirement: the unweighted
sums of the same sequence diverge.  `geometric_telescope_not_scale_exclusive`
proves both halves.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ScaleInvariantGradientEnergy

open MeasureTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

namespace ClayNS

/-! ## The pointwise gradient splitting -/

/-- The pointwise gradient bound behind (A-res): for a splitting `u = U + w`
into two differentiable pieces, `‖∇u‖² ≤ 2‖∇U‖² + 2‖∇w‖²`. -/
theorem norm_fderiv_sq_add_le (U W : E3 → E3) {y : E3} (hU : DifferentiableAt ℝ U y)
    (hW : DifferentiableAt ℝ W y) :
    ‖fderiv ℝ (fun x => U x + W x) y‖ ^ 2 ≤ 2 * ‖fderiv ℝ U y‖ ^ 2 + 2 * ‖fderiv ℝ W y‖ ^ 2 := by
  have hd : fderiv ℝ (fun x => U x + W x) y = fderiv ℝ U y + fderiv ℝ W y := fderiv_add hU hW
  rw [hd]
  have htri : ‖fderiv ℝ U y + fderiv ℝ W y‖ ≤ ‖fderiv ℝ U y‖ + ‖fderiv ℝ W y‖ := norm_add_le _ _
  have h0 : (0:ℝ) ≤ ‖fderiv ℝ U y‖ := norm_nonneg _
  have h1 : (0:ℝ) ≤ ‖fderiv ℝ W y‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖fderiv ℝ U y‖ - ‖fderiv ℝ W y‖), norm_nonneg
    (fderiv ℝ U y + fderiv ℝ W y)]

/-- **The gradient density of a velocity field is subadditive under any
splitting.**  With `u = U^ℓ + (u − U^ℓ)` this is the resolution used in (A-res). -/
theorem gradDensity_split_le (U W : ℝ → E3 → E3)
    (hU : ∀ s, Differentiable ℝ (U s)) (hW : ∀ s, Differentiable ℝ (W s)) (s : ℝ) (y : E3) :
    ‖fderiv ℝ (fun x => U s x + W s x) y‖ ^ 2
      ≤ 2 * ‖fderiv ℝ (U s) y‖ ^ 2 + 2 * ‖fderiv ℝ (W s) y‖ ^ 2 :=
  norm_fderiv_sq_add_le (U s) (W s) (hU s y) (hW s y)

/-! ## Monotonicity of the cylinder quantity, and (A-res) -/

/-- Monotonicity of `Q_∇` in the density (for `r ≥ 0`), given integrability of
both densities on the cylinder. -/
theorem QgradCyl_mono {G G' : ℝ → E3 → ℝ} {t0 : ℝ} {x0 : E3} {r : ℝ} (hr : 0 ≤ r)
    (hle : ∀ s y, G s y ≤ G' s y)
    (hint : IntervalIntegrable (fun s => ∫ y in Metric.ball x0 r, G s y) volume (t0 - r ^ 2) t0)
    (hint' : IntervalIntegrable (fun s => ∫ y in Metric.ball x0 r, G' s y) volume (t0 - r ^ 2) t0)
    (hGint : ∀ s, IntegrableOn (G s) (Metric.ball x0 r) volume)
    (hG'int : ∀ s, IntegrableOn (G' s) (Metric.ball x0 r) volume) :
    QgradCyl G t0 x0 r ≤ QgradCyl G' t0 x0 r := by
  have hts : t0 - r ^ 2 ≤ t0 := by nlinarith [sq_nonneg r]
  have hmono : (∫ s in (t0 - r ^ 2)..t0, ∫ y in Metric.ball x0 r, G s y)
      ≤ ∫ s in (t0 - r ^ 2)..t0, ∫ y in Metric.ball x0 r, G' s y := by
    refine intervalIntegral.integral_mono_on hts hint hint' fun s _ => ?_
    exact integral_mono (hGint s) (hG'int s) fun y => hle s y
  have hrinv : (0:ℝ) ≤ r⁻¹ := inv_nonneg.mpr hr
  exact mul_le_mul_of_nonneg_left hmono hrinv

/-- `Q_∇` of a sum of two densities with coefficient `2`. -/
theorem QgradCyl_two_add (G1 G2 : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3) {r : ℝ}
    (hint1 : ∀ s, IntegrableOn (G1 s) (Metric.ball x0 r) volume)
    (hint2 : ∀ s, IntegrableOn (G2 s) (Metric.ball x0 r) volume)
    (hI1 : IntervalIntegrable (fun s => ∫ y in Metric.ball x0 r, G1 s y) volume (t0 - r ^ 2) t0)
    (hI2 : IntervalIntegrable (fun s => ∫ y in Metric.ball x0 r, G2 s y) volume (t0 - r ^ 2) t0) :
    QgradCyl (fun s y => 2 * G1 s y + 2 * G2 s y) t0 x0 r
      = 2 * QgradCyl G1 t0 x0 r + 2 * QgradCyl G2 t0 x0 r := by
  have hinner : ∀ s : ℝ, (∫ y in Metric.ball x0 r, (2 * G1 s y + 2 * G2 s y))
      = 2 * (∫ y in Metric.ball x0 r, G1 s y) + 2 * ∫ y in Metric.ball x0 r, G2 s y := by
    intro s
    rw [integral_add ((hint1 s).const_mul 2) ((hint2 s).const_mul 2), integral_const_mul,
      integral_const_mul]
  simp only [QgradCyl]
  rw [intervalIntegral.integral_congr (g := fun s => 2 * (∫ y in Metric.ball x0 r, G1 s y)
      + 2 * ∫ y in Metric.ball x0 r, G2 s y) (fun s _ => hinner s),
    intervalIntegral.integral_add (hI1.const_mul 2) (hI2.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- **`GradientDefectCoarseResolution` (A-res).**  For any splitting of the
density subadditively dominated by a resolved and a subfilter part,

`Q_∇(u; r) ≤ 2 Q_∇(U^ℓ; r) + 2 Q_∇(u − U^ℓ; r)`. -/
theorem gradient_defect_coarse_resolution {G G1 G2 : ℝ → E3 → ℝ} {t0 : ℝ} {x0 : E3} {r : ℝ}
    (hr : 0 ≤ r) (hle : ∀ s y, G s y ≤ 2 * G1 s y + 2 * G2 s y)
    (hGint : ∀ s, IntegrableOn (G s) (Metric.ball x0 r) volume)
    (hint1 : ∀ s, IntegrableOn (G1 s) (Metric.ball x0 r) volume)
    (hint2 : ∀ s, IntegrableOn (G2 s) (Metric.ball x0 r) volume)
    (hI : IntervalIntegrable (fun s => ∫ y in Metric.ball x0 r, G s y) volume (t0 - r ^ 2) t0)
    (hI1 : IntervalIntegrable (fun s => ∫ y in Metric.ball x0 r, G1 s y) volume (t0 - r ^ 2) t0)
    (hI2 : IntervalIntegrable (fun s => ∫ y in Metric.ball x0 r, G2 s y) volume (t0 - r ^ 2) t0) :
    QgradCyl G t0 x0 r ≤ 2 * QgradCyl G1 t0 x0 r + 2 * QgradCyl G2 t0 x0 r := by
  have hsum : IntervalIntegrable
      (fun s => ∫ y in Metric.ball x0 r, (2 * G1 s y + 2 * G2 s y)) volume (t0 - r ^ 2) t0 := by
    have hcongr : ∀ s ∈ Set.uIcc (t0 - r ^ 2) t0,
        (∫ y in Metric.ball x0 r, (2 * G1 s y + 2 * G2 s y))
          = 2 * (∫ y in Metric.ball x0 r, G1 s y) + 2 * ∫ y in Metric.ball x0 r, G2 s y := by
      intro s _
      rw [integral_add ((hint1 s).const_mul 2) ((hint2 s).const_mul 2), integral_const_mul,
        integral_const_mul]
    refine IntervalIntegrable.congr (f := fun s => 2 * (∫ y in Metric.ball x0 r, G1 s y)
      + 2 * ∫ y in Metric.ball x0 r, G2 s y) ?_ ((hI1.const_mul 2).add (hI2.const_mul 2))
    intro s hs
    exact (hcongr s (Set.uIoc_subset_uIcc hs)).symm
  calc QgradCyl G t0 x0 r
      ≤ QgradCyl (fun s y => 2 * G1 s y + 2 * G2 s y) t0 x0 r := by
        refine QgradCyl_mono hr hle hI hsum hGint fun s => ?_
        exact ((hint1 s).const_mul 2).add ((hint2 s).const_mul 2)
    _ = 2 * QgradCyl G1 t0 x0 r + 2 * QgradCyl G2 t0 x0 r :=
        QgradCyl_two_add G1 G2 t0 x0 hint1 hint2 hI1 hI2

/-- **The coarse-graining dichotomy.**  A gradient defect at scale `r` is either
resolved viscous dissipation or a subfilter gradient defect, each at level
`ε/4`. -/
theorem gradient_defect_dichotomy {G G1 G2 : ℝ → E3 → ℝ} {t0 : ℝ} {x0 : E3} {r eps : ℝ}
    (hres : QgradCyl G t0 x0 r ≤ 2 * QgradCyl G1 t0 x0 r + 2 * QgradCyl G2 t0 x0 r)
    (hdef : eps ≤ QgradCyl G t0 x0 r) :
    eps / 4 ≤ QgradCyl G1 t0 x0 r ∨ eps / 4 ≤ QgradCyl G2 t0 x0 r := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  linarith

/-! ## The weight cut: geometric telescopes are compatible with a bad scale at
every dyadic radius -/

/-- **A geometrically weighted ledger cannot exclude a defect at every dyadic
scale.**  The constant sequence `D_k = ε` obeys `∑_{k<N} 2^{-k} D_k ≤ 2ε` for
*every* `N`, while its unweighted partial sums diverge.  Hence a bound of the
form `∑_k (r_k/r_0) D_k ≤ B` is strictly weaker than the logarithmic
(`∫ D dr/r`, i.e. unweighted per dyadic step) bound that the
almost-monotonicity route consumes. -/
theorem geometric_telescope_not_scale_exclusive {eps : ℝ} (heps : 0 < eps) :
    (∀ N : ℕ, ∑ k ∈ range N, (2 : ℝ) ^ (-(k : ℤ)) * eps ≤ 2 * eps) ∧
      Tendsto (fun N : ℕ => ∑ _k ∈ range N, eps) atTop atTop := by
  constructor
  · intro N
    have hgeom : ∑ k ∈ range N, (2 : ℝ) ^ (-(k : ℤ)) = ∑ k ∈ range N, ((1:ℝ)/2) ^ k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [zpow_neg, zpow_natCast, ← inv_pow]
      norm_num
    have hsum : ∑ k ∈ range N, ((1:ℝ)/2) ^ k ≤ 2 := by
      rw [geom_sum_eq (by norm_num)]
      have h0 : (0:ℝ) ≤ ((1:ℝ)/2) ^ N := by positivity
      rw [div_le_iff_of_neg (by norm_num : ((1:ℝ)/2 - 1) < 0)]
      linarith
    calc ∑ k ∈ range N, (2 : ℝ) ^ (-(k : ℤ)) * eps
        = (∑ k ∈ range N, (2 : ℝ) ^ (-(k : ℤ))) * eps := by rw [Finset.sum_mul]
      _ ≤ 2 * eps := by
          rw [hgeom]; exact mul_le_mul_of_nonneg_right hsum (le_of_lt heps)
  · have hform : (fun N : ℕ => ∑ _k ∈ range N, eps) = fun N : ℕ => (N : ℝ) * eps := by
      funext N; simp [Finset.sum_const, nsmul_eq_mul]
    rw [hform]
    exact Tendsto.atTop_mul_const heps tendsto_natCast_atTop_atTop

end ClayNS
