/-
# The KNSŠ blow-up rescaling and the oscillation defect (target R1)

This file formalizes the *scale bookkeeping* of the blow-up (KNSŠ) rescaling
about a velocity maximum, in the form required by the strengthened extraction
statement R1:

  `u_k(y) = M_k⁻¹ · u (x_k + M_k⁻¹ y)`,

and the exact identity

  `osc_{B_R} u_k = M_k⁻¹ · osc_{B_{R/M_k}(x_k)} u`.                    (§2)

Everything here is unconditional and proved; nothing is postulated.  What the
file *does not* contain is the analytic input `A`
(`SingularScaleVelocityScaleMatching`): that a genuine singularity forces a
non-degenerate defect at the velocity scale.  The point of the file is to make
precise, and reduce to an equivalent elementary statement, exactly what that
input has to say.

Main results.

* `ClayNS.oscOn_add_const` — the oscillation is invariant under adding a
  constant vector to the field (the Galilean invariance that makes it the right
  constant-excluding quantity).
* `ClayNS.oscOn_blowupSpace` — the boxed identity of §2.
* `ClayNS.oscOn_blowupSpace_ge_iff` — hence R1-osc at the rescaled unit scale is
  *equivalent* to the original-scale inequality
  `osc_{B_{R/M}(x)} u ≥ c M`.
* `ClayNS.flatMax_iff` — the negation ("asymptotically flat velocity maximum")
  is likewise equivalent to the vanishing of the rescaled oscillation, and
  `ClayNS.tendsto_blowup_sub_center_of_flat`: on a flat maximum the rescaled
  fields converge to their own centre value uniformly on balls, i.e. locally to
  a constant.
* `ClayNS.oscOn_ge_of_fderiv_lower` — the mean-value package of §4: a large
  derivative *plus* a Lipschitz bound on the derivative gives an oscillation
  lower bound.
* `ClayNS.oscOn_blowup_ge_of_gradient_defect` — its scaled form: from
  `‖∇u(x₀)e‖ ≥ c₁M²` and `‖∇u(z) − ∇u(x₀)‖ ≤ C M³‖z − x₀‖` on `B_{ρ/M}(x₀)`
  one gets the *scale-independent* defect `osc_{B_ρ} u_M ≥ c₁²/(4C)`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ClayPeriodic

open scoped Pointwise
open Metric Set

noncomputable section

namespace ClayNS

/-! ## Oscillation -/

/-- The oscillation of a vector field on a set: `sup_{x,y ∈ S} ‖f x - f y‖`,
implemented as the diameter of the image.  (As with `Metric.diam`, the value is
`0` when the image is unbounded; all statements below either bound it from above
or supply boundedness.) -/
def oscOn {α : Type*} (f : α → E3) (S : Set α) : ℝ := Metric.diam (f '' S)

lemma oscOn_nonneg {α : Type*} (f : α → E3) (S : Set α) : 0 ≤ oscOn f S :=
  Metric.diam_nonneg

/-- Two-point lower bound for the oscillation, given boundedness of the image. -/
lemma norm_sub_le_oscOn {α : Type*} {f : α → E3} {S : Set α}
    (hb : Bornology.IsBounded (f '' S)) {x y : α} (hx : x ∈ S) (hy : y ∈ S) :
    ‖f x - f y‖ ≤ oscOn f S := by
  have := Metric.dist_le_diam_of_mem hb (mem_image_of_mem f hx) (mem_image_of_mem f hy)
  simpa [dist_eq_norm, oscOn] using this

/-- A sup bound on the field bounds the oscillation. -/
lemma oscOn_le_two_mul {α : Type*} {f : α → E3} {S : Set α} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ x ∈ S, ‖f x‖ ≤ K) : oscOn f S ≤ 2 * K := by
  refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
  rintro p ⟨x, hx, rfl⟩ q ⟨y, hy, rfl⟩
  calc dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := by
        simpa [dist_eq_norm] using norm_sub_le (f x) (f y)
    _ ≤ K + K := add_le_add (h x hx) (h y hy)
    _ = 2 * K := by ring

/-- The oscillation of a constant field vanishes. -/
@[simp] lemma oscOn_const {α : Type*} (b : E3) (S : Set α) :
    oscOn (fun _ => b) S = 0 := by
  classical
  rcases S.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · simp [oscOn, h]
  · have : (fun _ : α => b) '' S = {b} := by
      apply Set.eq_singleton_iff_unique_mem.2
      exact ⟨mem_image_of_mem _ hx, by rintro y ⟨z, _, rfl⟩; rfl⟩
    simp [oscOn, this]

/-- **Galilean invariance**: adding a constant vector does not change the
oscillation. -/
lemma oscOn_add_const {α : Type*} (f : α → E3) (b : E3) (S : Set α) :
    oscOn (fun x => f x + b) S = oscOn f S := by
  have himg : (fun x => f x + b) '' S = (fun v : E3 => v + b) '' (f '' S) := by
    rw [← Set.image_comp]; rfl
  have hiso : Isometry (fun v : E3 => v + b) := (IsometryEquiv.addRight b).isometry
  rw [oscOn, oscOn, himg, hiso.diam_image]

/-- Scaling of the oscillation in the field. -/
lemma oscOn_smul {α : Type*} (f : α → E3) (c : ℝ) (S : Set α) :
    oscOn (fun x => c • f x) S = |c| * oscOn f S := by
  have himg : (fun x => c • f x) '' S = c • (f '' S) := by
    rw [← Set.image_smul, ← Set.image_comp]; rfl
  rw [oscOn, oscOn, himg, diam_smul₀]
  simp [Real.norm_eq_abs]

/-- Reindexing the domain. -/
lemma oscOn_comp {α β : Type*} (f : α → E3) (g : β → α) (S : Set β) :
    oscOn (fun y => f (g y)) S = oscOn f (g '' S) := by
  rw [oscOn, oscOn, ← Set.image_comp]; rfl

/-! ## The blow-up rescaling -/

/-- The KNSŠ rescaling of a spatial field about `x₀` at velocity scale `M`:
`u_M(y) = M⁻¹ u(x₀ + M⁻¹ y)`. -/
def blowupSpace (u : E3 → E3) (M : ℝ) (x0 : E3) : E3 → E3 :=
  fun y => M⁻¹ • u (x0 + M⁻¹ • y)

/-- The rescaling maps the unit-scale ball onto the physical ball of radius
`R/M` about `x₀`. -/
lemma image_affine_ball {M : ℝ} (hM : 0 < M) (x0 : E3) (R : ℝ) :
    (fun y : E3 => x0 + M⁻¹ • y) '' Metric.ball 0 R = Metric.ball x0 (M⁻¹ * R) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : ‖y‖ < R := by simpa [dist_eq_norm] using hy
    have hn : ‖M⁻¹ • y‖ = M⁻¹ * ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, hn]
    exact mul_lt_mul_of_pos_left hy' (inv_pos.mpr hM)
  · intro hz
    have hz' : ‖z - x0‖ < M⁻¹ * R := by simpa [dist_eq_norm] using hz
    refine ⟨M • (z - x0), ?_, ?_⟩
    · have hnorm : ‖M • (z - x0)‖ = M * ‖z - x0‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hM]
      have hlt : M * ‖z - x0‖ < M * (M⁻¹ * R) := mul_lt_mul_of_pos_left hz' hM
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hM), one_mul] at hlt
      simpa [mem_ball, dist_eq_norm, hnorm] using hlt
    · show x0 + M⁻¹ • (M • (z - x0)) = z
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hM), one_smul]
      abel

/-- **The §2 identity.**  `osc_{B_R} u_M = M⁻¹ · osc_{B_{R/M}(x₀)} u`. -/
theorem oscOn_blowupSpace (u : E3 → E3) {M : ℝ} (hM : 0 < M) (x0 : E3) (R : ℝ) :
    oscOn (blowupSpace u M x0) (Metric.ball 0 R)
      = M⁻¹ * oscOn u (Metric.ball x0 (M⁻¹ * R)) := by
  have h1 : oscOn (blowupSpace u M x0) (Metric.ball 0 R)
      = |M⁻¹| * oscOn (fun y : E3 => u (x0 + M⁻¹ • y)) (Metric.ball 0 R) :=
    oscOn_smul _ _ _
  rw [h1, oscOn_comp u (fun y : E3 => x0 + M⁻¹ • y), image_affine_ball hM,
    abs_of_pos (inv_pos.mpr hM)]

/-- **R1 as an original-scale statement.**  A unit-scale oscillation defect `c`
for the rescaled field is *exactly* the physical inequality
`osc_{B_{R/M}(x₀)} u ≥ c·M`. -/
theorem oscOn_blowupSpace_ge_iff (u : E3 → E3) {M : ℝ} (hM : 0 < M) (x0 : E3) (R c : ℝ) :
    c ≤ oscOn (blowupSpace u M x0) (Metric.ball 0 R)
      ↔ c * M ≤ oscOn u (Metric.ball x0 (M⁻¹ * R)) := by
  rw [oscOn_blowupSpace u hM x0 R]
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hM)
    have hfix : M⁻¹ * oscOn u (Metric.ball x0 (M⁻¹ * R)) * M
        = oscOn u (Metric.ball x0 (M⁻¹ * R)) := by
      field_simp
    rwa [hfix] at hmul
  · intro h
    have := mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hM))
    calc c = M⁻¹ * (c * M) := by field_simp
      _ ≤ M⁻¹ * oscOn u (Metric.ball x0 (M⁻¹ * R)) := this

/-! ## Flat maxima (§3) -/

/-- The rescaled field at a point of the unit ball differs from its centre value
by at most the oscillation: this is what makes "flat" mean "locally constant". -/
lemma norm_blowup_sub_center_le (u : E3 → E3) (M : ℝ) (x0 : E3) {R : ℝ} (hR : 0 < R)
    {y : E3} (hy : y ∈ Metric.ball (0 : E3) R)
    (hb : Bornology.IsBounded (blowupSpace u M x0 '' Metric.ball (0 : E3) R)) :
    ‖blowupSpace u M x0 y - blowupSpace u M x0 0‖
      ≤ oscOn (blowupSpace u M x0) (Metric.ball 0 R) :=
  norm_sub_le_oscOn hb hy (by simpa using hR)

/-- The blow-up sequence `u_k` is *asymptotically flat at scale `R`* if the
rescaled oscillation on `B_R` tends to `0`. -/
def FlatMaxAt (u : ℕ → E3 → E3) (M : ℕ → ℝ) (x : ℕ → E3) (R : ℝ) : Prop :=
  Filter.Tendsto (fun k => oscOn (blowupSpace (u k) (M k) (x k)) (Metric.ball 0 R))
    Filter.atTop (nhds 0)

/-- **Flatness is exactly the failure of the physical oscillation bound (1).**
Being asymptotically flat at scale `R` is equivalent to
`osc_{B_{R/M_k}(x_k)} u_k / M_k → 0`. -/
theorem flatMax_iff (u : ℕ → E3 → E3) (M : ℕ → ℝ) (hM : ∀ k, 0 < M k) (x : ℕ → E3) (R : ℝ) :
    FlatMaxAt u M x R
      ↔ Filter.Tendsto
          (fun k => (M k)⁻¹ * oscOn (u k) (Metric.ball (x k) ((M k)⁻¹ * R)))
          Filter.atTop (nhds 0) := by
  unfold FlatMaxAt
  constructor <;> intro h
  · refine h.congr fun k => ?_
    exact oscOn_blowupSpace (u k) (hM k) (x k) R
  · refine h.congr fun k => ?_
    exact (oscOn_blowupSpace (u k) (hM k) (x k) R).symm

/-- On a flat maximum the rescaled fields converge to their own centre value,
uniformly on `B_R`: the limit is spatially constant there. -/
theorem tendsto_blowup_sub_center_of_flat (u : ℕ → E3 → E3) (M : ℕ → ℝ) (x : ℕ → E3)
    {R : ℝ} (hR : 0 < R) (hflat : FlatMaxAt u M x R)
    (hb : ∀ k, Bornology.IsBounded (blowupSpace (u k) (M k) (x k) '' Metric.ball (0 : E3) R))
    (y : ℕ → E3) (hy : ∀ k, y k ∈ Metric.ball (0 : E3) R) :
    Filter.Tendsto
      (fun k => ‖blowupSpace (u k) (M k) (x k) (y k) - blowupSpace (u k) (M k) (x k) 0‖)
      Filter.atTop (nhds 0) := by
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hflat
  exact norm_blowup_sub_center_le (u k) (M k) (x k) hR (hy k) (hb k)

/-! ## The derivative package (§4) -/

/-- **Mean value package.**  If `‖Df(x₀)e‖ ≥ A` for a unit vector `e`, and the
differential is `K`-Lipschitz on `B_r(x₀)`, then for every `0 < h < r`
the oscillation of `f` on `B_r(x₀)` is at least `hA − Kh²`. -/
theorem oscOn_ge_of_fderiv_lower (f : E3 → E3) (x0 e : E3) {r A K h : ℝ}
    (hf : Differentiable ℝ f) (he : ‖e‖ = 1)
    (hA : A ≤ ‖fderiv ℝ f x0 e‖) (hK : 0 ≤ K) (hh : 0 < h) (hhr : h < r)
    (hlip : ∀ z ∈ Metric.ball x0 r, ‖fderiv ℝ f z - fderiv ℝ f x0‖ ≤ K * ‖z - x0‖) :
    h * A - K * h ^ 2 ≤ oscOn f (Metric.ball x0 r) := by
  set y : E3 := x0 + h • e with hy
  have hnorm : ‖y - x0‖ = h := by
    simp [hy, norm_smul, he, abs_of_pos hh]
  -- the closed ball of radius `h` sits inside `B_r(x₀)`
  have hsub : Metric.closedBall x0 h ⊆ Metric.ball x0 r := by
    intro z hz
    exact Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hz) hhr)
  have hbound : ∀ z ∈ Metric.closedBall x0 h,
      ‖fderiv ℝ f z - fderiv ℝ f x0‖ ≤ K * h := by
    intro z hz
    have hz' : ‖z - x0‖ ≤ h := by simpa [dist_eq_norm] using Metric.mem_closedBall.1 hz
    exact le_trans (hlip z (hsub hz)) (mul_le_mul_of_nonneg_left hz' hK)
  have hx0mem : x0 ∈ Metric.closedBall x0 h := by simp [le_of_lt hh]
  have hymem : y ∈ Metric.closedBall x0 h := by
    simp [Metric.mem_closedBall, dist_eq_norm, hnorm]
  have hmv := (convex_closedBall x0 h).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ => hf z) hbound hx0mem hymem
  rw [hnorm] at hmv
  -- the linear term
  have hlin : fderiv ℝ f x0 (y - x0) = h • fderiv ℝ f x0 e := by
    have : y - x0 = h • e := by simp [hy]
    rw [this, map_smul]
  have hlinnorm : ‖fderiv ℝ f x0 (y - x0)‖ = h * ‖fderiv ℝ f x0 e‖ := by
    rw [hlin, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  have hlow : h * A - K * h ^ 2 ≤ ‖f y - f x0‖ := by
    set L := fderiv ℝ f x0 (y - x0) with hL
    set D := f y - f x0 with hD
    have h2 : ‖L‖ ≤ ‖D‖ + ‖D - L‖ := by
      calc ‖L‖ = ‖D - (D - L)‖ := by congr 1; abel
        _ ≤ ‖D‖ + ‖D - L‖ := norm_sub_le _ _
    have h3 : h * A ≤ ‖L‖ := by
      rw [hL, hlinnorm]
      exact mul_le_mul_of_nonneg_left hA (le_of_lt hh)
    have h4 : ‖D - L‖ ≤ K * h ^ 2 := by
      calc ‖D - L‖ ≤ K * h * h := hmv
        _ = K * h ^ 2 := by ring
    linarith
  -- both points are in the ball
  have hbdd : Bornology.IsBounded (f '' Metric.ball x0 r) := by
    have hcpt : IsCompact (f '' Metric.closedBall x0 r) :=
      (isCompact_closedBall x0 r).image hf.continuous
    exact hcpt.isBounded.subset (Set.image_mono Metric.ball_subset_closedBall)
  have hyb : y ∈ Metric.ball x0 r := hsub hymem
  have hx0b : x0 ∈ Metric.ball x0 r := Metric.mem_ball_self (lt_trans hh hhr)
  exact le_trans hlow (norm_sub_le_oscOn hbdd hyb hx0b)

/-- **R1-grad ⇒ R1-osc, with the scales matched.**  A gradient of size `c₁M²`
at the velocity maximum, together with a Hessian-type bound `C M³` on the ball
of radius `ρ/M`, produces a defect for the *rescaled* field which is
independent of `M`. -/
theorem oscOn_blowup_ge_of_gradient_defect (u : E3 → E3) (x0 e : E3) {M c1 C rho : ℝ}
    (hu : Differentiable ℝ u) (he : ‖e‖ = 1) (hM : 0 < M) (hc1 : 0 < c1) (hC : 0 < C)
    (hgrad : c1 * M ^ 2 ≤ ‖fderiv ℝ u x0 e‖)
    (hhess : ∀ z ∈ Metric.ball x0 (M⁻¹ * rho),
      ‖fderiv ℝ u z - fderiv ℝ u x0‖ ≤ C * M ^ 3 * ‖z - x0‖)
    (hrho : c1 / (2 * C) < rho) :
    c1 ^ 2 / (4 * C) ≤ oscOn (blowupSpace u M x0) (Metric.ball 0 rho) := by
  set h : ℝ := c1 / (2 * C * M) with hh
  have hMne : M ≠ 0 := ne_of_gt hM
  have hhpos : 0 < h := by
    apply div_pos hc1
    positivity
  have hhr : h < M⁻¹ * rho := by
    have : c1 / (2 * C) < rho := hrho
    rw [hh]
    rw [inv_mul_eq_div, lt_div_iff₀ hM]
    have hstep : c1 / (2 * C * M) * M = c1 / (2 * C) := by
      field_simp
    rw [hstep]
    exact this
  have hKnn : (0:ℝ) ≤ C * M ^ 3 := by positivity
  have hosc := oscOn_ge_of_fderiv_lower u x0 e hu he hgrad hKnn hhpos hhr hhess
  have hval : h * (c1 * M ^ 2) - C * M ^ 3 * h ^ 2 = c1 ^ 2 / (4 * C) * M := by
    rw [hh]; field_simp; ring
  rw [hval] at hosc
  rw [oscOn_blowupSpace u hM x0 rho]
  have := mul_le_mul_of_nonneg_left hosc (le_of_lt (inv_pos.mpr hM))
  calc c1 ^ 2 / (4 * C) = M⁻¹ * (c1 ^ 2 / (4 * C) * M) := by field_simp
    _ ≤ M⁻¹ * oscOn u (Metric.ball x0 (M⁻¹ * rho)) := this

/-! ## The derivative scaling audit (§4) -/

/-- The differential of the rescaled field: `∇u_M(y) = M⁻² ∇u(x₀ + M⁻¹y)`. -/
theorem fderiv_blowupSpace (u : E3 → E3) (M : ℝ) (hu : Differentiable ℝ u) (x0 y : E3) :
    fderiv ℝ (blowupSpace u M x0) y
      = (M⁻¹ * M⁻¹) • fderiv ℝ u (x0 + M⁻¹ • y) := by
  have hg : HasFDerivAt (fun y : E3 => x0 + M⁻¹ • y)
      (M⁻¹ • ContinuousLinearMap.id ℝ E3) y := by
    simpa using ((hasFDerivAt_id y).const_smul M⁻¹).const_add x0
  have hcomp : HasFDerivAt (fun y : E3 => u (x0 + M⁻¹ • y))
      ((fderiv ℝ u (x0 + M⁻¹ • y)).comp (M⁻¹ • ContinuousLinearMap.id ℝ E3)) y :=
    (hu _).hasFDerivAt.comp y hg
  have hfin : HasFDerivAt (blowupSpace u M x0)
      (M⁻¹ • ((fderiv ℝ u (x0 + M⁻¹ • y)).comp (M⁻¹ • ContinuousLinearMap.id ℝ E3))) y :=
    hcomp.const_smul M⁻¹
  rw [hfin.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp [ContinuousLinearMap.smul_apply, smul_smul]

/-- Hence the norm of the rescaled differential is `M⁻²` times the physical one. -/
theorem norm_fderiv_blowupSpace (u : E3 → E3) {M : ℝ} (hM : 0 < M)
    (hu : Differentiable ℝ u) (x0 y : E3) :
    ‖fderiv ℝ (blowupSpace u M x0) y‖ = (M ^ 2)⁻¹ * ‖fderiv ℝ u (x0 + M⁻¹ • y)‖ := by
  rw [fderiv_blowupSpace u M hu x0 y, norm_smul, Real.norm_eq_abs]
  have hpos : 0 < M⁻¹ * M⁻¹ := by positivity
  rw [abs_of_pos hpos]
  congr 1
  field_simp

/-- **The §4 scaling audit, stated exactly.**  A *derivative* normalization of the
rescaled field at the origin is available only at the price of a physical
gradient of size `M²`: `‖∇u_M(y)‖ ≥ 1` is equivalent to
`‖∇u(x₀ + M⁻¹y)‖ ≥ M²`.  (Contrast the oscillation, which by
`oscOn_blowupSpace` only needs `osc ≳ M`.) -/
theorem one_le_norm_fderiv_blowupSpace_iff (u : E3 → E3) {M : ℝ} (hM : 0 < M)
    (hu : Differentiable ℝ u) (x0 y : E3) :
    1 ≤ ‖fderiv ℝ (blowupSpace u M x0) y‖ ↔ M ^ 2 ≤ ‖fderiv ℝ u (x0 + M⁻¹ • y)‖ := by
  rw [norm_fderiv_blowupSpace u hM hu x0 y]
  have hM2 : (0:ℝ) < M ^ 2 := by positivity
  rw [le_inv_mul_iff₀ hM2, mul_one]

/-! ## Stability of the defect under uniform limits (target B) -/

/-- The oscillation is `2`-Lipschitz for the uniform distance:
`osc f ≤ osc g + 2 sup‖f − g‖`. -/
theorem oscOn_le_add_of_uniform_approx {alpha : Type*} {f g : alpha → E3} {S : Set alpha}
    {eps : ℝ} (heps : 0 ≤ eps) (hbg : Bornology.IsBounded (g '' S))
    (h : ∀ x ∈ S, ‖f x - g x‖ ≤ eps) :
    oscOn f S ≤ oscOn g S + 2 * eps := by
  refine Metric.diam_le_of_forall_dist_le (by have := oscOn_nonneg g S; linarith) ?_
  rintro p ⟨x, hx, rfl⟩ q ⟨y, hy, rfl⟩
  have hgxy : ‖g x - g y‖ ≤ oscOn g S := norm_sub_le_oscOn hbg hx hy
  have hsplit : f x - f y = (f x - g x) + (g x - g y) + (g y - f y) := by abel
  have : ‖f x - f y‖ ≤ ‖f x - g x‖ + ‖g x - g y‖ + ‖g y - f y‖ := by
    calc ‖f x - f y‖ = ‖(f x - g x) + (g x - g y) + (g y - f y)‖ := by rw [← hsplit]
      _ ≤ ‖(f x - g x) + (g x - g y)‖ + ‖g y - f y‖ := norm_add_le _ _
      _ ≤ ‖f x - g x‖ + ‖g x - g y‖ + ‖g y - f y‖ := by
          have := norm_add_le (f x - g x) (g x - g y); linarith
  have hy' : ‖g y - f y‖ ≤ eps := by
    have := h y hy
    simpa [norm_sub_rev] using this
  have hx' : ‖f x - g x‖ ≤ eps := h x hx
  simpa [dist_eq_norm] using (by linarith : ‖f x - f y‖ ≤ oscOn g S + 2 * eps)

/-- **Target B for the oscillation defect.**  A uniform-on-`S` limit of fields
each carrying a defect `c₀` carries the same defect.  (Uniform convergence on
the relevant compact set is exactly the topology in which the KNSŠ limit is
extracted.) -/
theorem oscOn_ge_of_uniform_limit {alpha : Type*} {u : ℕ → alpha → E3} {U : alpha → E3}
    {S : Set alpha} {c0 : ℝ} (hbU : Bornology.IsBounded (U '' S))
    (hconv : ∀ eps > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ x ∈ S, ‖u k x - U x‖ ≤ eps)
    (hdef : ∀ k, c0 ≤ oscOn (u k) S) :
    c0 ≤ oscOn U S := by
  refine le_of_forall_pos_le_add ?_
  intro d hd
  obtain ⟨N, hN⟩ := hconv (d / 2) (by linarith)
  have h1 : oscOn (u N) S ≤ oscOn U S + 2 * (d / 2) :=
    oscOn_le_add_of_uniform_approx (by linarith) hbU (hN N (le_refl N))
  have := hdef N
  linarith

/-! ## The expanding period of the rescaled fields (§8–§9) -/

/-- **The rescaled fields live on expanding lattices.**  If `u` is
`ℤ³`-periodic, then `u_M` is `Mℤ³`-periodic: its period is `M` times larger,
so its Fourier support lies on the lattice `(2π/M)ℤ³` and its Poincaré constant
`4π²/M²` tends to `0`.  This is the exact sense in which the KNSŠ rescaling
decompactifies the torus. -/
theorem blowupSpace_periodic (u : E3 → E3) {M : ℝ} (hM : 0 < M) (x0 : E3)
    (hper : ∀ (x : E3) (j : Fin 3), u (x + ee j) = u x) (y : E3) (j : Fin 3) :
    blowupSpace u M x0 (y + M • ee j) = blowupSpace u M x0 y := by
  have hstep : x0 + M⁻¹ • (y + M • ee j) = (x0 + M⁻¹ • y) + ee j := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt hM), one_smul]
    abel
  rw [blowupSpace, blowupSpace, hstep, hper]

end ClayNS
