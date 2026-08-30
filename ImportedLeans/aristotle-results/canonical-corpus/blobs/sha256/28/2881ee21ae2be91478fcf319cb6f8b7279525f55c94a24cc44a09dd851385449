/-
# A literal near/far decomposition in Gaussian similarity variables

`GaussianSimilarityInteractionClosure.lean` consumes a decomposition

  `N = N_near + N_far + N_marg`

of the physical interaction `N = (V·∇)V + ∇P` with (A-near) a *relative*
contraction and (A-far) a tail.  This file supplies a **literal** such
decomposition, in the variable in which the similarity problem is actually
posed: the spatial scale `R` of the Gaussian similarity variable `y`,

  `N_near = 1_{|y| ≤ R}·N`,   `N_far = 1_{|y| > R}·N`.

The point of this splitting is that the Gaussian weight itself pays for the far
part.  For `|y| ≥ R`,

  `ρ_ν(y) = e^{−|y|²/(4ν)} ≤ e^{−R²/(8ν)}·e^{−|y|²/(8ν)} = e^{−R²/(8ν)}ρ_{2ν}(y)`,

so the whole far interaction is exponentially small in the cutoff, measured
against a *fixed* second-Gaussian moment of the interaction.  That is a proof,
not an assumption: it is `ClayNS.gauss_far_pairing_tail_bound` below.  The near
part, by contrast, is where the physics sits: the estimate reduces to the
pointwise near-field domination `‖N(y)‖ ≤ η‖W_⊥(y)‖` on `|y| ≤ R`, which is
exactly the remaining research content of (A-near).

## Results

* `ClayNS.gaussNear`, `ClayNS.gaussFar`, `ClayNS.gaussNear_add_gaussFar` — the
  literal decomposition, exact by construction;
* `ClayNS.gaussWeight_le_tail` — the pointwise Gaussian tail domination
  `ρ_ν ≤ e^{−R²/(8ν)}ρ_{2ν}` on `|y| ≥ R`;
* `ClayNS.gauss_far_pairing_tail_bound` — **(A-far), proved**: the far pairing
  is at most `e^{−R²/(8ν)}·∫ρ_{2ν}‖N‖‖W‖`;
* `ClayNS.gauss_far_sq_tail_bound` — the same for the weighted `L²` norm of the
  far part;
* `ClayNS.gauss_near_pairing_relative` — **(A-near) reduced to a pointwise
  near-field bound**: if `‖N‖ ≤ η‖W_⊥‖` pointwise on the near field, the near
  pairing is `≤ η·∫ρ_ν‖W_⊥‖²`, i.e. a relative contraction of the transverse
  expenditure;
* `ClayNS.gauss_nearfar_interaction_bound` — the two together: the full
  interaction obeys `|⟪N,W_⊥⟫_ρ| ≤ η‖W_⊥‖²_ρ + e^{−R²/(8ν)}·M`, the shape the
  closure consumes, with the cutoff `R` free to be optimized.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianMarginalChannel

open MeasureTheory Set
open RealInnerProductSpace

noncomputable section

namespace ClayNS

/-! ## The literal splitting -/

/-- The near field of `N` at cutoff `R`: `1_{|y| ≤ R}·N`. -/
def gaussNear (R : ℝ) (N : E3 → E3) (y : E3) : E3 := if ‖y‖ ≤ R then N y else 0

/-- The far field of `N` at cutoff `R`: `1_{|y| > R}·N`. -/
def gaussFar (R : ℝ) (N : E3 → E3) (y : E3) : E3 := if ‖y‖ ≤ R then 0 else N y

/-- The decomposition is exact by construction. -/
@[simp] lemma gaussNear_add_gaussFar (R : ℝ) (N : E3 → E3) (y : E3) :
    gaussNear R N y + gaussFar R N y = N y := by
  unfold gaussNear gaussFar
  by_cases h : ‖y‖ ≤ R <;> simp [h]

/-! ## The Gaussian weight pays for the far field -/

/-- **The Gaussian tail domination.**  On `|y| ≥ R ≥ 0`,

  `ρ_ν(y) ≤ e^{−R²/(8ν)}·ρ_{2ν}(y)`.

Half of the Gaussian exponent is spent on the cutoff, the other half is kept as
a fixed, `R`-independent weight. -/
lemma gaussWeight_le_tail {nu R : ℝ} (hnu : 0 < nu) (hR : 0 ≤ R) {y : E3}
    (hy : R ≤ ‖y‖) :
    gaussWeight nu y ≤ Real.exp (-(R ^ 2) / (8 * nu)) * gaussWeight (2 * nu) y := by
  have hsq : R ^ 2 ≤ ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
  have hmul : Real.exp (-(R ^ 2) / (8 * nu)) * gaussWeight (2 * nu) y
      = Real.exp (-(R ^ 2) / (8 * nu) + -(‖y‖ ^ 2) / (4 * (2 * nu))) := by
    rw [gaussWeight, ← Real.exp_add]
  rw [gaussWeight, hmul, Real.exp_le_exp, ← sub_nonneg]
  have hne : (nu : ℝ) ≠ 0 := ne_of_gt hnu
  have key : -(R ^ 2) / (8 * nu) + -(‖y‖ ^ 2) / (4 * (2 * nu)) - -(‖y‖ ^ 2) / (4 * nu)
      = (‖y‖ ^ 2 - R ^ 2) / (8 * nu) := by
    field_simp
    ring
  rw [key]
  exact div_nonneg (by linarith) (by linarith)

/-- **(A-far), proved.**  The far part of the interaction is exponentially small
in the cutoff, measured against the fixed second-Gaussian moment
`∫ρ_{2ν}‖N‖‖W‖`. -/
theorem gauss_far_pairing_tail_bound {nu R : ℝ} (hnu : 0 < nu) (hR : 0 ≤ R)
    (N W : E3 → E3)
    (hint : Integrable (fun y : E3 => gaussWeight (2 * nu) y * (‖N y‖ * ‖W y‖))) :
    |∫ y : E3, gaussWeight nu y * ⟪gaussFar R N y, W y⟫|
      ≤ Real.exp (-(R ^ 2) / (8 * nu))
        * ∫ y : E3, gaussWeight (2 * nu) y * (‖N y‖ * ‖W y‖) := by
  have hg : Integrable (fun y : E3 => Real.exp (-(R ^ 2) / (8 * nu))
      * (gaussWeight (2 * nu) y * (‖N y‖ * ‖W y‖))) := hint.const_mul _
  have hbound : ∀ y : E3, ‖gaussWeight nu y * ⟪gaussFar R N y, W y⟫‖
      ≤ Real.exp (-(R ^ 2) / (8 * nu)) * (gaussWeight (2 * nu) y * (‖N y‖ * ‖W y‖)) := by
    intro y
    have hrhs : 0 ≤ Real.exp (-(R ^ 2) / (8 * nu))
        * (gaussWeight (2 * nu) y * (‖N y‖ * ‖W y‖)) := by
      have := (gaussWeight_pos (2 * nu) y).le
      have h1 := Real.exp_pos (-(R ^ 2) / (8 * nu))
      positivity
    by_cases h : ‖y‖ ≤ R
    · simp [gaussFar, h, hrhs]
    · have hy : R ≤ ‖y‖ := le_of_lt (lt_of_not_ge h)
      have hcs : |(⟪N y, W y⟫ : ℝ)| ≤ ‖N y‖ * ‖W y‖ := abs_real_inner_le_norm _ _
      have hw := gaussWeight_le_tail hnu hR hy
      have hwpos := (gaussWeight_pos nu y).le
      have hprod : gaussWeight nu y * |(⟪N y, W y⟫ : ℝ)|
          ≤ (Real.exp (-(R ^ 2) / (8 * nu)) * gaussWeight (2 * nu) y)
            * (‖N y‖ * ‖W y‖) := by
        have h1 : gaussWeight nu y * |(⟪N y, W y⟫ : ℝ)|
            ≤ gaussWeight nu y * (‖N y‖ * ‖W y‖) :=
          mul_le_mul_of_nonneg_left hcs hwpos
        have h2 : gaussWeight nu y * (‖N y‖ * ‖W y‖)
            ≤ (Real.exp (-(R ^ 2) / (8 * nu)) * gaussWeight (2 * nu) y)
              * (‖N y‖ * ‖W y‖) :=
          mul_le_mul_of_nonneg_right hw (by positivity)
        linarith
      simp only [gaussFar, h, if_false, Real.norm_eq_abs, abs_mul, abs_of_nonneg hwpos]
      calc gaussWeight nu y * |(⟪N y, W y⟫ : ℝ)|
          ≤ (Real.exp (-(R ^ 2) / (8 * nu)) * gaussWeight (2 * nu) y)
            * (‖N y‖ * ‖W y‖) := hprod
        _ = Real.exp (-(R ^ 2) / (8 * nu))
            * (gaussWeight (2 * nu) y * (‖N y‖ * ‖W y‖)) := by ring
  have hle := norm_integral_le_of_norm_le hg
    (Filter.Eventually.of_forall hbound)
  rw [integral_const_mul] at hle
  simpa [Real.norm_eq_abs] using hle

/-- The weighted `L²` version of the tail bound: the far part of the
interaction has exponentially small Gaussian energy. -/
theorem gauss_far_sq_tail_bound {nu R : ℝ} (hnu : 0 < nu) (hR : 0 ≤ R)
    (N : E3 → E3)
    (hint : Integrable (fun y : E3 => gaussWeight (2 * nu) y * ‖N y‖ ^ 2)) :
    ∫ y : E3, gaussWeight nu y * ‖gaussFar R N y‖ ^ 2
      ≤ Real.exp (-(R ^ 2) / (8 * nu))
        * ∫ y : E3, gaussWeight (2 * nu) y * ‖N y‖ ^ 2 := by
  have hg : Integrable (fun y : E3 => Real.exp (-(R ^ 2) / (8 * nu))
      * (gaussWeight (2 * nu) y * ‖N y‖ ^ 2)) := hint.const_mul _
  have hbound : ∀ y : E3, gaussWeight nu y * ‖gaussFar R N y‖ ^ 2
      ≤ Real.exp (-(R ^ 2) / (8 * nu)) * (gaussWeight (2 * nu) y * ‖N y‖ ^ 2) := by
    intro y
    have hrhs : 0 ≤ Real.exp (-(R ^ 2) / (8 * nu)) * (gaussWeight (2 * nu) y * ‖N y‖ ^ 2) := by
      have := (gaussWeight_pos (2 * nu) y).le
      have h1 := Real.exp_pos (-(R ^ 2) / (8 * nu))
      positivity
    by_cases h : ‖y‖ ≤ R
    · simp [gaussFar, h, hrhs]
    · have hy : R ≤ ‖y‖ := le_of_lt (lt_of_not_ge h)
      have hw := gaussWeight_le_tail hnu hR hy
      have hsq : (0 : ℝ) ≤ ‖N y‖ ^ 2 := sq_nonneg _
      have := mul_le_mul_of_nonneg_right hw hsq
      simp only [gaussFar, h, if_false]
      calc gaussWeight nu y * ‖N y‖ ^ 2
          ≤ (Real.exp (-(R ^ 2) / (8 * nu)) * gaussWeight (2 * nu) y) * ‖N y‖ ^ 2 := this
        _ = Real.exp (-(R ^ 2) / (8 * nu)) * (gaussWeight (2 * nu) y * ‖N y‖ ^ 2) := by ring
  have := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun y : E3 => by
      have := (gaussWeight_pos nu y).le
      positivity))
    hg (Filter.Eventually.of_forall hbound)
  rwa [integral_const_mul] at this

/-! ## The near field: (A-near) reduces to a pointwise domination -/

/-- **(A-near) from a pointwise near-field bound.**  If on the near field the
interaction is dominated by the transverse velocity of the profile,

  `‖N(y)‖ ≤ η‖W_⊥(y)‖`  for `|y| ≤ R`,

then the near pairing is a **relative contraction** of the transverse
expenditure:

  `|∫ρ_ν⟪N_near, W_⊥⟫| ≤ η·∫ρ_ν‖W_⊥‖²`.

This is the precise reduction of the remaining physical content of (A-near) to
a pointwise statement about the near field. -/
theorem gauss_near_pairing_relative {nu R eta : ℝ} (heta : 0 ≤ eta)
    (N Wp : E3 → E3)
    (hdom : ∀ y : E3, ‖y‖ ≤ R → ‖N y‖ ≤ eta * ‖Wp y‖)
    (hint : Integrable (fun y : E3 => gaussWeight nu y * ‖Wp y‖ ^ 2)) :
    |∫ y : E3, gaussWeight nu y * ⟪gaussNear R N y, Wp y⟫|
      ≤ eta * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2 := by
  have hg : Integrable (fun y : E3 => eta * (gaussWeight nu y * ‖Wp y‖ ^ 2)) :=
    hint.const_mul _
  have hbound : ∀ y : E3, ‖gaussWeight nu y * ⟪gaussNear R N y, Wp y⟫‖
      ≤ eta * (gaussWeight nu y * ‖Wp y‖ ^ 2) := by
    intro y
    have hwpos := (gaussWeight_pos nu y).le
    by_cases h : ‖y‖ ≤ R
    · have hcs : |(⟪N y, Wp y⟫ : ℝ)| ≤ ‖N y‖ * ‖Wp y‖ := abs_real_inner_le_norm _ _
      have hd := hdom y h
      have hstep : ‖N y‖ * ‖Wp y‖ ≤ eta * ‖Wp y‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_right hd (norm_nonneg (Wp y))
        nlinarith [norm_nonneg (Wp y)]
      simp only [gaussNear, h, if_true, Real.norm_eq_abs, abs_mul, abs_of_nonneg hwpos]
      calc gaussWeight nu y * |(⟪N y, Wp y⟫ : ℝ)|
          ≤ gaussWeight nu y * (eta * ‖Wp y‖ ^ 2) := by
            have : |(⟪N y, Wp y⟫ : ℝ)| ≤ eta * ‖Wp y‖ ^ 2 := le_trans hcs hstep
            exact mul_le_mul_of_nonneg_left this hwpos
        _ = eta * (gaussWeight nu y * ‖Wp y‖ ^ 2) := by ring
    · have hrhs : 0 ≤ eta * (gaussWeight nu y * ‖Wp y‖ ^ 2) := by positivity
      simp [gaussNear, h, hrhs]
  have hle := norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hbound)
  rw [integral_const_mul] at hle
  simpa [Real.norm_eq_abs] using hle

/-! ## The two facets together -/

/-- **The near/far interaction bound.**  With the literal cutoff decomposition,
a pointwise near-field domination and a finite second-Gaussian moment, the full
interaction obeys

  `|⟪N, W_⊥⟫_ρ| ≤ η·‖W_⊥‖²_ρ + e^{−R²/(8ν)}·M`,

with `M = ∫ρ_{2ν}‖N‖‖W_⊥‖` and the cutoff `R` free.  This is exactly the pair
of inputs (A-near) and (A-far) that
`ClayNS.gaussian_similarity_interaction_closure` consumes; only the pointwise
near-field constant `η` remains physical. -/
theorem gauss_nearfar_interaction_bound {nu R eta : ℝ} (hnu : 0 < nu) (hR : 0 ≤ R)
    (heta : 0 ≤ eta) (N Wp : E3 → E3)
    (hdom : ∀ y : E3, ‖y‖ ≤ R → ‖N y‖ ≤ eta * ‖Wp y‖)
    (hintW : Integrable (fun y : E3 => gaussWeight nu y * ‖Wp y‖ ^ 2))
    (hintM : Integrable (fun y : E3 => gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖)))
    (hnearInt : Integrable (fun y : E3 => gaussWeight nu y * ⟪gaussNear R N y, Wp y⟫))
    (hfarInt : Integrable (fun y : E3 => gaussWeight nu y * ⟪gaussFar R N y, Wp y⟫)) :
    |∫ y : E3, gaussWeight nu y * ⟪N y, Wp y⟫|
      ≤ eta * (∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2)
        + Real.exp (-(R ^ 2) / (8 * nu))
          * ∫ y : E3, gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖) := by
  have hsplit : (∫ y : E3, gaussWeight nu y * ⟪N y, Wp y⟫)
      = (∫ y : E3, gaussWeight nu y * ⟪gaussNear R N y, Wp y⟫)
        + ∫ y : E3, gaussWeight nu y * ⟪gaussFar R N y, Wp y⟫ := by
    rw [← integral_add hnearInt hfarInt]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have : (⟪N y, Wp y⟫ : ℝ)
        = ⟪gaussNear R N y, Wp y⟫ + ⟪gaussFar R N y, Wp y⟫ := by
      rw [← inner_add_left, gaussNear_add_gaussFar]
    dsimp only
    rw [this]
    ring
  have hnear := gauss_near_pairing_relative (nu := nu) heta N Wp hdom hintW
  have hfar := gauss_far_pairing_tail_bound hnu hR N Wp hintM
  calc |∫ y : E3, gaussWeight nu y * ⟪N y, Wp y⟫|
      = |(∫ y : E3, gaussWeight nu y * ⟪gaussNear R N y, Wp y⟫)
          + ∫ y : E3, gaussWeight nu y * ⟪gaussFar R N y, Wp y⟫| := by rw [hsplit]
    _ ≤ |∫ y : E3, gaussWeight nu y * ⟪gaussNear R N y, Wp y⟫|
          + |∫ y : E3, gaussWeight nu y * ⟪gaussFar R N y, Wp y⟫| := abs_add_le _ _
    _ ≤ eta * (∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2)
          + Real.exp (-(R ^ 2) / (8 * nu))
            * ∫ y : E3, gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖) := by
        linarith

end ClayNS
