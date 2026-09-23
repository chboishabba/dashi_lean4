/-
# §10 of the BIDI note: Cauchy extraction of the mixed source derivative

R402 turns a *pointwise absolute* bound for the source-domain function into a
bound for its mixed second derivative at the centre of the selected polydisc.
Both forms used in the note are proved here from Mathlib's Cauchy estimate, with
no further hypotheses than holomorphy on the polydisc and the sup bound on its
distinguished boundary.

* `norm_mixed_deriv_le` — the two-source form: if `y ↦ F x y` is holomorphic on
  the disc of radius `r` for every `x` in the closed disc of radius `r`, if
  `‖F‖ ≤ M` there, and if the first source derivative
  `x ↦ ∂_y F(x, c_R)` is itself holomorphic on the disc, then

      ‖∂_x ∂_y F (c_L, c_R)‖ ≤ M / r / r.

* `norm_polarized_mixed_le` — the polarised one-parameter form, which needs no
  holomorphy hypothesis beyond that of the two diagonal restrictions
  `h± (z) = log Z(z·(J_L ± J_R))`:

      ‖¼ (h₊''(0) − h₋''(0))‖ ≤ M / r².

  This is the form used by the assembled chain, because the polarisation
  identity `D_L D_R = ¼(D₊² − D₋²)` is exactly how the two-source mixed
  derivative is presented by the normalised source calculus.

`cauchyConst r = r⁻²` is the constant `C_Cauchy` of equation (31).
-/
import Mathlib

namespace RequestProject.YangMills.BIDI

open Metric

/-- The Cauchy constant of equation (31) for a polydisc of radius `r`. -/
noncomputable def cauchyConst (r : ℝ) : ℝ := 1 / r ^ 2

theorem cauchyConst_pos {r : ℝ} (hr : 0 < r) : 0 < cauchyConst r := by
  have : (0:ℝ) < r ^ 2 := by positivity
  simpa [cauchyConst] using (one_div_pos.mpr this)

/-- **Two-source Cauchy extraction.** -/
theorem norm_mixed_deriv_le {F : ℂ → ℂ → ℂ} {cL cR : ℂ} {r M : ℝ} (hr : 0 < r)
    (hslice : ∀ x ∈ closedBall cL r, DiffContOnCl ℂ (fun y => F x y) (ball cR r))
    (hbound : ∀ x ∈ closedBall cL r, ∀ y ∈ sphere cR r, ‖F x y‖ ≤ M)
    (houter : DiffContOnCl ℂ (fun x => deriv (fun y => F x y) cR) (ball cL r)) :
    ‖deriv (fun x => deriv (fun y => F x y) cR) cL‖ ≤ M / r / r := by
  have hinner : ∀ x ∈ sphere cL r, ‖deriv (fun y => F x y) cR‖ ≤ M / r := by
    intro x hx
    have hx' : x ∈ closedBall cL r := sphere_subset_closedBall hx
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr (hslice x hx')
      (hbound x hx')
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr houter hinner

/-- The same estimate written with the Cauchy constant of (31). -/
theorem norm_mixed_deriv_le_cauchyConst {F : ℂ → ℂ → ℂ} {cL cR : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hslice : ∀ x ∈ closedBall cL r, DiffContOnCl ℂ (fun y => F x y) (ball cR r))
    (hbound : ∀ x ∈ closedBall cL r, ∀ y ∈ sphere cR r, ‖F x y‖ ≤ M)
    (houter : DiffContOnCl ℂ (fun x => deriv (fun y => F x y) cR) (ball cL r)) :
    ‖deriv (fun x => deriv (fun y => F x y) cR) cL‖ ≤ cauchyConst r * M := by
  have h := norm_mixed_deriv_le hr hslice hbound houter
  have hne : r ≠ 0 := ne_of_gt hr
  have : M / r / r = cauchyConst r * M := by
    unfold cauchyConst
    field_simp
  rwa [this] at h

/-- The polarised mixed derivative: `¼ (h₊''(0) − h₋''(0))`. -/
noncomputable def polarizedMixed (hp hm : ℂ → ℂ) : ℂ :=
  (1 / 4) * (iteratedDeriv 2 hp 0 - iteratedDeriv 2 hm 0)

/-- **Polarised Cauchy extraction**, the one-parameter form of (31). -/
theorem norm_polarized_mixed_le {hp hm : ℂ → ℂ} {r M : ℝ} (hr : 0 < r)
    (hhp : DiffContOnCl ℂ hp (ball 0 r)) (hhm : DiffContOnCl ℂ hm (ball 0 r))
    (hbp : ∀ z ∈ sphere (0 : ℂ) r, ‖hp z‖ ≤ M)
    (hbm : ∀ z ∈ sphere (0 : ℂ) r, ‖hm z‖ ≤ M) :
    ‖polarizedMixed hp hm‖ ≤ cauchyConst r * M := by
  have h2p : ‖iteratedDeriv 2 hp 0‖ ≤ 2 * M / r ^ 2 := by
    have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hr hhp hbp
    simpa using this
  have h2m : ‖iteratedDeriv 2 hm 0‖ ≤ 2 * M / r ^ 2 := by
    have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hr hhm hbm
    simpa using this
  have hsub : ‖iteratedDeriv 2 hp 0 - iteratedDeriv 2 hm 0‖ ≤ 4 * M / r ^ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    have := add_le_add h2p h2m
    calc ‖iteratedDeriv 2 hp 0‖ + ‖iteratedDeriv 2 hm 0‖
        ≤ 2 * M / r ^ 2 + 2 * M / r ^ 2 := this
      _ = 4 * M / r ^ 2 := by ring
  have hr2 : (0:ℝ) < r ^ 2 := by positivity
  calc ‖polarizedMixed hp hm‖
      = (1 / 4) * ‖iteratedDeriv 2 hp 0 - iteratedDeriv 2 hm 0‖ := by
        rw [polarizedMixed, norm_mul]
        norm_num
    _ ≤ (1 / 4) * (4 * M / r ^ 2) := by
        exact mul_le_mul_of_nonneg_left hsub (by norm_num)
    _ = cauchyConst r * M := by
        have hne : r ≠ 0 := ne_of_gt hr
        unfold cauchyConst
        field_simp

end RequestProject.YangMills.BIDI
