/-
# The point-window `3 × 3` gate: three centres that separate three heights

The two-taper lane needed a *strictly positive* `2 × 2` cross determinant, because the
one-zero admission was formulated as a strict domination.  The two-zero lane needs less:
`ThreeTaperSchurCore.elim2_ne_zero_of_det3_ne_zero` only asks for a **nonzero** `3 × 3`
determinant.  That is decisive, because nonvanishing can be obtained without any total
positivity theory for `cosh`.

The point-window limit of the cross response of a unit-mass window at `c` against the
shared window at `c_p`, read at height `x`, is

    pointCross c_p c x = (3/4) (c² - c_p²) (cosh (x c) - cosh (x c_p)).

For three heights `0 < a₁ < a₂ < a₃` the determinant of the `3 × 3` matrix
`[pointCross c_p c_j a_i]` is, as a function of the last centre `c₂`, a combination

    α₀ + α₁ cosh(a₁ c₂) + α₂ cosh(a₂ c₂) + α₃ cosh(a₃ c₂)

whose top coefficient `α₃` is the previous `2 × 2` minor.  So one only has to choose the
centres greedily, each time invoking
`CoshCombinationSeparation.exists_gt_coshCombo_ne_zero`, which also delivers the
ordering `c_p < c₀ < c₁ < c₂` for free.

The result, `exists_centres_pointCrossDet_ne_zero`, is the point-window gate of the
two-zero lane: an actual ordered triple of window centres whose point-window response
matrix is nonsingular at three prescribed distinct positive heights.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.CoshCombinationSeparation
import Zeta23Bridge.ThreeTaperSchurCore

noncomputable section

open Filter Topology

namespace Zeta23Bridge
namespace ThreeWindowPointGate

open Zeta23Bridge.ThreeTaperSchurCore
open Zeta23Bridge.CoshCombinationSeparation

/-! ## The point-window responses -/

/-- The response difference of a unit point mass at `c` against one at `c_p`, at
height `a`. -/
def coshDiffAt (a cp c : ℝ) : ℝ := Real.cosh (a * c) - Real.cosh (a * cp)

/-- The point-window limit of the cross response `covForm p q a` for unit-mass windows
concentrated at `c_p` and `c`. -/
def pointCross (cp c a : ℝ) : ℝ := 3 / 4 * (c ^ 2 - cp ^ 2) * coshDiffAt a cp c

theorem coshDiffAt_pos {a cp c : ℝ} (ha : 0 < a) (hcp : 0 ≤ cp) (h : cp < c) :
    0 < coshDiffAt a cp c := by
  have habs : |a * cp| < |a * c| := by
    rw [abs_of_nonneg (mul_nonneg ha.le hcp),
      abs_of_nonneg (mul_nonneg ha.le (hcp.trans h.le))]
    exact mul_lt_mul_of_pos_left h ha
  have := Real.cosh_lt_cosh.mpr habs
  unfold coshDiffAt
  linarith

theorem det3_cons (u0 u1 u2 v0 v1 v2 w0 w1 w2 : ℝ) :
    det3 ![u0, u1, u2] ![v0, v1, v2] ![w0, w1, w2]
      = u0 * v1 * w2 - u0 * v2 * w1 - u1 * v0 * w2 + u1 * v2 * w0 + u2 * v0 * w1
        - u2 * v1 * w0 := by
  simp [det3]

/-! ## Greedy choice of the three centres -/

/-- **The point-window `3 × 3` gate.**  For three distinct positive heights and any
positive shared centre there is an ordered triple of window centres beyond it whose
point-window response matrix is nonsingular. -/
theorem exists_centres_coshDiffDet_ne_zero {a₁ a₂ a₃ cp : ℝ}
    (ha₁ : 0 < a₁) (h₁₂ : a₁ < a₂) (h₂₃ : a₂ < a₃) (hcp : 0 < cp) :
    ∃ c₀ c₁ c₂ : ℝ, cp < c₀ ∧ c₀ < c₁ ∧ c₁ < c₂ ∧
      det3 ![coshDiffAt a₁ cp c₀, coshDiffAt a₁ cp c₁, coshDiffAt a₁ cp c₂]
        ![coshDiffAt a₂ cp c₀, coshDiffAt a₂ cp c₁, coshDiffAt a₂ cp c₂]
        ![coshDiffAt a₃ cp c₀, coshDiffAt a₃ cp c₁, coshDiffAt a₃ cp c₂] ≠ 0 := by
  have ha₂ : 0 < a₂ := ha₁.trans h₁₂
  have ha₃ : 0 < a₃ := ha₂.trans h₂₃
  -- first centre: any point beyond `cp`
  set c₀ : ℝ := cp + 1 with hc₀def
  have hc₀ : cp < c₀ := by rw [hc₀def]; linarith
  have hm₁₀ : coshDiffAt a₁ cp c₀ ≠ 0 := ne_of_gt (coshDiffAt_pos ha₁ hcp.le hc₀)
  -- second centre: make the leading `2 × 2` minor nonzero
  obtain ⟨c₁, hc₁gt, hminor⟩ :=
    exists_gt_coshCombo_ne_zero (a₁ := a₁) (a₂ := a₂) (a₃ := a₃)
      (al0 := -(coshDiffAt a₁ cp c₀) * Real.cosh (a₂ * cp)
        + coshDiffAt a₂ cp c₀ * Real.cosh (a₁ * cp))
      (al1 := -(coshDiffAt a₂ cp c₀)) (al2 := coshDiffAt a₁ cp c₀) (al3 := 0)
      ha₁ h₁₂ h₂₃ (Or.inr (Or.inl hm₁₀)) c₀
  have hD₂ : coshDiffAt a₁ cp c₀ * coshDiffAt a₂ cp c₁
      - coshDiffAt a₁ cp c₁ * coshDiffAt a₂ cp c₀ ≠ 0 := by
    intro hzero
    apply hminor
    unfold coshDiffAt at hzero ⊢
    linear_combination hzero
  -- third centre: make the full `3 × 3` determinant nonzero
  obtain ⟨c₂, hc₂gt, hdet⟩ :=
    exists_gt_coshCombo_ne_zero (a₁ := a₁) (a₂ := a₂) (a₃ := a₃)
      (al0 := -((coshDiffAt a₂ cp c₀ * coshDiffAt a₃ cp c₁
            - coshDiffAt a₂ cp c₁ * coshDiffAt a₃ cp c₀) * Real.cosh (a₁ * cp))
          - (coshDiffAt a₁ cp c₁ * coshDiffAt a₃ cp c₀
            - coshDiffAt a₁ cp c₀ * coshDiffAt a₃ cp c₁) * Real.cosh (a₂ * cp)
          - (coshDiffAt a₁ cp c₀ * coshDiffAt a₂ cp c₁
            - coshDiffAt a₁ cp c₁ * coshDiffAt a₂ cp c₀) * Real.cosh (a₃ * cp))
      (al1 := coshDiffAt a₂ cp c₀ * coshDiffAt a₃ cp c₁
        - coshDiffAt a₂ cp c₁ * coshDiffAt a₃ cp c₀)
      (al2 := coshDiffAt a₁ cp c₁ * coshDiffAt a₃ cp c₀
        - coshDiffAt a₁ cp c₀ * coshDiffAt a₃ cp c₁)
      (al3 := coshDiffAt a₁ cp c₀ * coshDiffAt a₂ cp c₁
        - coshDiffAt a₁ cp c₁ * coshDiffAt a₂ cp c₀)
      ha₁ h₁₂ h₂₃ (Or.inr (Or.inr hD₂)) c₁
  refine ⟨c₀, c₁, c₂, hc₀, hc₁gt, hc₂gt, ?_⟩
  rw [det3_cons]
  intro hzero
  apply hdet
  unfold coshDiffAt at hzero ⊢
  linear_combination hzero

/-- The same gate for the point-window cross responses themselves: the geometric column
factors `(3/4)(c_j² − c_p²)` are nonzero, so they do not affect nonsingularity. -/
theorem exists_centres_pointCrossDet_ne_zero {a₁ a₂ a₃ cp : ℝ}
    (ha₁ : 0 < a₁) (h₁₂ : a₁ < a₂) (h₂₃ : a₂ < a₃) (hcp : 0 < cp) :
    ∃ c₀ c₁ c₂ : ℝ, cp < c₀ ∧ c₀ < c₁ ∧ c₁ < c₂ ∧
      det3 ![pointCross cp c₀ a₁, pointCross cp c₁ a₁, pointCross cp c₂ a₁]
        ![pointCross cp c₀ a₂, pointCross cp c₁ a₂, pointCross cp c₂ a₂]
        ![pointCross cp c₀ a₃, pointCross cp c₁ a₃, pointCross cp c₂ a₃] ≠ 0 := by
  obtain ⟨c₀, c₁, c₂, h₀, h₁, h₂, hdet⟩ :=
    exists_centres_coshDiffDet_ne_zero ha₁ h₁₂ h₂₃ hcp
  refine ⟨c₀, c₁, c₂, h₀, h₁, h₂, ?_⟩
  have hk₀ : (3:ℝ) / 4 * (c₀ ^ 2 - cp ^ 2) ≠ 0 := by
    have : cp ^ 2 < c₀ ^ 2 := by nlinarith
    intro h; nlinarith [h]
  have hk₁ : (3:ℝ) / 4 * (c₁ ^ 2 - cp ^ 2) ≠ 0 := by
    have : cp ^ 2 < c₁ ^ 2 := by nlinarith
    intro h; nlinarith [h]
  have hk₂ : (3:ℝ) / 4 * (c₂ ^ 2 - cp ^ 2) ≠ 0 := by
    have : cp ^ 2 < c₂ ^ 2 := by nlinarith
    intro h; nlinarith [h]
  rw [det3_cons] at hdet ⊢
  unfold pointCross
  intro hzero
  apply hdet
  have hfac : (3 / 4 * (c₀ ^ 2 - cp ^ 2)) * ((3 / 4 * (c₁ ^ 2 - cp ^ 2))
      * ((3 / 4 * (c₂ ^ 2 - cp ^ 2))
        * (coshDiffAt a₁ cp c₀ * coshDiffAt a₂ cp c₁ * coshDiffAt a₃ cp c₂
          - coshDiffAt a₁ cp c₀ * coshDiffAt a₂ cp c₂ * coshDiffAt a₃ cp c₁
          - coshDiffAt a₁ cp c₁ * coshDiffAt a₂ cp c₀ * coshDiffAt a₃ cp c₂
          + coshDiffAt a₁ cp c₁ * coshDiffAt a₂ cp c₂ * coshDiffAt a₃ cp c₀
          + coshDiffAt a₁ cp c₂ * coshDiffAt a₂ cp c₀ * coshDiffAt a₃ cp c₁
          - coshDiffAt a₁ cp c₂ * coshDiffAt a₂ cp c₁ * coshDiffAt a₃ cp c₀))) = 0 := by
    linear_combination hzero
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd h hk₀
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' hk₁
  rcases mul_eq_zero.mp h' with h'' | h''
  · exact absurd h'' hk₂
  · linear_combination h''

end ThreeWindowPointGate
end Zeta23Bridge
