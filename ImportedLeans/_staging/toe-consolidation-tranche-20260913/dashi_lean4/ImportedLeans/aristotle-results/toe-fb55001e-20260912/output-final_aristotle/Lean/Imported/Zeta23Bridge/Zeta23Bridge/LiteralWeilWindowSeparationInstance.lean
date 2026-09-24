/-
# Non-vacuity of the localized-window separation

`LiteralWeilWindowRatioSeparation` proves that three **window tapers** with ordered
modulus windows and the four-endpoint gate satisfy the strict cross-determinant
separation

    covForm p q₁ a * covForm p q₀ b  <  covForm p q₀ a * covForm p q₁ b.

That theorem would be worthless if no such configuration existed.  This module
closes that gap constructively:

* `exists_windowTaper` builds an explicit tent taper supported in any prescribed
  modulus window `lo ≤ |u| ≤ hi` with `0 < lo < hi`, continuous, compactly
  supported, nonnegative and of strictly positive mass;
* `exists_gate_radius` shows the four-endpoint gate holds for all sufficiently
  narrow symmetric windows around three ordered centres, by continuity from the
  degenerate (point-window) gate, which is a theorem;
* `exists_separated_window_tapers` combines the two: for **any** two heights
  `0 < a < b` and **any** three ordered centres `0 < c₀ < c₁ < c₂` there really are
  three window tapers realising the strict separation.

Nothing here is numerical: the radius is produced by an openness argument, not by
an estimate on a computed quantity.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilWindowRatioSeparation

noncomputable section

open scoped Real
open MeasureTheory Set

namespace Zeta23Bridge
namespace LiteralWeilWindowSeparationInstance

open LiteralWeilWindowRatioSeparation CoshWindowSeparation
  LiteralWeilLeadingCoefficientCovariance

/-! ## An explicit taper for a prescribed modulus window -/

/-- The tent taper of a window: `max 0 (d - ||u| - c|)` with centre `c` and radius
`d`. -/
def tentTaper (lo hi : ℝ) : ℝ → ℝ :=
  fun u => max 0 ((hi - lo) / 2 - |(|u| - (lo + hi) / 2)|)

/-- **Window tapers exist.**  Every nondegenerate modulus window carries an explicit
continuous, compactly supported, nonnegative taper of positive mass. -/
theorem exists_windowTaper {lo hi : ℝ} (hlo : 0 < lo) (hh : lo < hi) :
    WindowTaper (tentTaper lo hi) lo hi := by
  set c : ℝ := (lo + hi) / 2 with hc
  set d : ℝ := (hi - lo) / 2 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  have hcpos : 0 ≤ c := by rw [hc]; linarith
  have hf : tentTaper lo hi = fun u => max 0 (d - |(|u| - c)|) := rfl
  have hcont : Continuous (tentTaper lo hi) := by rw [hf]; fun_prop
  have hvanish : ∀ x : ℝ, x ∉ Icc (-hi) hi → tentTaper lo hi x = 0 := by
    intro x hx
    simp only [mem_Icc, not_and_or, not_le] at hx
    have hxa : hi < |x| := by
      rcases hx with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · exact lt_of_lt_of_le h (le_abs_self x)
    have hb : d < |(|x| - c)| := by
      rw [abs_of_nonneg (by rw [hc]; linarith)]
      rw [hc, hd]; linarith
    rw [hf]
    simp only [max_eq_left_iff]
    linarith
  have hcpt : HasCompactSupport (tentTaper lo hi) :=
    HasCompactSupport.intro (isCompact_Icc (a := -hi) (b := hi)) hvanish
  refine ⟨hcont, hcpt, fun u => le_max_left _ _, ?_, ?_⟩
  · intro u hu
    rw [hf] at hu
    have hposu : 0 < max 0 (d - |(|u| - c)|) :=
      lt_of_le_of_ne (le_max_left _ _) (Ne.symm hu)
    have h1 : 0 < d - |(|u| - c)| := by
      rcases lt_max_iff.mp hposu with h | h
      · exact absurd h (lt_irrefl 0)
      · exact h
    have h2 : |(|u| - c)| < d := by linarith
    rw [abs_lt] at h2
    constructor
    · rw [hc, hd] at h2; linarith [h2.1]
    · rw [hc, hd] at h2; linarith [h2.2]
  · rw [hf]
    refine MeasureTheory.integral_pos_of_integrable_nonneg_nonzero (x := c)
      (by fun_prop) ?_ (fun u => le_max_left _ _) ?_
    · rw [← hf]; exact hcont.integrable_of_hasCompactSupport hcpt
    · simp only [abs_of_nonneg hcpos, sub_self, abs_zero, sub_zero]
      simp [hdpos.le, hdpos.ne']

/-! ## The gate holds for all sufficiently narrow windows -/

/-- The gate defect of the symmetric windows of radius `e` around `c₀ < c₁ < c₂`. -/
def gateDefect (a b c0 c1 c2 e : ℝ) : ℝ :=
  coshDiff b (c0 - e) (c2 - e) * coshDiff a (c0 + e) (c1 + e)
    - coshDiff b (c0 + e) (c1 + e) * coshDiff a (c0 - e) (c2 - e)

theorem continuous_gateDefect (a b c0 c1 c2 : ℝ) :
    Continuous (gateDefect a b c0 c1 c2) := by
  unfold gateDefect coshDiff
  fun_prop

/-- At radius zero the gate defect is strictly positive: this is exactly the
point-window gate, a theorem of `CoshWindowSeparation`. -/
theorem gateDefect_zero_pos {a b c0 c1 c2 : ℝ} (ha : 0 < a) (hab : a < b) (hc0 : 0 < c0)
    (h01 : c0 < c1) (h12 : c1 < c2) : 0 < gateDefect a b c0 c1 c2 0 := by
  have := window_gate_of_point_windows ha hab hc0 h01 h12
  unfold gateDefect
  simp only [sub_zero, add_zero]
  linarith

/-- **The four-endpoint gate is satisfied by all sufficiently narrow windows.**  There
is a strictly positive radius `e` for which the three symmetric windows of radius `e`
around `c₀ < c₁ < c₂` are ordered, stay in the positive halfline, and satisfy the
gate of `LiteralWeilWindowRatioSeparation.covForm_det_lt`. -/
theorem exists_gate_radius {a b c0 c1 c2 : ℝ} (ha : 0 < a) (hab : a < b) (hc0 : 0 < c0)
    (h01 : c0 < c1) (h12 : c1 < c2) :
    ∃ e : ℝ, 0 < e ∧ e < c0 ∧ c0 + e < c1 - e ∧ c1 + e < c2 - e ∧
      coshDiff b (c0 + e) (c1 + e) * coshDiff a (c0 - e) (c2 - e)
        < coshDiff b (c0 - e) (c2 - e) * coshDiff a (c0 + e) (c1 + e) := by
  have hopen : IsOpen {e : ℝ | 0 < gateDefect a b c0 c1 c2 e} :=
    isOpen_lt continuous_const (continuous_gateDefect a b c0 c1 c2)
  have hmem : (0 : ℝ) ∈ {e : ℝ | 0 < gateDefect a b c0 c1 c2 e} :=
    gateDefect_zero_pos ha hab hc0 h01 h12
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hopen 0 hmem
  set e : ℝ := min (min (eps / 2) (c0 / 2)) (min ((c1 - c0) / 4) ((c2 - c1) / 4)) with he
  have he1 : e ≤ eps / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have he2 : e ≤ c0 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have he3 : e ≤ (c1 - c0) / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
  have he4 : e ≤ (c2 - c1) / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hepos : 0 < e := by
    rw [he]
    refine lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
  have hin : e ∈ Metric.ball (0 : ℝ) eps := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hepos]
    linarith
  have hgate : 0 < gateDefect a b c0 c1 c2 e := hball hin
  refine ⟨e, hepos, by linarith, by linarith, by linarith, ?_⟩
  unfold gateDefect at hgate
  linarith

/-! ## The full instance -/

/-- **The localized-window separation is realised.**  For any two heights `0 < a < b`
and any three ordered centres `0 < c₀ < c₁ < c₂` there exist three window tapers `p`,
`q₀`, `q₁`, supported in disjoint ordered modulus windows around the three centres,
whose polarised leading coefficients separate strictly:

    covForm p q₁ a * covForm p q₀ b  <  covForm p q₀ a * covForm p q₁ b.

In particular the hypothesis of the two-taper Schur admission gate is not vacuous. -/
theorem exists_separated_window_tapers {a b c0 c1 c2 : ℝ} (ha : 0 < a) (hab : a < b)
    (hc0 : 0 < c0) (h01 : c0 < c1) (h12 : c1 < c2) :
    ∃ (p q0 q1 : ℝ → ℝ) (al0 be0 al1 be1 al2 be2 : ℝ),
      WindowTaper p al0 be0 ∧ WindowTaper q0 al1 be1 ∧ WindowTaper q1 al2 be2 ∧
      0 < al0 ∧ al0 ≤ be0 ∧ be0 < al1 ∧ al1 ≤ be1 ∧ be1 < al2 ∧ al2 ≤ be2 ∧
      covForm p q1 a * covForm p q0 b < covForm p q0 a * covForm p q1 b := by
  obtain ⟨e, hepos, hec0, hord1, hord2, hgate⟩ := exists_gate_radius ha hab hc0 h01 h12
  have hp := exists_windowTaper (lo := c0 - e) (hi := c0 + e) (by linarith) (by linarith)
  have hq0 := exists_windowTaper (lo := c1 - e) (hi := c1 + e) (by linarith) (by linarith)
  have hq1 := exists_windowTaper (lo := c2 - e) (hi := c2 + e) (by linarith) (by linarith)
  refine ⟨_, _, _, c0 - e, c0 + e, c1 - e, c1 + e, c2 - e, c2 + e, hp, hq0, hq1,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
  exact covForm_det_lt hp hq0 hq1 ha hab (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hgate

end LiteralWeilWindowSeparationInstance
end Zeta23Bridge
