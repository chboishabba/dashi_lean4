/-
# The Eq. (119) source spine, end to end

This module assembles the source-side chain in a single theorem, with every
step a proved implication and no interface, receipt or recognition axiom in
between:

  stored positive bonds with `ℓ¹` budget `1/2048`
    → signed traversals are conjugates, same budget
    → closed word `Γ ∥ c⁻¹` of at most `74` oriented links
    → relative element `U(Γ) U(c)⁻¹` (same-object identity)
    → operator defect `≤ 37/1024 < 1/24`
    → principal chart admission
    → `Y` with `Y.re = 0`, `‖Y‖ < π/2` and `exp (su2 Y) = U(Γ) U(c)⁻¹`.

`relative_log_spine` is the whole chain; `relative_log_spine_quantitative`
adds the sharp bound `‖Y‖ ≤ arccos (1 - 37/1024)` on the produced Lie-algebra
element.

What is *not* claimed: that the stored bonds of an actual Bałaban background
satisfy the `1/2048` budget.  That is the physical hypothesis of the theorem,
displayed as such.
-/
import Mathlib
import RequestProject.YangMills.SU2QuaternionOperatorNorm
import RequestProject.YangMills.RelativeHolonomyDefect
import RequestProject.YangMills.SU2PrincipalChart

namespace RequestProject.YangMills.Eq119RelativeLogSpine

open NormedSpace Matrix
open scoped Matrix.Norms.L2Operator
open RequestProject.YangMills.SU2QuaternionOperatorNorm
open RequestProject.YangMills.RelativeHolonomyDefect
open RequestProject.YangMills.SU2PrincipalChart

/-- **The Eq. (119) source spine.**  From the stored positive-bond budget alone,
the literal relative holonomy of the closed word `Γ ∥ c⁻¹` admits a principal
logarithm, and the closed word really is the relative element. -/
theorem relative_log_spine (gamma c : List (Bool × Quaternion ℝ))
    (hlen : gamma.length + c.length ≤ 74)
    (hu : ∀ b ∈ gamma ++ reverseWord c, IsUnitQuaternion b.2)
    (hd : ∀ b ∈ gamma ++ reverseWord c, l1defect b.2 ≤ 1 / 2048)
    (hc : ∀ b ∈ c, IsUnitQuaternion b.2) :
    holonomy (gamma ++ reverseWord c) * holonomy c = holonomy gamma ∧
      ∃ Y : Quaternion ℝ, Y.re = 0 ∧ ‖Y‖ < Real.pi / 2 ∧
        exp (su2 Y) = holonomy (gamma ++ reverseWord c) := by
  refine ⟨holonomy_relative gamma c hc, ?_⟩
  set w := gamma ++ reverseWord c with hw
  have hdef : defect (holonomy w) ≤ 37 / 1024 :=
    relative_holonomy_defect_le gamma c hlen hu hd
  have huq : IsUnitQuaternion (qholonomy w) := isUnitQuaternion_qholonomy hu
  have hmat : holonomy w = su2 (qholonomy w) := holonomy_eq_su2_qholonomy w
  have hsmall : ‖su2 (qholonomy w) - 1‖ < 1 := by
    have : defect (holonomy w) < 1 := lt_of_le_of_lt hdef (by norm_num)
    rw [defect, hmat] at this
    exact this
  obtain ⟨Y, hYre, hYnorm, hYexp⟩ := principal_chart_of_defect_lt_one huq hsmall
  exact ⟨Y, hYre, hYnorm, by rw [hYexp, hmat]⟩

/-- The quantitative form: the produced Lie-algebra element obeys the sharp
bound coming from the `37/1024` defect. -/
theorem relative_log_spine_quantitative (gamma c : List (Bool × Quaternion ℝ))
    (hlen : gamma.length + c.length ≤ 74)
    (hu : ∀ b ∈ gamma ++ reverseWord c, IsUnitQuaternion b.2)
    (hd : ∀ b ∈ gamma ++ reverseWord c, l1defect b.2 ≤ 1 / 2048) :
    ∃ Y : Quaternion ℝ, Y.re = 0 ∧ ‖Y‖ ≤ Real.arccos (1 - 37 / 1024) ∧
      exp (su2 Y) = holonomy (gamma ++ reverseWord c) := by
  set w := gamma ++ reverseWord c with hw
  have hdef : defect (holonomy w) ≤ 37 / 1024 :=
    relative_holonomy_defect_le gamma c hlen hu hd
  have huq : IsUnitQuaternion (qholonomy w) := isUnitQuaternion_qholonomy hu
  have hmat : holonomy w = su2 (qholonomy w) := holonomy_eq_su2_qholonomy w
  have hdefq : ‖su2 (qholonomy w) - 1‖ ≤ 37 / 1024 := by
    rw [defect, hmat] at hdef
    exact hdef
  have hre : 1 - 37 / 1024 ≤ (qholonomy w).re := by
    have := abs_re_sub_one_le_defect (qholonomy w)
    have habs : |(qholonomy w).re - 1| ≤ 37 / 1024 := this.trans hdefq
    have := abs_le.mp habs
    linarith [this.1]
  have hrepos : 0 < (qholonomy w).re := by linarith
  refine ⟨qlog (qholonomy w), qlog_re _, ?_, ?_⟩
  · rw [norm_qlog huq (by linarith)]
    exact Real.arccos_le_arccos hre
  · rw [← su2_exp, exp_qlog huq (by linarith), hmat]

end RequestProject.YangMills.Eq119RelativeLogSpine
