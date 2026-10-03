import Mathlib.Tactic
import NSBControl.Rational345BPHelicalBounds
import NSBControl.Rational345BPMaxCut

/-!
# B_P mixed-fold operator leaves

Uses the genuine real helical bound plus fixed-output resonance uniqueness to
prove the two mixed-vector inequalities consumed by the coherent-work max-cut.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345BPMixedBounds

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345BQFieldBound
open Rational345BPBudget
open Rational345BPMaxCut
open Rational345BPHelicalBounds

classical

/-- Modal vector norm is bounded by the full state sup norm. -/
theorem modeVec_norm_le_state_norm (u : State) (k : Mode) :
    ‖u k‖ ≤ ‖u‖ := norm_le_pi_norm u k

/-- One mixed cell component. -/
theorem mixedCell_component_norm_le
    (u : State) (p q : Mode) (j : Fin 3) :
    ‖mixedCell u p q j‖
      ≤ 2 * helicalConstant^2 * ‖u‖^2 := by
  unfold mixedCell
  calc
    ‖cross (helicalPlus p (u p)) (helicalMinus q (u q)) j‖
      ≤ 2 * ‖helicalPlus p (u p)‖ * ‖helicalMinus q (u q)‖ :=
        cross_component_norm_le _ _ _
    _ ≤ 2 * (helicalConstant * ‖u p‖) *
        (helicalConstant * ‖u q‖) := by
      gcongr
      · exact helicalPlus_norm_le p (u p)
      · exact helicalMinus_norm_le q (u q)
    _ ≤ 2 * helicalConstant^2 * ‖u‖^2 := by
      have hp := modeVec_norm_le_state_norm u p
      have hq := modeVec_norm_le_state_norm u q
      nlinarith [helicalConstant_pos, norm_nonneg u]

/-- One mixed-cell difference on the B_P ball. -/
theorem mixedCell_diff_component_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (p q : Mode) (j : Fin 3) :
    ‖mixedCell x p q j - mixedCell y p q j‖
      ≤ 4 * helicalConstant^2 * stateBound * ‖x - y‖ := by
  have hxR := norm_le_stateBound_of_mem_bpBall hx
  have hyR := norm_le_stateBound_of_mem_bpBall hy
  unfold mixedCell
  rw [show cross (helicalPlus p (x p)) (helicalMinus q (x q)) -
      cross (helicalPlus p (y p)) (helicalMinus q (y q)) =
      cross (helicalPlus p (x p) - helicalPlus p (y p))
        (helicalMinus q (x q)) +
      cross (helicalPlus p (y p))
        (helicalMinus q (x q) - helicalMinus q (y q)) from
      cross_sub_cross _ _ _ _]
  rw [helicalPlus_sub, helicalMinus_sub]
  have hdp : ‖x p - y p‖ ≤ ‖x - y‖ := by
    simpa using norm_le_pi_norm (x - y) p
  have hdq : ‖x q - y q‖ ≤ ‖x - y‖ := by
    simpa using norm_le_pi_norm (x - y) q
  have hxp : ‖x p‖ ≤ stateBound := (norm_le_pi_norm x p).trans hxR
  have hxq : ‖x q‖ ≤ stateBound := (norm_le_pi_norm x q).trans hxR
  have hyp : ‖y p‖ ≤ stateBound := (norm_le_pi_norm y p).trans hyR
  calc
    ‖(cross (helicalPlus p (x p - y p)) (helicalMinus q (x q)) +
      cross (helicalPlus p (y p)) (helicalMinus q (x q - y q))) j‖
      ≤ ‖cross (helicalPlus p (x p - y p)) (helicalMinus q (x q)) j‖ +
        ‖cross (helicalPlus p (y p)) (helicalMinus q (x q - y q)) j‖ :=
          norm_add_le _ _
    _ ≤ 2 * (helicalConstant * ‖x p - y p‖) *
          (helicalConstant * ‖x q‖) +
        2 * (helicalConstant * ‖y p‖) *
          (helicalConstant * ‖x q - y q‖) := by
      gcongr
      · exact cross_component_norm_le _ _ _
      · exact helicalPlus_norm_le p (x p - y p)
      · exact helicalMinus_norm_le q (x q)
      · exact cross_component_norm_le _ _ _
      · exact helicalPlus_norm_le p (y p)
      · exact helicalMinus_norm_le q (x q - y q)
    _ ≤ 4 * helicalConstant^2 * stateBound * ‖x - y‖ := by
      nlinarith [helicalConstant_pos, norm_nonneg (x - y)]

private theorem inner_mixed_value_le
    {u : State}
    (hu : u ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (p k : Mode) (j : Fin 3) :
    ‖∑ q : Mode, if Resonates p q k then mixedCell u p q j else 0‖
      ≤ 2 * helicalConstant^2 * stateBound^2 := by
  have huR := norm_le_stateBound_of_mem_bpBall hu
  have heq :
      (∑ q : Mode, if Resonates p q k then mixedCell u p q j else 0) =
      ∑ q in resonantQs p k, mixedCell u p q j := by
    simp [resonantQs]
  rw [heq]
  calc
    ‖∑ q in resonantQs p k, mixedCell u p q j‖
      ≤ ∑ q in resonantQs p k, ‖mixedCell u p q j‖ := norm_sum_le _ _
    _ ≤ ∑ _q in resonantQs p k,
        2 * helicalConstant^2 * stateBound^2 := by
      apply Finset.sum_le_sum
      intro q hq
      calc
        ‖mixedCell u p q j‖
          ≤ 2 * helicalConstant^2 * ‖u‖^2 := mixedCell_component_norm_le u p q j
        _ ≤ 2 * helicalConstant^2 * stateBound^2 := by
          gcongr
    _ = (resonantQs p k).card *
        (2 * helicalConstant^2 * stateBound^2) := by simp
    _ ≤ 1 * (2 * helicalConstant^2 * stateBound^2) := by
      gcongr
      · exact resonantQs_card_le_one p k
      · positivity
    _ = 2 * helicalConstant^2 * stateBound^2 := by ring

private theorem inner_mixed_diff_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (p k : Mode) (j : Fin 3) :
    ‖(∑ q : Mode, if Resonates p q k then mixedCell x p q j else 0) -
      (∑ q : Mode, if Resonates p q k then mixedCell y p q j else 0)‖
      ≤ 4 * helicalConstant^2 * stateBound * ‖x - y‖ := by
  have heq :
      (∑ q : Mode, if Resonates p q k then mixedCell x p q j else 0) -
      (∑ q : Mode, if Resonates p q k then mixedCell y p q j else 0) =
      ∑ q in resonantQs p k, (mixedCell x p q j - mixedCell y p q j) := by
    simp [resonantQs, Finset.sum_sub_distrib]
  rw [heq]
  calc
    ‖∑ q in resonantQs p k,
      (mixedCell x p q j - mixedCell y p q j)‖
      ≤ ∑ q in resonantQs p k,
        ‖mixedCell x p q j - mixedCell y p q j‖ := norm_sum_le _ _
    _ ≤ ∑ _q in resonantQs p k,
        4 * helicalConstant^2 * stateBound * ‖x - y‖ := by
      apply Finset.sum_le_sum
      intro q hq
      exact mixedCell_diff_component_le hx hy p q j
    _ = (resonantQs p k).card *
        (4 * helicalConstant^2 * stateBound * ‖x - y‖) := by simp
    _ ≤ 1 * (4 * helicalConstant^2 * stateBound * ‖x - y‖) := by
      gcongr
      · exact resonantQs_card_le_one p k
      · positivity
    _ = 4 * helicalConstant^2 * stateBound * ‖x - y‖ := by ring

/-- Mixed fixed-output component value bound. -/
theorem fixedOutputMixed_component_le
    {u : State}
    (hu : u ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) (j : Fin 3) :
    ‖fixedOutputMixed u k j‖ ≤ mixedValueBound := by
  unfold fixedOutputMixed
  calc
    ‖∑ p : Mode,
      (∑ q : Mode, if Resonates p q k then mixedCell u p q else 0) j‖
      ≤ ∑ p : Mode,
        ‖∑ q : Mode, if Resonates p q k then mixedCell u p q j else 0‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _p : Mode, 2 * helicalConstant^2 * stateBound^2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact inner_mixed_value_le hu p k j
    _ = 729 * (2 * helicalConstant^2 * stateBound^2) := by
      rw [show Fintype.card Mode = 729 by native_decide]
      simp
    _ = mixedValueBound := by
      unfold mixedValueBound
      ring

/-- Mixed fixed-output component difference bound. -/
theorem fixedOutputMixed_diff_component_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) (j : Fin 3) :
    ‖fixedOutputMixed x k j - fixedOutputMixed y k j‖
      ≤ mixedLipschitzBound * ‖x - y‖ := by
  unfold fixedOutputMixed
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ p : Mode,
      ((∑ q : Mode, if Resonates p q k then mixedCell x p q else 0) -
       (∑ q : Mode, if Resonates p q k then mixedCell y p q else 0)) j‖
      ≤ ∑ p : Mode,
        ‖(∑ q : Mode, if Resonates p q k then mixedCell x p q j else 0) -
          (∑ q : Mode, if Resonates p q k then mixedCell y p q j else 0)‖ :=
            norm_sum_le _ _
    _ ≤ ∑ _p : Mode,
        4 * helicalConstant^2 * stateBound * ‖x - y‖ := by
      apply Finset.sum_le_sum
      intro p hp
      exact inner_mixed_diff_le hx hy p k j
    _ = 729 * (4 * helicalConstant^2 * stateBound * ‖x - y‖) := by
      rw [show Fintype.card Mode = 729 by native_decide]
      simp
    _ = mixedLipschitzBound * ‖x - y‖ := by
      unfold mixedLipschitzBound
      ring

private theorem vec_norm_le_of_components
    (v : Vec3) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j : Fin 3, ‖v j‖ ≤ C) : ‖v‖ ≤ C := by
  rw [pi_norm_le_iff_of_nonneg hC]
  exact h

/-- First two `CoherentOperatorLeaves` fields. -/
theorem fixedOutputMixed_norm_le
    {u : State}
    (hu : u ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) :
    ‖fixedOutputMixed u k‖ ≤ mixedValueBound := by
  apply vec_norm_le_of_components _ (by positivity)
  intro j
  exact fixedOutputMixed_component_le hu k j

theorem fixedOutputMixed_diff_norm_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) :
    ‖fixedOutputMixed x k - fixedOutputMixed y k‖
      ≤ mixedLipschitzBound * ‖x - y‖ := by
  apply vec_norm_le_of_components _ (by positivity)
  intro j
  exact fixedOutputMixed_diff_component_le hx hy k j

end Rational345BPMixedBounds
end NSBControl
