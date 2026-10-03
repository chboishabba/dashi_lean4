import Mathlib.Tactic
import NSBControl.Rational345BPMixedBounds

/-!
# B_P forcing-commutator operator leaves

Closes the remaining two fields of `CoherentOperatorLeaves` using:

* the genuine real H± bound;
* the projected-forcing value/difference bounds from B_P production;
* one-resonant-q-per-p finite support at fixed output.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345BPCommutatorBounds

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345BQFieldBound
open Rational345BPBudget
open Rational345BPMaxCut
open Rational345BPProduction
open Rational345BPHelicalBounds
open Rational345BPMixedBounds

classical

/-- Difference bound for one cross-product component. -/
theorem cross_pair_diff_component_le
    (a₁ a₂ b₁ b₂ : Vec3) (j : Fin 3) :
    ‖cross a₁ b₁ j - cross a₂ b₂ j‖
      ≤ 2 * ‖a₁ - a₂‖ * ‖b₁‖ +
        2 * ‖a₂‖ * ‖b₁ - b₂‖ := by
  rw [show cross a₁ b₁ - cross a₂ b₂ =
    cross (a₁ - a₂) b₁ + cross a₂ (b₁ - b₂) from
      cross_sub_cross _ _ _ _]
  calc
    ‖(cross (a₁ - a₂) b₁ + cross a₂ (b₁ - b₂)) j‖
      ≤ ‖cross (a₁ - a₂) b₁ j‖ +
        ‖cross a₂ (b₁ - b₂) j‖ := norm_add_le _ _
    _ ≤ 2 * ‖a₁ - a₂‖ * ‖b₁‖ +
        2 * ‖a₂‖ * ‖b₁ - b₂‖ := by
      gcongr
      · exact cross_component_norm_le _ _ _
      · exact cross_component_norm_le _ _ _

/-- One forcing-commutator cell value. -/
theorem forcingCommutatorCell_component_le
    (u forcing : State) (p q : Mode) (j : Fin 3) :
    ‖forcingCommutatorCell u forcing p q j‖
      ≤ 4 * helicalConstant^2 * ‖forcing‖ * ‖u‖ := by
  unfold forcingCommutatorCell
  calc
    ‖cross (helicalPlus p (forcing p)) (helicalMinus q (u q)) j -
      cross (helicalMinus p (forcing p)) (helicalPlus q (u q)) j‖
      ≤ ‖cross (helicalPlus p (forcing p)) (helicalMinus q (u q)) j‖ +
        ‖cross (helicalMinus p (forcing p)) (helicalPlus q (u q)) j‖ :=
          norm_sub_le _ _
    _ ≤ 2 * ‖helicalPlus p (forcing p)‖ * ‖helicalMinus q (u q)‖ +
        2 * ‖helicalMinus p (forcing p)‖ * ‖helicalPlus q (u q)‖ := by
      gcongr
      · exact cross_component_norm_le _ _ _
      · exact cross_component_norm_le _ _ _
    _ ≤ 2 * (helicalConstant * ‖forcing p‖) *
          (helicalConstant * ‖u q‖) +
        2 * (helicalConstant * ‖forcing p‖) *
          (helicalConstant * ‖u q‖) := by
      gcongr
      · exact helicalPlus_norm_le p (forcing p)
      · exact helicalMinus_norm_le q (u q)
      · exact helicalMinus_norm_le p (forcing p)
      · exact helicalPlus_norm_le q (u q)
    _ ≤ 4 * helicalConstant^2 * ‖forcing‖ * ‖u‖ := by
      have hf : ‖forcing p‖ ≤ ‖forcing‖ := norm_le_pi_norm forcing p
      have hu : ‖u q‖ ≤ ‖u‖ := norm_le_pi_norm u q
      nlinarith [helicalConstant_pos, norm_nonneg forcing, norm_nonneg u]

/-- One forcing-commutator cell difference specialized to F(u). -/
theorem forcingCommutatorCell_projected_diff_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (p q : Mode) (j : Fin 3) :
    ‖forcingCommutatorCell x (projectedNonlinearity x) p q j -
      forcingCommutatorCell y (projectedNonlinearity y) p q j‖
      ≤ 4 * helicalConstant^2 *
        (forcingLipschitzBound * stateBound + forcingValueBound) *
        ‖x - y‖ := by
  let fx := projectedNonlinearity x
  let fy := projectedNonlinearity y
  have hxR := norm_le_stateBound_of_mem_bpBall hx
  have hyR := norm_le_stateBound_of_mem_bpBall hy
  have hfx := forcing_norm_le hx
  have hfy := forcing_norm_le hy
  have hfd := forcing_diff_norm_le hx hy
  have hdfp : ‖fx p - fy p‖ ≤ forcingLipschitzBound * ‖x - y‖ := by
    exact (norm_le_pi_norm (fx - fy) p).trans hfd
  have hfxp : ‖fx p‖ ≤ forcingValueBound :=
    (norm_le_pi_norm fx p).trans hfx
  have hfyp : ‖fy p‖ ≤ forcingValueBound :=
    (norm_le_pi_norm fy p).trans hfy
  have hdxq : ‖x q - y q‖ ≤ ‖x - y‖ := by
    exact norm_le_pi_norm (x - y) q
  have hxq : ‖x q‖ ≤ stateBound := (norm_le_pi_norm x q).trans hxR
  have hyq : ‖y q‖ ≤ stateBound := (norm_le_pi_norm y q).trans hyR

  have hplusF :
      ‖helicalPlus p (fx p) - helicalPlus p (fy p)‖
        ≤ helicalConstant * (forcingLipschitzBound * ‖x - y‖) := by
    rw [helicalPlus_sub]
    exact (helicalPlus_norm_le p (fx p - fy p)).trans (by gcongr)
  have hminusF :
      ‖helicalMinus p (fx p) - helicalMinus p (fy p)‖
        ≤ helicalConstant * (forcingLipschitzBound * ‖x - y‖) := by
    rw [helicalMinus_sub]
    exact (helicalMinus_norm_le p (fx p - fy p)).trans (by gcongr)
  have hplusU :
      ‖helicalPlus q (x q) - helicalPlus q (y q)‖
        ≤ helicalConstant * ‖x - y‖ := by
    rw [helicalPlus_sub]
    exact (helicalPlus_norm_le q (x q - y q)).trans (by gcongr)
  have hminusU :
      ‖helicalMinus q (x q) - helicalMinus q (y q)‖
        ≤ helicalConstant * ‖x - y‖ := by
    rw [helicalMinus_sub]
    exact (helicalMinus_norm_le q (x q - y q)).trans (by gcongr)

  have hplusFx : ‖helicalPlus p (fx p)‖ ≤ helicalConstant * forcingValueBound :=
    (helicalPlus_norm_le p (fx p)).trans (by gcongr)
  have hplusFy : ‖helicalPlus p (fy p)‖ ≤ helicalConstant * forcingValueBound :=
    (helicalPlus_norm_le p (fy p)).trans (by gcongr)
  have hminusFx : ‖helicalMinus p (fx p)‖ ≤ helicalConstant * forcingValueBound :=
    (helicalMinus_norm_le p (fx p)).trans (by gcongr)
  have hminusFy : ‖helicalMinus p (fy p)‖ ≤ helicalConstant * forcingValueBound :=
    (helicalMinus_norm_le p (fy p)).trans (by gcongr)
  have hplusX : ‖helicalPlus q (x q)‖ ≤ helicalConstant * stateBound :=
    (helicalPlus_norm_le q (x q)).trans (by gcongr)
  have hminusX : ‖helicalMinus q (x q)‖ ≤ helicalConstant * stateBound :=
    (helicalMinus_norm_le q (x q)).trans (by gcongr)
  have hplusY : ‖helicalPlus q (y q)‖ ≤ helicalConstant * stateBound :=
    (helicalPlus_norm_le q (y q)).trans (by gcongr)
  have hminusY : ‖helicalMinus q (y q)‖ ≤ helicalConstant * stateBound :=
    (helicalMinus_norm_le q (y q)).trans (by gcongr)

  unfold forcingCommutatorCell
  calc
    ‖(cross (helicalPlus p (fx p)) (helicalMinus q (x q)) -
        cross (helicalMinus p (fx p)) (helicalPlus q (x q))) j -
      (cross (helicalPlus p (fy p)) (helicalMinus q (y q)) -
        cross (helicalMinus p (fy p)) (helicalPlus q (y q))) j‖
      ≤ ‖cross (helicalPlus p (fx p)) (helicalMinus q (x q)) j -
          cross (helicalPlus p (fy p)) (helicalMinus q (y q)) j‖ +
        ‖cross (helicalMinus p (fx p)) (helicalPlus q (x q)) j -
          cross (helicalMinus p (fy p)) (helicalPlus q (y q)) j‖ := by
        have := norm_sub_le
          (cross (helicalPlus p (fx p)) (helicalMinus q (x q)) j -
            cross (helicalPlus p (fy p)) (helicalMinus q (y q)) j)
          (cross (helicalMinus p (fx p)) (helicalPlus q (x q)) j -
            cross (helicalMinus p (fy p)) (helicalPlus q (y q)) j)
        convert this using 1 <;> ring
    _ ≤ (2 * ‖helicalPlus p (fx p) - helicalPlus p (fy p)‖ *
            ‖helicalMinus q (x q)‖ +
          2 * ‖helicalPlus p (fy p)‖ *
            ‖helicalMinus q (x q) - helicalMinus q (y q)‖) +
        (2 * ‖helicalMinus p (fx p) - helicalMinus p (fy p)‖ *
            ‖helicalPlus q (x q)‖ +
          2 * ‖helicalMinus p (fy p)‖ *
            ‖helicalPlus q (x q) - helicalPlus q (y q)‖) := by
        gcongr
        · exact cross_pair_diff_component_le _ _ _ _ j
        · exact cross_pair_diff_component_le _ _ _ _ j
    _ ≤ (2 * (helicalConstant * (forcingLipschitzBound * ‖x - y‖)) *
            (helicalConstant * stateBound) +
          2 * (helicalConstant * forcingValueBound) *
            (helicalConstant * ‖x - y‖)) +
        (2 * (helicalConstant * (forcingLipschitzBound * ‖x - y‖)) *
            (helicalConstant * stateBound) +
          2 * (helicalConstant * forcingValueBound) *
            (helicalConstant * ‖x - y‖)) := by
        gcongr
    _ = 4 * helicalConstant^2 *
        (forcingLipschitzBound * stateBound + forcingValueBound) *
        ‖x - y‖ := by ring

private theorem inner_commutator_value_le
    {u : State}
    (hu : u ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (p k : Mode) (j : Fin 3) :
    ‖∑ q : Mode, if Resonates p q k then
        forcingCommutatorCell u (projectedNonlinearity u) p q j else 0‖
      ≤ 4 * helicalConstant^2 * forcingValueBound * stateBound := by
  have huR := norm_le_stateBound_of_mem_bpBall hu
  have hf := forcing_norm_le hu
  have heq :
      (∑ q : Mode, if Resonates p q k then
        forcingCommutatorCell u (projectedNonlinearity u) p q j else 0) =
      ∑ q in resonantQs p k,
        forcingCommutatorCell u (projectedNonlinearity u) p q j := by
    simp [resonantQs]
  rw [heq]
  calc
    ‖∑ q in resonantQs p k,
        forcingCommutatorCell u (projectedNonlinearity u) p q j‖
      ≤ ∑ q in resonantQs p k,
        ‖forcingCommutatorCell u (projectedNonlinearity u) p q j‖ := norm_sum_le _ _
    _ ≤ ∑ _q in resonantQs p k,
        4 * helicalConstant^2 * forcingValueBound * stateBound := by
      apply Finset.sum_le_sum
      intro q hq
      calc
        ‖forcingCommutatorCell u (projectedNonlinearity u) p q j‖
          ≤ 4 * helicalConstant^2 * ‖projectedNonlinearity u‖ * ‖u‖ :=
            forcingCommutatorCell_component_le _ _ _ _ _
        _ ≤ 4 * helicalConstant^2 * forcingValueBound * stateBound := by
          gcongr
    _ = (resonantQs p k).card *
        (4 * helicalConstant^2 * forcingValueBound * stateBound) := by simp
    _ ≤ 1 * (4 * helicalConstant^2 * forcingValueBound * stateBound) := by
      gcongr
      · exact resonantQs_card_le_one p k
      · positivity
    _ = 4 * helicalConstant^2 * forcingValueBound * stateBound := by ring

private theorem inner_commutator_diff_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (p k : Mode) (j : Fin 3) :
    ‖(∑ q : Mode, if Resonates p q k then
        forcingCommutatorCell x (projectedNonlinearity x) p q j else 0) -
      (∑ q : Mode, if Resonates p q k then
        forcingCommutatorCell y (projectedNonlinearity y) p q j else 0)‖
      ≤ 4 * helicalConstant^2 *
        (forcingLipschitzBound * stateBound + forcingValueBound) *
        ‖x - y‖ := by
  have heq :
      (∑ q : Mode, if Resonates p q k then
        forcingCommutatorCell x (projectedNonlinearity x) p q j else 0) -
      (∑ q : Mode, if Resonates p q k then
        forcingCommutatorCell y (projectedNonlinearity y) p q j else 0) =
      ∑ q in resonantQs p k,
        (forcingCommutatorCell x (projectedNonlinearity x) p q j -
         forcingCommutatorCell y (projectedNonlinearity y) p q j) := by
    simp [resonantQs, Finset.sum_sub_distrib]
  rw [heq]
  calc
    ‖∑ q in resonantQs p k,
      (forcingCommutatorCell x (projectedNonlinearity x) p q j -
       forcingCommutatorCell y (projectedNonlinearity y) p q j)‖
      ≤ ∑ q in resonantQs p k,
        ‖forcingCommutatorCell x (projectedNonlinearity x) p q j -
         forcingCommutatorCell y (projectedNonlinearity y) p q j‖ := norm_sum_le _ _
    _ ≤ ∑ _q in resonantQs p k,
        4 * helicalConstant^2 *
          (forcingLipschitzBound * stateBound + forcingValueBound) *
          ‖x - y‖ := by
      apply Finset.sum_le_sum
      intro q hq
      exact forcingCommutatorCell_projected_diff_le hx hy p q j
    _ = (resonantQs p k).card *
        (4 * helicalConstant^2 *
          (forcingLipschitzBound * stateBound + forcingValueBound) *
          ‖x - y‖) := by simp
    _ ≤ 1 * (4 * helicalConstant^2 *
          (forcingLipschitzBound * stateBound + forcingValueBound) *
          ‖x - y‖) := by
      gcongr
      · exact resonantQs_card_le_one p k
      · positivity
    _ = 4 * helicalConstant^2 *
        (forcingLipschitzBound * stateBound + forcingValueBound) *
        ‖x - y‖ := by ring

/-- Commutator fixed-output component value. -/
theorem fixedOutputCommutator_component_le
    {u : State}
    (hu : u ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) (j : Fin 3) :
    ‖fixedOutputCommutator u (projectedNonlinearity u) k j‖
      ≤ commutatorValueBound := by
  unfold fixedOutputCommutator
  calc
    ‖∑ p : Mode,
      (∑ q : Mode, if Resonates p q k then
        forcingCommutatorCell u (projectedNonlinearity u) p q else 0) j‖
      ≤ ∑ p : Mode,
        ‖∑ q : Mode, if Resonates p q k then
          forcingCommutatorCell u (projectedNonlinearity u) p q j else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _p : Mode,
        4 * helicalConstant^2 * forcingValueBound * stateBound := by
      apply Finset.sum_le_sum
      intro p hp
      exact inner_commutator_value_le hu p k j
    _ = 729 * (4 * helicalConstant^2 * forcingValueBound * stateBound) := by
      rw [show Fintype.card Mode = 729 by native_decide]
      simp
    _ = commutatorValueBound := by
      unfold commutatorValueBound
      ring

/-- Commutator fixed-output component difference. -/
theorem fixedOutputCommutator_diff_component_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) (j : Fin 3) :
    ‖fixedOutputCommutator x (projectedNonlinearity x) k j -
      fixedOutputCommutator y (projectedNonlinearity y) k j‖
      ≤ commutatorLipschitzBound * ‖x - y‖ := by
  unfold fixedOutputCommutator
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ p : Mode,
      ((∑ q : Mode, if Resonates p q k then
        forcingCommutatorCell x (projectedNonlinearity x) p q else 0) -
       (∑ q : Mode, if Resonates p q k then
        forcingCommutatorCell y (projectedNonlinearity y) p q else 0)) j‖
      ≤ ∑ p : Mode,
        ‖(∑ q : Mode, if Resonates p q k then
          forcingCommutatorCell x (projectedNonlinearity x) p q j else 0) -
         (∑ q : Mode, if Resonates p q k then
          forcingCommutatorCell y (projectedNonlinearity y) p q j else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _p : Mode,
        4 * helicalConstant^2 *
          (forcingLipschitzBound * stateBound + forcingValueBound) *
          ‖x - y‖ := by
      apply Finset.sum_le_sum
      intro p hp
      exact inner_commutator_diff_le hx hy p k j
    _ = 729 * (4 * helicalConstant^2 *
        (forcingLipschitzBound * stateBound + forcingValueBound) *
        ‖x - y‖) := by
      rw [show Fintype.card Mode = 729 by native_decide]
      simp
    _ = commutatorLipschitzBound * ‖x - y‖ := by
      unfold commutatorLipschitzBound
      ring

private theorem vec_norm_le_of_components
    (v : Vec3) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j : Fin 3, ‖v j‖ ≤ C) : ‖v‖ ≤ C := by
  rw [pi_norm_le_iff_of_nonneg hC]
  exact h

/-- Last two `CoherentOperatorLeaves` fields. -/
theorem fixedOutputCommutator_norm_le
    {u : State}
    (hu : u ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) :
    ‖fixedOutputCommutator u (projectedNonlinearity u) k‖
      ≤ commutatorValueBound := by
  apply vec_norm_le_of_components _ (by positivity)
  intro j
  exact fixedOutputCommutator_component_le hu k j

theorem fixedOutputCommutator_diff_norm_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) :
    ‖fixedOutputCommutator x (projectedNonlinearity x) k -
      fixedOutputCommutator y (projectedNonlinearity y) k‖
      ≤ commutatorLipschitzBound * ‖x - y‖ := by
  apply vec_norm_le_of_components _ (by positivity)
  intro j
  exact fixedOutputCommutator_diff_component_le hx hy k j

end Rational345BPCommutatorBounds
end NSBControl
