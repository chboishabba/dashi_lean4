import Mathlib.Tactic
import NSBControl.Rational345BQGeometry
import NSBControl.Rational345BPBudget
import NSBControl.Rational345R830DecisionCompiler

/-!
# B_P max-cut

The selected-rate difference is split according to the literal R815
normalization:

  72 * (global coherent work difference)
-  6 * (critical production difference)
+  6 * (critical dissipation difference).

This owner closes the quadratic dissipation term outright on the radius-1/100
bootstrap ball and exposes only two remaining quantitative leaves:

* cubic critical-production difference;
* degree-five global coherent-work difference.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345BPMaxCut

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345BQGeometry
open Rational345BPBudget
open Rational345ShortTime
open Rational345R830DecisionCompiler

classical

/-- States in the B_P ball have norm at most 6.01. -/
theorem norm_le_stateBound_of_mem_bpBall
    {x : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius) :
    ‖x‖ ≤ stateBound := by
  have hdist : ‖x - u₀‖ ≤ bpBootstrapRadius := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  calc
    ‖x‖ = ‖(x - u₀) + u₀‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - u₀‖ + ‖u₀‖ := norm_add_le _ _
    _ ≤ bpBootstrapRadius + 6 := add_le_add hdist u₀_norm_le_six
    _ = stateBound := by norm_num [bpBootstrapRadius, stateBound]

theorem component_norm_le_stateBound_of_mem_bpBall
    {x : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) (j : Fin 3) :
    ‖x k j‖ ≤ stateBound := by
  exact (norm_le_pi_norm (x k) j).trans
    ((norm_le_pi_norm x k).trans (norm_le_stateBound_of_mem_bpBall hx))

theorem component_diff_norm_le
    (x y : State) (k : Mode) (j : Fin 3) :
    ‖x k j - y k j‖ ≤ ‖x - y‖ := by
  exact (norm_le_pi_norm ((x - y) k) j).trans (norm_le_pi_norm (x - y) k)

/-- Critical weights are always one of 1,2,4. -/
theorem criticalWeight_nonneg (k : Mode) : 0 ≤ criticalWeight k := by
  unfold criticalWeight
  split_ifs <;> norm_num

theorem criticalWeight_le_four (k : Mode) : criticalWeight k ≤ 4 := by
  unfold criticalWeight
  split_ifs <;> norm_num

/-- One complex component of the quadratic energy changes by at most
2*R*||x-y|| on the B_P ball. -/
theorem component_sq_diff_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) (j : Fin 3) :
    ‖star (x k j) * x k j - star (y k j) * y k j‖
      ≤ 2 * stateBound * ‖x - y‖ := by
  have hxR := component_norm_le_stateBound_of_mem_bpBall hx k j
  have hyR := component_norm_le_stateBound_of_mem_bpBall hy k j
  have hd := component_diff_norm_le x y k j
  calc
    ‖star (x k j) * x k j - star (y k j) * y k j‖
        = ‖star (x k j - y k j) * x k j +
            star (y k j) * (x k j - y k j)‖ := by
          congr 1
          apply Complex.ext <;> simp <;> ring
    _ ≤ ‖star (x k j - y k j) * x k j‖ +
        ‖star (y k j) * (x k j - y k j)‖ := norm_add_le _ _
    _ = ‖x k j - y k j‖ * ‖x k j‖ +
        ‖y k j‖ * ‖x k j - y k j‖ := by
          simp [norm_mul]
    _ ≤ ‖x - y‖ * stateBound + stateBound * ‖x - y‖ := by
          gcongr
    _ = 2 * stateBound * ‖x - y‖ := by ring

/-- Modal Hermitian self-pairing real part has difference at most
6*R*||x-y||. -/
theorem hermitian_self_re_diff_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) :
    |(hermitianDot (x k) (x k)).re -
      (hermitianDot (y k) (y k)).re|
      ≤ 6 * stateBound * ‖x - y‖ := by
  have hnorm :
      ‖hermitianDot (x k) (x k) - hermitianDot (y k) (y k)‖
        ≤ 6 * stateBound * ‖x - y‖ := by
    unfold hermitianDot
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ j : Fin 3,
          (star (x k j) * x k j - star (y k j) * y k j)‖
          ≤ ∑ j : Fin 3,
              ‖star (x k j) * x k j - star (y k j) * y k j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, 2 * stateBound * ‖x - y‖ := by
        apply Finset.sum_le_sum
        intro j hj
        exact component_sq_diff_le hx hy k j
      _ = 6 * stateBound * ‖x - y‖ := by
        simp [Fin.sum_univ_succ]
        ring
  have hre :
      |(hermitianDot (x k) (x k) - hermitianDot (y k) (y k)).re|
        ≤ ‖hermitianDot (x k) (x k) - hermitianDot (y k) (y k)‖ :=
    Complex.abs_re_le_norm _
  simpa using hre.trans hnorm

/-- One modal critical-dissipation row is 1152*R-Lipschitz. -/
theorem modalDissipation_diff_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) :
    |modalDissipation x k - modalDissipation y k|
      ≤ 1152 * stateBound * ‖x - y‖ := by
  unfold modalDissipation
  have hw0 := criticalWeight_nonneg k
  have hw4 := criticalWeight_le_four k
  have hns0 := normSq_nonneg k
  have hns48 := normSq_le_48 k
  have hpair := hermitian_self_re_diff_le hx hy k
  rw [← mul_sub]
  rw [← mul_sub]
  rw [abs_mul, abs_mul]
  have hcoeff : |criticalWeight k| * |normSq k| ≤ 4 * 48 := by
    rw [abs_of_nonneg hw0, abs_of_nonneg hns0]
    gcongr
  calc
    |criticalWeight k| * |normSq k| *
        |(hermitianDot (x k) (x k)).re -
          (hermitianDot (y k) (y k)).re|
      ≤ (4 * 48) * (6 * stateBound * ‖x - y‖) := by
        gcongr
    _ = 1152 * stateBound * ‖x - y‖ := by ring

/-- The whole critical dissipation difference is closed. -/
theorem criticalDissipation_diff_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius) :
    |criticalDissipation x - criticalDissipation y|
      ≤ criticalDissipationLipschitzBound * ‖x - y‖ := by
  unfold criticalDissipation
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ k : Mode,
        ((if isZeroMode k then 0 else modalDissipation x k) -
         (if isZeroMode k then 0 else modalDissipation y k))|
      ≤ ∑ k : Mode,
          |(if isZeroMode k then 0 else modalDissipation x k) -
           (if isZeroMode k then 0 else modalDissipation y k)| := by
        exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Mode, 1152 * stateBound * ‖x - y‖ := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hz : isZeroMode k
      · simp [hz]
        positivity
      · simpa [hz] using modalDissipation_diff_le hx hy k
    _ = 729 * 1152 * stateBound * ‖x - y‖ := by
      rw [show Fintype.card Mode = 729 by native_decide]
      simp
      ring
    _ = criticalDissipationLipschitzBound * ‖x - y‖ := by
      rfl

/-- Remaining cubic leaf. -/
def ProductionLeaf : Prop :=
  ∀ x ∈ Metric.closedBall u₀ bpBootstrapRadius,
    ∀ y ∈ Metric.closedBall u₀ bpBootstrapRadius,
      |criticalProduction x - criticalProduction y|
        ≤ criticalProductionLipschitzBound * ‖x - y‖

/-- Remaining degree-five leaf. -/
def CoherentLeaf : Prop :=
  ∀ x ∈ Metric.closedBall u₀ bpBootstrapRadius,
    ∀ y ∈ Metric.closedBall u₀ bpBootstrapRadius,
      |globalCoherentWork x - globalCoherentWork y|
        ≤ globalCoherentLipschitzBound * ‖x - y‖

/-- The literal R815 normalization consumes the three component estimates. -/
theorem selectedRate_diff_le_budget
    (hC : CoherentLeaf)
    (hP : ProductionLeaf)
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius) :
    |selectedRate x - selectedRate y|
      ≤ selectedRateLipschitzBudget * ‖x - y‖ := by
  have hc := hC x hx y hy
  have hp := hP x hx y hy
  have hd := criticalDissipation_diff_le hx hy
  unfold selectedRate
  have htri :
      |6 * (12 * globalCoherentWork x - criticalProduction x + criticalDissipation x) -
       6 * (12 * globalCoherentWork y - criticalProduction y + criticalDissipation y)|
      ≤ 72 * |globalCoherentWork x - globalCoherentWork y| +
        6 * |criticalProduction x - criticalProduction y| +
        6 * |criticalDissipation x - criticalDissipation y| := by
    calc
      |6 * (12 * globalCoherentWork x - criticalProduction x + criticalDissipation x) -
       6 * (12 * globalCoherentWork y - criticalProduction y + criticalDissipation y)|
        = 6 * |12 * (globalCoherentWork x - globalCoherentWork y) -
          (criticalProduction x - criticalProduction y) +
          (criticalDissipation x - criticalDissipation y)| := by
            rw [← abs_of_nonneg (show (0:ℝ) ≤ 6 by norm_num)]
            rw [← abs_mul]
            congr 1
            ring
      _ ≤ 6 * (12 * |globalCoherentWork x - globalCoherentWork y| +
          |criticalProduction x - criticalProduction y| +
          |criticalDissipation x - criticalDissipation y|) := by
            gcongr
            calc
              |12 * (globalCoherentWork x - globalCoherentWork y) -
                (criticalProduction x - criticalProduction y) +
                (criticalDissipation x - criticalDissipation y)|
                ≤ |12 * (globalCoherentWork x - globalCoherentWork y) -
                    (criticalProduction x - criticalProduction y)| +
                  |criticalDissipation x - criticalDissipation y| := abs_add _ _
              _ ≤ (|12 * (globalCoherentWork x - globalCoherentWork y)| +
                    |criticalProduction x - criticalProduction y|) +
                  |criticalDissipation x - criticalDissipation y| := by
                    gcongr
                    exact abs_sub _ _
              _ = 12 * |globalCoherentWork x - globalCoherentWork y| +
                    |criticalProduction x - criticalProduction y| +
                    |criticalDissipation x - criticalDissipation y| := by
                    rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 12 by norm_num)]
                    ring
      _ = 72 * |globalCoherentWork x - globalCoherentWork y| +
          6 * |criticalProduction x - criticalProduction y| +
          6 * |criticalDissipation x - criticalDissipation y| := by ring
  calc
    |selectedRate x - selectedRate y|
      ≤ 72 * |globalCoherentWork x - globalCoherentWork y| +
          6 * |criticalProduction x - criticalProduction y| +
          6 * |criticalDissipation x - criticalDissipation y| := htri
    _ ≤ 72 * (globalCoherentLipschitzBound * ‖x - y‖) +
          6 * (criticalProductionLipschitzBound * ‖x - y‖) +
          6 * (criticalDissipationLipschitzBound * ‖x - y‖) := by
          gcongr
    _ = selectedRateLipschitzBudget * ‖x - y‖ := by
          unfold selectedRateLipschitzBudget
          ring

/-- Once the cubic and degree-five leaves land, the concrete B_P proposition
used by R830 is automatic. -/
theorem bpLeaf_of_two_leaves
    (hC : CoherentLeaf)
    (hP : ProductionLeaf) :
    BPLeaf := by
  intro x hx
  have habs := selectedRate_diff_le_budget hC hP hx
    (Metric.mem_closedBall_self (le_of_lt bpBootstrapRadius_pos))
  have hcert := selectedRateLipschitzBudget_le_certified
  calc
    selectedRate x - selectedRate u₀
      ≤ |selectedRate x - selectedRate u₀| := le_abs_self _
    _ ≤ selectedRateLipschitzBudget * ‖x - u₀‖ := habs
    _ ≤ rateLipschitzBound * ‖x - u₀‖ := by
      gcongr

end Rational345BPMaxCut
end NSBControl
