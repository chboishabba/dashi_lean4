import Mathlib.Tactic
import NSBControl.Rational345BPProduction

/-!
# B_P coherent-work max-cut

The degree-five R692 difference is separated from the lower-level helical
operator estimates.  Four finite vector inequalities are sufficient:

* fixed-output mixed value bound;
* fixed-output mixed difference bound;
* fixed-output forcing-commutator value bound;
* fixed-output forcing-commutator difference bound.

This file proves that those four leaves imply the complete global
`CoherentLeaf`.  No `sorry`, no alternate observable, and no giant monomial
expansion is used here.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345BPCoherent

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345BPBudget
open Rational345BPMaxCut
open Rational345BPProduction

classical

record CoherentOperatorLeaves : Prop where
  mixedValue :
    ∀ u ∈ Metric.closedBall u₀ bpBootstrapRadius,
      ∀ k : Mode,
        ‖fixedOutputMixed u k‖ ≤ mixedValueBound

  mixedDiff :
    ∀ x ∈ Metric.closedBall u₀ bpBootstrapRadius,
      ∀ y ∈ Metric.closedBall u₀ bpBootstrapRadius,
        ∀ k : Mode,
          ‖fixedOutputMixed x k - fixedOutputMixed y k‖
            ≤ mixedLipschitzBound * ‖x - y‖

  commutatorValue :
    ∀ u ∈ Metric.closedBall u₀ bpBootstrapRadius,
      ∀ k : Mode,
        ‖fixedOutputCommutator u (projectedNonlinearity u) k‖
          ≤ commutatorValueBound

  commutatorDiff :
    ∀ x ∈ Metric.closedBall u₀ bpBootstrapRadius,
      ∀ y ∈ Metric.closedBall u₀ bpBootstrapRadius,
        ∀ k : Mode,
          ‖fixedOutputCommutator x (projectedNonlinearity x) k -
            fixedOutputCommutator y (projectedNonlinearity y) k‖
            ≤ commutatorLipschitzBound * ‖x - y‖

/-- One coherent output row is controlled by the four structural leaves. -/
theorem outputCommutatorWork_diff_le
    (leaves : CoherentOperatorLeaves)
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) :
    |outputCommutatorWork x k - outputCommutatorWork y k|
      ≤ coherentOutputLipschitzBound * ‖x - y‖ := by
  let Mx := fixedOutputMixed x k
  let My := fixedOutputMixed y k
  let Gx := fixedOutputCommutator x (projectedNonlinearity x) k
  let Gy := fixedOutputCommutator y (projectedNonlinearity y) k

  have hMx : ‖Mx‖ ≤ mixedValueBound := leaves.mixedValue x hx k
  have hMy : ‖My‖ ≤ mixedValueBound := leaves.mixedValue y hy k
  have hMd : ‖Mx - My‖ ≤ mixedLipschitzBound * ‖x - y‖ :=
    leaves.mixedDiff x hx y hy k
  have hGx : ‖Gx‖ ≤ commutatorValueBound :=
    leaves.commutatorValue x hx k
  have hGd : ‖Gx - Gy‖ ≤ commutatorLipschitzBound * ‖x - y‖ :=
    leaves.commutatorDiff x hx y hy k

  have hpairIdentity :
      hermitianDot Mx Gx - hermitianDot My Gy =
        hermitianDot (Mx - My) Gx + hermitianDot My (Gx - Gy) := by
    unfold Mx My Gx Gy hermitianDot
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp
    ring

  have hpair1 :
      ‖hermitianDot (Mx - My) Gx‖
        ≤ 3 * (mixedLipschitzBound * ‖x - y‖) * commutatorValueBound := by
    apply hermitianDot_norm_le
    · intro j
      exact (norm_le_pi_norm (Mx - My) j).trans hMd
    · intro j
      exact (norm_le_pi_norm Gx j).trans hGx

  have hpair2 :
      ‖hermitianDot My (Gx - Gy)‖
        ≤ 3 * mixedValueBound *
            (commutatorLipschitzBound * ‖x - y‖) := by
    apply hermitianDot_norm_le
    · intro j
      exact (norm_le_pi_norm My j).trans hMy
    · intro j
      exact (norm_le_pi_norm (Gx - Gy) j).trans hGd

  unfold outputCommutatorWork coherentWork
  rw [← mul_sub]
  rw [hpairIdentity]
  calc
    |2 * (hermitianDot (Mx - My) Gx +
      hermitianDot My (Gx - Gy)).re|
      ≤ 2 * ‖hermitianDot (Mx - My) Gx +
        hermitianDot My (Gx - Gy)‖ := by
          rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
          gcongr
          exact Complex.abs_re_le_norm _
    _ ≤ 2 * (‖hermitianDot (Mx - My) Gx‖ +
      ‖hermitianDot My (Gx - Gy)‖) := by
        gcongr
        exact norm_add_le _ _
    _ ≤ 2 *
      (3 * (mixedLipschitzBound * ‖x - y‖) * commutatorValueBound +
       3 * mixedValueBound *
         (commutatorLipschitzBound * ‖x - y‖)) := by
        gcongr
    _ = coherentOutputLipschitzBound * ‖x - y‖ := by
      unfold coherentOutputLipschitzBound
      ring

/-- The four finite operator leaves imply the full degree-five global work
leaf used by the B_P compiler. -/
theorem coherentLeaf_of_operator_leaves
    (leaves : CoherentOperatorLeaves) : CoherentLeaf := by
  intro x hx y hy
  unfold globalCoherentWork
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ k : Mode,
      ((if isZeroMode k then 0 else outputCommutatorWork x k) -
       (if isZeroMode k then 0 else outputCommutatorWork y k))|
      ≤ ∑ k : Mode,
        |(if isZeroMode k then 0 else outputCommutatorWork x k) -
         (if isZeroMode k then 0 else outputCommutatorWork y k)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Mode,
        coherentOutputLipschitzBound * ‖x - y‖ := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hz : isZeroMode k
      · simp [hz]
        positivity
      · simpa [hz] using outputCommutatorWork_diff_le leaves hx hy k
    _ = 729 * coherentOutputLipschitzBound * ‖x - y‖ := by
      rw [show Fintype.card Mode = 729 by native_decide]
      simp
      ring
    _ = globalCoherentLipschitzBound * ‖x - y‖ := by
      unfold globalCoherentLipschitzBound
      ring

end Rational345BPCoherent
end NSBControl
