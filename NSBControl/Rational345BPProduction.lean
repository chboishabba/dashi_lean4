import Mathlib.Tactic
import NSBControl.Rational345RealRadius4Quadratic
import NSBControl.Rational345BQFieldBound
import NSBControl.Rational345BPMaxCut

/-!
# B_P cubic critical-production leaf

This file proves the explicit finite bilinear estimate

  ||B(a,b)||_∞ <= 21870 ||a||_∞ ||b||_∞

for the literal radius-four projected convolution.  Bilinearity then yields

  B(x,x)-B(y,y) = B(x-y,x)+B(y,x-y),

which closes the critical-production difference on the B_P bootstrap ball.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345BPProduction

open Rational345RealRadius4
open Rational345RealRadius4Quadratic
open Rational345RealInitialState
open Rational345BQGeometry
open Rational345BQFieldBound
open Rational345BPBudget
open Rational345BPMaxCut

classical

/-- A scalar component of a state is controlled by the state sup norm. -/
theorem component_norm_le_state_norm
    (x : State) (k : Mode) (j : Fin 3) :
    ‖x k j‖ ≤ ‖x‖ := by
  exact (norm_le_pi_norm (x k) j).trans (norm_le_pi_norm x k)

/-- Dotting any state coefficient with a radius-four wavevector costs at most
12 times the state sup norm. -/
theorem bilinearDot_state_k_norm_le
    (x : State) (p q : Mode) :
    ‖bilinearDot (x p) (kComplex q)‖ ≤ 12 * ‖x‖ := by
  unfold bilinearDot
  calc
    ‖∑ j : Fin 3, x p j * kComplex q j‖
      ≤ ∑ j : Fin 3, ‖x p j * kComplex q j‖ := norm_sum_le _ _
    _ = ∑ j : Fin 3, ‖x p j‖ * |kReal q j| := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [kComplex, norm_mul]
    _ ≤ ∑ _j : Fin 3, ‖x‖ * 4 := by
      apply Finset.sum_le_sum
      intro j hj
      gcongr
      · exact component_norm_le_state_norm x p j
      · exact kReal_abs_le_four q j
    _ = 12 * ‖x‖ := by
      simp [Fin.sum_univ_succ]
      ring

/-- One raw bilinear interaction component costs at most 12||a||||b||. -/
theorem rawBilinear_component_norm_le
    (left right : State) (p q : Mode) (j : Fin 3) :
    ‖bilinearDot (left p) (kComplex q) * right q j‖
      ≤ 12 * ‖left‖ * ‖right‖ := by
  rw [norm_mul]
  calc
    ‖bilinearDot (left p) (kComplex q)‖ * ‖right q j‖
      ≤ (12 * ‖left‖) * ‖right‖ := by
        gcongr
        · exact bilinearDot_state_k_norm_le left p q
        · exact component_norm_le_state_norm right q j
    _ = 12 * ‖left‖ * ‖right‖ := by ring

/-- The Leray projection costs at most a factor 5/2 componentwise. -/
theorem leray_raw_bilinear_component_norm_le
    (left right : State) (p q k : Mode)
    (hk : ¬ isZeroMode k) (j : Fin 3) :
    ‖leray k
      (fun a => bilinearDot (left p) (kComplex q) * right q a) j‖
      ≤ 30 * ‖left‖ * ‖right‖ := by
  let raw : Vec3 := fun a =>
    bilinearDot (left p) (kComplex q) * right q a
  have hraw : ∀ a : Fin 3,
      ‖raw a‖ ≤ 12 * ‖left‖ * ‖right‖ := by
    intro a
    exact rawBilinear_component_norm_le left right p q a
  have hdot :
      ‖bilinearDot (kComplex k) raw‖ ≤
        (|kReal k 0| + |kReal k 1| + |kReal k 2|) *
          (12 * ‖left‖ * ‖right‖) := by
    unfold bilinearDot
    calc
      ‖∑ a : Fin 3, kComplex k a * raw a‖
        ≤ ∑ a : Fin 3, ‖kComplex k a * raw a‖ := norm_sum_le _ _
      _ = ∑ a : Fin 3, |kReal k a| * ‖raw a‖ := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [kComplex, norm_mul, mul_comm]
      _ ≤ ∑ a : Fin 3,
          |kReal k a| * (12 * ‖left‖ * ‖right‖) := by
        apply Finset.sum_le_sum
        intro a ha
        gcongr
        exact hraw a
      _ = (|kReal k 0| + |kReal k 1| + |kReal k 2|) *
          (12 * ‖left‖ * ‖right‖) := by
        simp [Fin.sum_univ_succ]
        ring
  have hratio := leray_ratio_real k j hk
  unfold leray
  simp only [if_neg hk]
  calc
    ‖raw j - (kReal k j : ℂ) *
      (bilinearDot (kComplex k) raw / (normSq k : ℂ))‖
      ≤ ‖raw j‖ + ‖(kReal k j : ℂ) *
        (bilinearDot (kComplex k) raw / (normSq k : ℂ))‖ := norm_sub_le _ _
    _ ≤ 12 * ‖left‖ * ‖right‖ +
        |kReal k j| *
          ((|kReal k 0| + |kReal k 1| + |kReal k 2|) *
            (12 * ‖left‖ * ‖right‖)) / normSq k := by
      gcongr
      · exact hraw j
      · rw [norm_mul, norm_div]
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (normSq_nonneg k)]
        gcongr
    _ ≤ 12 * ‖left‖ * ‖right‖ +
        ((3 : ℝ) / 2) * (12 * ‖left‖ * ‖right‖) := by
      gcongr
      calc
        |kReal k j| *
            ((|kReal k 0| + |kReal k 1| + |kReal k 2|) *
              (12 * ‖left‖ * ‖right‖)) / normSq k
          = (|kReal k j| *
              (|kReal k 0| + |kReal k 1| + |kReal k 2|) /
              normSq k) * (12 * ‖left‖ * ‖right‖) := by ring
        _ ≤ ((3 : ℝ) / 2) * (12 * ‖left‖ * ‖right‖) := by
          gcongr
    _ = 30 * ‖left‖ * ‖right‖ := by ring

/-- One projected ordered term is bounded by 30||a||||b||. -/
theorem projectedOrdered_component_norm_le
    (left right : State) (p q k : Mode) (j : Fin 3) :
    ‖projectedOrderedBilinear left right p q k j‖
      ≤ 30 * ‖left‖ * ‖right‖ := by
  unfold projectedOrderedBilinear
  split_ifs with hres
  · by_cases hk : isZeroMode k
    · have hzero : leray k
          (fun a => bilinearDot (left p) (kComplex q) * right q a) = 0 := by
        funext a
        simp [leray, hk]
      simp [hzero]
      positivity
    · rw [norm_mul]
      simp only [norm_neg, Complex.norm_I, one_mul]
      exact leray_raw_bilinear_component_norm_le left right p q k hk j
  · simp
    positivity

/-- For fixed p,k, resonance uniqueness leaves at most one q. -/
theorem inner_q_sum_component_norm_le
    (left right : State) (p k : Mode) (j : Fin 3) :
    ‖∑ q : Mode, projectedOrderedBilinear left right p q k j‖
      ≤ 30 * ‖left‖ * ‖right‖ := by
  let s := resonantQs p k
  have hs : s.card ≤ 1 := resonantQs_card_le_one p k
  have hfilter :
      (∑ q : Mode, projectedOrderedBilinear left right p q k j) =
      ∑ q in s, projectedOrderedBilinear left right p q k j := by
    unfold s resonantQs
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    simp only [Finset.mem_univ, true_and] at hq
    by_cases hr : Resonates p q k
    · simp [hr]
    · simp [projectedOrderedBilinear, hr]
  rw [hfilter]
  calc
    ‖∑ q in s, projectedOrderedBilinear left right p q k j‖
      ≤ ∑ q in s, ‖projectedOrderedBilinear left right p q k j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _q in s, 30 * ‖left‖ * ‖right‖ := by
      apply Finset.sum_le_sum
      intro q hq
      exact projectedOrdered_component_norm_le left right p q k j
    _ = s.card * (30 * ‖left‖ * ‖right‖) := by simp
    _ ≤ 1 * (30 * ‖left‖ * ‖right‖) := by
      gcongr
      positivity
    _ = 30 * ‖left‖ * ‖right‖ := by ring

/-- Explicit finite operator norm for the radius-four projected convolution. -/
theorem projectedBilinear_component_norm_le
    (left right : State) (k : Mode) (j : Fin 3) :
    ‖projectedBilinear left right k j‖
      ≤ projectedBilinearConstant * ‖left‖ * ‖right‖ := by
  unfold projectedBilinear
  split_ifs with hz
  · simp [projectedBilinearConstant]
    positivity
  · calc
      ‖∑ p : Mode, ∑ q : Mode,
        projectedOrderedBilinear left right p q k j‖
        ≤ ∑ p : Mode,
            ‖∑ q : Mode,
              projectedOrderedBilinear left right p q k j‖ := norm_sum_le _ _
      _ ≤ ∑ _p : Mode, 30 * ‖left‖ * ‖right‖ := by
        apply Finset.sum_le_sum
        intro p hp
        exact inner_q_sum_component_norm_le left right p k j
      _ = (Fintype.card Mode : ℝ) * (30 * ‖left‖ * ‖right‖) := by simp
      _ = projectedBilinearConstant * ‖left‖ * ‖right‖ := by
        norm_num [show Fintype.card Mode = 729 by native_decide,
          projectedBilinearConstant]
        ring

/-- State sup-norm form of the bilinear bound. -/
theorem projectedBilinear_norm_le
    (left right : State) :
    ‖projectedBilinear left right‖
      ≤ projectedBilinearConstant * ‖left‖ * ‖right‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro k
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  exact projectedBilinear_component_norm_le left right k j

lemma projectedBilinear_sub_left (x y z : State) :
    projectedBilinear (x - y) z =
      projectedBilinear x z - projectedBilinear y z := by
  rw [sub_eq_add_neg, projectedBilinear_add_left]
  have hneg : projectedBilinear (-y) z = -projectedBilinear y z := by
    simpa using projectedBilinear_smul_left (-1 : ℂ) y z
  rw [hneg]
  rfl

lemma projectedBilinear_sub_right (x y z : State) :
    projectedBilinear x (y - z) =
      projectedBilinear x y - projectedBilinear x z := by
  rw [sub_eq_add_neg, projectedBilinear_add_right]
  have hneg : projectedBilinear x (-z) = -projectedBilinear x z := by
    simpa using projectedBilinear_smul_right (-1 : ℂ) x z
  rw [hneg]
  rfl

/-- Exact quadratic difference identity. -/
theorem projectedNonlinearity_sub_identity (x y : State) :
    projectedNonlinearity x - projectedNonlinearity y =
      projectedBilinear (x - y) x +
      projectedBilinear y (x - y) := by
  rw [projectedNonlinearity_eq_bilinear_diag,
      projectedNonlinearity_eq_bilinear_diag]
  rw [projectedBilinear_sub_left, projectedBilinear_sub_right]
  abel

/-- Value bound on the B_P ball. -/
theorem forcing_norm_le
    {x : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius) :
    ‖projectedNonlinearity x‖ ≤ forcingValueBound := by
  rw [projectedNonlinearity_eq_bilinear_diag]
  calc
    ‖projectedBilinear x x‖
      ≤ projectedBilinearConstant * ‖x‖ * ‖x‖ := projectedBilinear_norm_le x x
    _ ≤ projectedBilinearConstant * stateBound * stateBound := by
      gcongr
      all_goals exact norm_le_stateBound_of_mem_bpBall hx
    _ = forcingValueBound := by
      unfold forcingValueBound
      ring

/-- Quadratic forcing difference bound on the B_P ball. -/
theorem forcing_diff_norm_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius) :
    ‖projectedNonlinearity x - projectedNonlinearity y‖
      ≤ forcingLipschitzBound * ‖x - y‖ := by
  rw [projectedNonlinearity_sub_identity]
  calc
    ‖projectedBilinear (x - y) x +
      projectedBilinear y (x - y)‖
      ≤ ‖projectedBilinear (x - y) x‖ +
        ‖projectedBilinear y (x - y)‖ := norm_add_le _ _
    _ ≤ projectedBilinearConstant * ‖x - y‖ * ‖x‖ +
        projectedBilinearConstant * ‖y‖ * ‖x - y‖ := by
      gcongr
      · exact projectedBilinear_norm_le (x - y) x
      · exact projectedBilinear_norm_le y (x - y)
    _ ≤ projectedBilinearConstant * ‖x - y‖ * stateBound +
        projectedBilinearConstant * stateBound * ‖x - y‖ := by
      gcongr
      · exact norm_le_stateBound_of_mem_bpBall hx
      · exact norm_le_stateBound_of_mem_bpBall hy
    _ = forcingLipschitzBound * ‖x - y‖ := by
      unfold forcingLipschitzBound
      ring

/-- Three-component Hermitian pairing is bounded by 3||a||||b||. -/
theorem hermitianDot_norm_le
    (a b : Vec3)
    (ha : ∀ j : Fin 3, ‖a j‖ ≤ A)
    (hb : ∀ j : Fin 3, ‖b j‖ ≤ B) :
    ‖hermitianDot a b‖ ≤ 3 * A * B := by
  unfold hermitianDot
  calc
    ‖∑ j : Fin 3, star (a j) * b j‖
      ≤ ∑ j : Fin 3, ‖star (a j) * b j‖ := norm_sum_le _ _
    _ = ∑ j : Fin 3, ‖a j‖ * ‖b j‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [norm_mul]
    _ ≤ ∑ _j : Fin 3, A * B := by
      apply Finset.sum_le_sum
      intro j hj
      gcongr
      · exact ha j
      · exact hb j
    _ = 3 * A * B := by
      simp [Fin.sum_univ_succ]
      ring

/-- One production row is controlled by forcing value + forcing difference. -/
theorem modalProduction_diff_le
    {x y : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (hy : y ∈ Metric.closedBall u₀ bpBootstrapRadius)
    (k : Mode) :
    |modalProduction x k - modalProduction y k|
      ≤ 24 * (forcingValueBound +
          stateBound * forcingLipschitzBound) * ‖x - y‖ := by
  have hweight0 := criticalWeight_nonneg k
  have hweight4 := criticalWeight_le_four k
  have hxR := norm_le_stateBound_of_mem_bpBall hx
  have hyR := norm_le_stateBound_of_mem_bpBall hy
  have hF := forcing_norm_le hx
  have hDF := forcing_diff_norm_le hx hy
  have hpair1 :
      ‖hermitianDot ((x - y) k) (projectedNonlinearity x k)‖
        ≤ 3 * ‖x - y‖ * forcingValueBound := by
    apply hermitianDot_norm_le
    · intro j
      exact component_norm_le_state_norm (x - y) k j
    · intro j
      exact (component_norm_le_state_norm (projectedNonlinearity x) k j).trans hF
  have hpair2 :
      ‖hermitianDot (y k)
        ((projectedNonlinearity x - projectedNonlinearity y) k)‖
        ≤ 3 * stateBound * (forcingLipschitzBound * ‖x - y‖) := by
    apply hermitianDot_norm_le
    · intro j
      exact (component_norm_le_state_norm y k j).trans hyR
    · intro j
      exact (component_norm_le_state_norm
        (projectedNonlinearity x - projectedNonlinearity y) k j).trans hDF
  have hid :
      hermitianDot (x k) (projectedNonlinearity x k) -
        hermitianDot (y k) (projectedNonlinearity y k) =
      hermitianDot ((x - y) k) (projectedNonlinearity x k) +
        hermitianDot (y k)
          ((projectedNonlinearity x - projectedNonlinearity y) k) := by
    unfold hermitianDot
    rw [← Finset.sum_sub_distrib]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp
    ring
  unfold modalProduction
  rw [← mul_sub]
  rw [← mul_sub]
  rw [hid]
  have hre :
      |(hermitianDot ((x - y) k) (projectedNonlinearity x k) +
          hermitianDot (y k)
            ((projectedNonlinearity x - projectedNonlinearity y) k)).re|
      ≤ 3 * ‖x - y‖ * forcingValueBound +
          3 * stateBound * (forcingLipschitzBound * ‖x - y‖) := by
    calc
      |(hermitianDot ((x - y) k) (projectedNonlinearity x k) +
          hermitianDot (y k)
            ((projectedNonlinearity x - projectedNonlinearity y) k)).re|
        ≤ ‖hermitianDot ((x - y) k) (projectedNonlinearity x k) +
          hermitianDot (y k)
            ((projectedNonlinearity x - projectedNonlinearity y) k)‖ :=
          Complex.abs_re_le_norm _
      _ ≤ ‖hermitianDot ((x - y) k) (projectedNonlinearity x k)‖ +
          ‖hermitianDot (y k)
            ((projectedNonlinearity x - projectedNonlinearity y) k)‖ :=
          norm_add_le _ _
      _ ≤ 3 * ‖x - y‖ * forcingValueBound +
          3 * stateBound * (forcingLipschitzBound * ‖x - y‖) := by
          gcongr
  rw [abs_mul, abs_mul]
  have hcoeff : |2| * |criticalWeight k| ≤ 8 := by
    norm_num
    rw [abs_of_nonneg hweight0]
    linarith
  calc
    |2| * |criticalWeight k| *
        |(hermitianDot ((x - y) k) (projectedNonlinearity x k) +
          hermitianDot (y k)
            ((projectedNonlinearity x - projectedNonlinearity y) k)).re|
      ≤ 8 *
        (3 * ‖x - y‖ * forcingValueBound +
          3 * stateBound * (forcingLipschitzBound * ‖x - y‖)) := by
        gcongr
    _ = 24 * (forcingValueBound + stateBound * forcingLipschitzBound) *
        ‖x - y‖ := by ring

/-- Cubic production leaf closed. -/
theorem productionLeaf_closed : ProductionLeaf := by
  intro x hx y hy
  unfold criticalProduction
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ k : Mode,
      ((if isZeroMode k then 0 else modalProduction x k) -
       (if isZeroMode k then 0 else modalProduction y k))|
      ≤ ∑ k : Mode,
        |(if isZeroMode k then 0 else modalProduction x k) -
         (if isZeroMode k then 0 else modalProduction y k)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Mode,
        24 * (forcingValueBound + stateBound * forcingLipschitzBound) *
          ‖x - y‖ := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hz : isZeroMode k
      · simp [hz]
        positivity
      · simpa [hz] using modalProduction_diff_le hx hy k
    _ = 729 * 24 *
        (forcingValueBound + stateBound * forcingLipschitzBound) *
          ‖x - y‖ := by
      rw [show Fintype.card Mode = 729 by native_decide]
      simp
      ring
    _ = criticalProductionLipschitzBound * ‖x - y‖ := by
      rfl

end Rational345BPProduction
end NSBControl
