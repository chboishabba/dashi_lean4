import Mathlib.Tactic
import NSBControl.Rational345BQGeometry
import NSBControl.Rational345ShortTime

/-!
# B_Q coarse field bound on the radius-one bootstrap ball

The certified R828 component budget is intentionally very large.  We therefore
use only coarse finite bounds:

* bootstrap state component norm <= 7;
* |k_j| <= 4 and |k|^2 <= 48;
* one bilinear dot product <= 84;
* one raw ordered vector component <= 588;
* the finite integer Leray certificate gives a <= 5/2 component multiplier;
* for fixed p,k there is at most one resonant q in the radius-four cube;
* there are 9^3 = 729 choices of p.

This yields a field bound far below 5032512 without optimizing constants.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345BQFieldBound

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345BQGeometry
open Rational345ShortTime

classical

/-- The radius-four carrier has 729 modes. -/
theorem mode_card : Fintype.card Mode = 729 := by
  native_decide

/-- For fixed p,k, at most one q in the finite cube can solve p+q=k. -/
def resonantQs (p k : Mode) : Finset Mode :=
  Finset.univ.filter fun q => Resonates p q k

theorem resonantQs_card_le_one (p k : Mode) :
    (resonantQs p k).card ≤ 1 := by
  native_decide

/-- Sum of the absolute integer coordinates is at most 12. -/
theorem sumAbs_le_twelve (k : Mode) : sumAbs k ≤ 12 := by
  unfold sumAbs
  have h0 := axisInt_abs_le_four k.x
  have h1 := axisInt_abs_le_four k.y
  have h2 := axisInt_abs_le_four k.z
  fin_cases k <;> norm_num [absCoord, kInt, axisInt]

/-- The wavevector dot product against a bootstrap state has norm at most 84. -/
theorem bilinearDot_state_k_norm_le_84
    {x : State}
    (hx : x ∈ Metric.closedBall u₀ bootstrapRadius)
    (p q : Mode) :
    ‖bilinearDot (x p) (kComplex q)‖ ≤ 84 := by
  unfold bilinearDot
  calc
    ‖∑ j : Fin 3, x p j * kComplex q j‖
        ≤ ∑ j : Fin 3, ‖x p j * kComplex q j‖ := norm_sum_le _ _
    _ = ∑ j : Fin 3, ‖x p j‖ * |kReal q j| := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [kComplex, norm_mul]
    _ ≤ ∑ _j : Fin 3, 7 * 4 := by
      apply Finset.sum_le_sum
      intro j hj
      gcongr
      · exact component_norm_le_seven_of_mem_bootstrapBall hx p j
      · exact kReal_abs_le_four q j
    _ = 84 := by norm_num

/-- One unprojected ordered interaction component has norm at most 588. -/
theorem rawOrdered_component_norm_le_588
    {x : State}
    (hx : x ∈ Metric.closedBall u₀ bootstrapRadius)
    (p q : Mode) (j : Fin 3) :
    ‖bilinearDot (x p) (kComplex q) * x q j‖ ≤ 588 := by
  rw [norm_mul]
  calc
    ‖bilinearDot (x p) (kComplex q)‖ * ‖x q j‖
        ≤ 84 * 7 := mul_le_mul
          (bilinearDot_state_k_norm_le_84 hx p q)
          (component_norm_le_seven_of_mem_bootstrapBall hx q j)
          (norm_nonneg _) (by norm_num)
    _ = 588 := by norm_num

/-- Real form of the finite Leray ratio certificate.
For nonzero k, |k_j| * sum_l |k_l| / |k|^2 <= 3/2. -/
theorem leray_ratio_real
    (k : Mode) (j : Fin 3)
    (hk : ¬ isZeroMode k) :
    |kReal k j| *
        (|kReal k 0| + |kReal k 1| + |kReal k 2|) /
        normSq k ≤ (3 : ℝ) / 2 := by
  have hnat := leray_ratio_nat k j
  have hsqpos : 0 < normSq k := by
    have hnz : normSq k ≠ 0 := by
      intro hzero
      have h0 : kReal k 0 = 0 := by
        have hnon : 0 ≤ (kReal k 0)^2 := sq_nonneg _
        have hsum : (kReal k 0)^2 + (kReal k 1)^2 + (kReal k 2)^2 = 0 := by
          simpa [normSq, Fin.sum_univ_succ] using hzero
        nlinarith [sq_nonneg (kReal k 1), sq_nonneg (kReal k 2)]
      have h1 : kReal k 1 = 0 := by
        have hsum : (kReal k 0)^2 + (kReal k 1)^2 + (kReal k 2)^2 = 0 := by
          simpa [normSq, Fin.sum_univ_succ] using hzero
        nlinarith [sq_nonneg (kReal k 0), sq_nonneg (kReal k 2)]
      have h2 : kReal k 2 = 0 := by
        have hsum : (kReal k 0)^2 + (kReal k 1)^2 + (kReal k 2)^2 = 0 := by
          simpa [normSq, Fin.sum_univ_succ] using hzero
        nlinarith [sq_nonneg (kReal k 0), sq_nonneg (kReal k 1)]
      apply hk
      intro a
      fin_cases a
      · simpa [kReal] using h0
      · simpa [kReal] using h1
      · simpa [kReal] using h2
    exact lt_of_le_of_ne (by exact normSq_nonneg k) (Ne.symm hnz)
  have hcast :
      (2 : ℝ) * |kReal k j| *
          (|kReal k 0| + |kReal k 1| + |kReal k 2|)
        ≤ 3 * normSq k := by
    exact_mod_cast hnat
  apply (div_le_iff₀ hsqpos).2
  nlinarith

/-- Leray projection of one raw ordered vector costs at most 1470 per
component in the bootstrap ball. -/
theorem leray_raw_component_norm_le_1470
    {x : State}
    (hx : x ∈ Metric.closedBall u₀ bootstrapRadius)
    (p q k : Mode) (hk : ¬ isZeroMode k)
    (j : Fin 3) :
    ‖leray k (fun a => bilinearDot (x p) (kComplex q) * x q a) j‖ ≤ 1470 := by
  let raw : Vec3 := fun a => bilinearDot (x p) (kComplex q) * x q a
  have hraw : ∀ a : Fin 3, ‖raw a‖ ≤ 588 := by
    intro a
    exact rawOrdered_component_norm_le_588 hx p q a
  have hdot : ‖bilinearDot (kComplex k) raw‖ ≤
      (|kReal k 0| + |kReal k 1| + |kReal k 2|) * 588 := by
    unfold bilinearDot
    calc
      ‖∑ a : Fin 3, kComplex k a * raw a‖
          ≤ ∑ a : Fin 3, ‖kComplex k a * raw a‖ := norm_sum_le _ _
      _ = ∑ a : Fin 3, |kReal k a| * ‖raw a‖ := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [kComplex, norm_mul, mul_comm]
      _ ≤ ∑ a : Fin 3, |kReal k a| * 588 := by
        apply Finset.sum_le_sum
        intro a ha
        gcongr
        exact hraw a
      _ = (|kReal k 0| + |kReal k 1| + |kReal k 2|) * 588 := by
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
    _ ≤ 588 +
        (|kReal k j| *
          ((|kReal k 0| + |kReal k 1| + |kReal k 2|) * 588) /
          normSq k) := by
      gcongr
      · exact hraw j
      · rw [norm_mul, norm_div]
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (normSq_nonneg k)]
        gcongr
    _ ≤ 588 + ((3 : ℝ) / 2) * 588 := by
      gcongr
      calc
        |kReal k j| *
            ((|kReal k 0| + |kReal k 1| + |kReal k 2|) * 588) /
            normSq k
          = (|kReal k j| *
              (|kReal k 0| + |kReal k 1| + |kReal k 2|) /
              normSq k) * 588 := by ring
        _ ≤ ((3 : ℝ) / 2) * 588 := by gcongr
    _ = 1470 := by norm_num

/-- Each resonant projected ordered term has component norm at most 1470. -/
theorem projectedOrdered_component_norm_le_1470
    {x : State}
    (hx : x ∈ Metric.closedBall u₀ bootstrapRadius)
    (p q k : Mode) (j : Fin 3) :
    ‖projectedOrderedBilinear x x p q k j‖ ≤ 1470 := by
  unfold projectedOrderedBilinear
  split_ifs with hres
  · by_cases hk : isZeroMode k
    · have hzero : leray k
          (fun a => bilinearDot (x p) (kComplex q) * x q a) = 0 := by
        funext a
        simp [leray, hk]
      simp [hzero]
    · rw [norm_mul]
      simp only [norm_neg, Complex.norm_I, one_mul]
      exact leray_raw_component_norm_le_1470 hx p q k hk j
  · simp

/-- For fixed p,k, the q-sum has norm at most 1470 because there is at most
one resonant q. -/
theorem inner_q_sum_component_norm_le_1470
    {x : State}
    (hx : x ∈ Metric.closedBall u₀ bootstrapRadius)
    (p k : Mode) (j : Fin 3) :
    ‖∑ q : Mode, projectedOrderedBilinear x x p q k j‖ ≤ 1470 := by
  rw [← Finset.sum_filter]
  let s := resonantQs p k
  have hs : s.card ≤ 1 := resonantQs_card_le_one p k
  calc
    ‖∑ q in s, projectedOrderedBilinear x x p q k j‖
        ≤ ∑ q in s, ‖projectedOrderedBilinear x x p q k j‖ := norm_sum_le _ _
    _ ≤ ∑ _q in s, 1470 := by
      apply Finset.sum_le_sum
      intro q hq
      exact projectedOrdered_component_norm_le_1470 hx p q k j
    _ = s.card * 1470 := by simp
    _ ≤ 1 * 1470 := by gcongr
    _ = 1470 := by norm_num

/-- The complete projected nonlinearity component has norm at most
729*1470 = 1071630. -/
theorem projectedNonlinearity_component_norm_le
    {x : State}
    (hx : x ∈ Metric.closedBall u₀ bootstrapRadius)
    (k : Mode) (j : Fin 3) :
    ‖projectedNonlinearity x k j‖ ≤ 1071630 := by
  unfold projectedNonlinearity projectedBilinear
  split_ifs with hz
  · simp
  · calc
      ‖∑ p : Mode, ∑ q : Mode,
        projectedOrderedBilinear x x p q k j‖
          ≤ ∑ p : Mode,
              ‖∑ q : Mode, projectedOrderedBilinear x x p q k j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _p : Mode, 1470 := by
        apply Finset.sum_le_sum
        intro p hp
        exact inner_q_sum_component_norm_le_1470 hx p k j
      _ = (Fintype.card Mode : ℝ) * 1470 := by simp
      _ = 1071630 := by norm_num [mode_card]

/-- Viscous component norm is at most 48*7 = 336. -/
theorem viscous_component_norm_le_336
    {x : State}
    (hx : x ∈ Metric.closedBall u₀ bootstrapRadius)
    (k : Mode) (j : Fin 3) :
    ‖viscousLinear x k j‖ ≤ 336 := by
  unfold viscousLinear
  split_ifs with hz
  · simp
  · rw [norm_mul]
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (normSq_nonneg k)]
    calc
      normSq k * ‖x k j‖ ≤ 48 * 7 := mul_le_mul
        (normSq_le_48 k)
        (component_norm_le_seven_of_mem_bootstrapBall hx k j)
        (norm_nonneg _) (normSq_nonneg k)
      _ = 336 := by norm_num

/-- Coarse component bound for the actual literal field. -/
theorem galerkinField_component_norm_le
    {x : State}
    (hx : x ∈ Metric.closedBall u₀ bootstrapRadius)
    (k : Mode) (j : Fin 3) :
    ‖galerkinField x k j‖ ≤ 1071966 := by
  unfold galerkinField
  calc
    ‖viscousLinear x k j + projectedBilinear x x k j‖
        ≤ ‖viscousLinear x k j‖ + ‖projectedBilinear x x k j‖ := norm_add_le _ _
    _ ≤ 336 + 1071630 := by
      gcongr
      · exact viscous_component_norm_le_336 hx k j
      · simpa [projectedNonlinearity] using
          projectedNonlinearity_component_norm_le hx k j
    _ = 1071966 := by norm_num

/-- The state sup norm inherits the component bound. -/
theorem galerkinField_norm_le_coarse
    {x : State}
    (hx : x ∈ Metric.closedBall u₀ bootstrapRadius) :
    ‖galerkinField x‖ ≤ 1071966 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro k
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro j
  exact galerkinField_component_norm_le hx k j

/-- B_Q: the actual field is comfortably below the R828 certified budget. -/
theorem galerkinField_norm_le_certified
    {x : State}
    (hx : x ∈ Metric.closedBall u₀ bootstrapRadius) :
    ‖galerkinField x‖ ≤ odeComponentBound := by
  calc
    ‖galerkinField x‖ ≤ 1071966 := galerkinField_norm_le_coarse hx
    _ ≤ odeComponentBound := by norm_num [odeComponentBound]

end Rational345BQFieldBound
end NSBControl
