import Synthesis.RiemannNormalizedZeroCountingStieltjes

/-!
# Finite Abel compiler for the normalized zero-counting remainder

The live H2 aggregate is a target-centred spectral-measure problem. The
repository currently owns an unconditional local upper count, but it does not
own a Riemann--von Mangoldt main-term/error theorem strong enough to control the
required phase sum.

For weights w_i and test values phi_i, let

  P_k = sum_{i <= k} w_i.

Then for every n,

  sum_{i=0}^n w_i phi_i
    = P_n phi_n
      + sum_{i=0}^{n-1} P_i (phi_i - phi_{i+1}).

Consequently, if |P_i| <= B for every prefix,

  |sum w_i phi_i|
    <= B * ( |phi_n| + sum |phi_i-phi_{i+1}| ).

This is the finite atomic Stieltjes / Abel summation inequality needed after
subtracting a smooth zero-counting main term. It deliberately does not assert
the missing RvM remainder bound; it makes that analytic input explicit.
-/

noncomputable section

open scoped BigOperators

namespace Synthesis

def abelPrefix (w : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), w i

theorem abelPrefix_zero (w : ℕ → ℝ) :
    abelPrefix w 0 = w 0 := by
  simp [abelPrefix]

theorem abelPrefix_succ (w : ℕ → ℝ) (k : ℕ) :
    abelPrefix w (k + 1) = abelPrefix w k + w (k + 1) := by
  unfold abelPrefix
  rw [show k + 1 + 1 = (k + 1) + 1 by omega,
      Finset.sum_range_succ]
  rfl

/-- Exact finite summation by parts on indices 0,...,n. -/
theorem finite_abel_sum_range_succ
    (w phi : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), w i * phi i)
      =
    abelPrefix w n * phi n
      +
    ∑ i ∈ Finset.range n,
      abelPrefix w i * (phi i - phi (i + 1)) := by
  induction n with
  | zero =>
      simp [abelPrefix]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, abelPrefix_succ,
        Finset.sum_range_succ]
      ring

def abelVariation (phi : ℕ → ℝ) (n : ℕ) : ℝ :=
  |phi n| + ∑ i ∈ Finset.range n, |phi i - phi (i + 1)|

theorem abelVariation_nonneg (phi : ℕ → ℝ) (n : ℕ) :
    0 <= abelVariation phi n := by
  unfold abelVariation
  positivity

/--
Finite Stieltjes remainder bound from a uniform cumulative discrepancy bound.

No zero-distribution theorem is assumed here: the prefix hypothesis is exactly
the analytic input that a genuine normalized RvM remainder theorem must provide.
-/
theorem abs_weighted_sum_le_prefix_bound_mul_variation
    {w phi : ℕ → ℝ} {n : ℕ} {B : ℝ}
    (hB : 0 <= B)
    (hprefix : ∀ k, k <= n -> |abelPrefix w k| <= B) :
    |∑ i ∈ Finset.range (n + 1), w i * phi i|
      <= B * abelVariation phi n := by
  rw [finite_abel_sum_range_succ]
  have htri :
      |abelPrefix w n * phi n
        + ∑ i ∈ Finset.range n,
          abelPrefix w i * (phi i - phi (i + 1))|
      <=
      |abelPrefix w n * phi n|
        +
      |∑ i ∈ Finset.range n,
        abelPrefix w i * (phi i - phi (i + 1))| :=
    abs_add _ _
  have hsumabs :
      |∑ i ∈ Finset.range n,
        abelPrefix w i * (phi i - phi (i + 1))|
      <=
      ∑ i ∈ Finset.range n,
        |abelPrefix w i * (phi i - phi (i + 1))| :=
    Finset.abs_sum_le_sum_abs _ _
  have hend :
      |abelPrefix w n * phi n| <= B * |phi n| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hprefix n le_rfl) (abs_nonneg _)
  have hterms :
      ∑ i ∈ Finset.range n,
        |abelPrefix w i * (phi i - phi (i + 1))|
      <=
      ∑ i ∈ Finset.range n,
        B * |phi i - phi (i + 1)| := by
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_mul]
    have hin : i < n := Finset.mem_range.mp hi
    have hin' : i <= n := Nat.le_trans (Nat.le_of_lt hin) (Nat.le_succ n)
    exact mul_le_mul_of_nonneg_right
      (hprefix i hin') (abs_nonneg _)
  calc
    |abelPrefix w n * phi n
      + ∑ i ∈ Finset.range n,
        abelPrefix w i * (phi i - phi (i + 1))|
      <=
      |abelPrefix w n * phi n|
        +
      |∑ i ∈ Finset.range n,
        abelPrefix w i * (phi i - phi (i + 1))| := htri
    _ <=
      B * |phi n|
        +
      ∑ i ∈ Finset.range n,
        |abelPrefix w i * (phi i - phi (i + 1))| := by
          linarith
    _ <=
      B * |phi n|
        +
      ∑ i ∈ Finset.range n,
        B * |phi i - phi (i + 1)| := by
          gcongr
    _ =
      B * abelVariation phi n := by
        unfold abelVariation
        rw [Finset.mul_sum]
        ring

/--
The theorem-facing finite normalized counting-remainder package.

The weight is intended to be the increment of actual normalized zero count
minus a smooth RvM main count on an ordered q-grid. The prefix bound is exactly
the cumulative remainder estimate.
-/
record FiniteNormalizedCountingRemainder (n : ℕ) : Set where
  field
    weight : ℕ → ℝ
    testValue : ℕ → ℝ
    remainderBound : ℝ
    remainderBound_nonneg : 0 <= remainderBound
    prefixBound :
      ∀ k, k <= n -> |abelPrefix weight k| <= remainderBound

open FiniteNormalizedCountingRemainder

theorem finiteNormalizedCountingRemainder_pair_bound
    {n : ℕ} (R : FiniteNormalizedCountingRemainder n) :
    |∑ i ∈ Finset.range (n + 1), R.weight i * R.testValue i|
      <=
    R.remainderBound * abelVariation R.testValue n :=
  abs_weighted_sum_le_prefix_bound_mul_variation
    R.remainderBound_nonneg R.prefixBound

end Synthesis
