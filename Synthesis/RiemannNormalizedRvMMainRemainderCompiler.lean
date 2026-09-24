import Synthesis.RiemannNormalizedCountingAbelCompiler

/-!
# RvM main/remainder compiler for the normalized H2 aggregate

The normalized q-counting problem has two logically distinct pieces:

  actual count increment = smooth RvM main increment + remainder increment.

This file keeps that split exact before any absolute value.

For an ordered finite q-grid:

  A = sum actual_i * phi_i
  M = sum main_i   * phi_i
  E = sum (actual_i-main_i) * phi_i.

Then A = M + E exactly. If cumulative remainder prefixes are bounded by B,
the finite Abel compiler gives

  |E| <= B * Var(phi).

Thus the smooth main term remains signed and available for Fourier cancellation;
only the genuine counting remainder is majorized.

This file does NOT assert an RvM main term or remainder estimate for zeta. It is
the exact consumer those theorem-bearing inputs must inhabit.
-/

noncomputable section

open scoped BigOperators

namespace Synthesis

record FiniteRvMMainRemainderData (n : ℕ) : Set where
  field
    actualIncrement : ℕ → ℝ
    mainIncrement : ℕ → ℝ
    testValue : ℕ → ℝ
    remainderBound : ℝ
    remainderBound_nonneg : 0 <= remainderBound
    remainderPrefixBound :
      ∀ k, k <= n ->
        |abelPrefix
          (fun i => actualIncrement i - mainIncrement i) k|
          <= remainderBound

open FiniteRvMMainRemainderData

def finiteActualPair {n : ℕ} (D : FiniteRvMMainRemainderData n) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), D.actualIncrement i * D.testValue i

def finiteMainPair {n : ℕ} (D : FiniteRvMMainRemainderData n) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), D.mainIncrement i * D.testValue i

def finiteRemainderPair {n : ℕ} (D : FiniteRvMMainRemainderData n) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (D.actualIncrement i - D.mainIncrement i) * D.testValue i

theorem finiteActualPair_eq_main_add_remainder
    {n : ℕ} (D : FiniteRvMMainRemainderData n) :
    finiteActualPair D = finiteMainPair D + finiteRemainderPair D := by
  unfold finiteActualPair finiteMainPair finiteRemainderPair
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finiteRemainderPair_abs_le
    {n : ℕ} (D : FiniteRvMMainRemainderData n) :
    |finiteRemainderPair D|
      <=
    D.remainderBound * abelVariation D.testValue n := by
  unfold finiteRemainderPair
  exact abs_weighted_sum_le_prefix_bound_mul_variation
    D.remainderBound_nonneg D.remainderPrefixBound

theorem finiteActualPair_sub_main_abs_le
    {n : ℕ} (D : FiniteRvMMainRemainderData n) :
    |finiteActualPair D - finiteMainPair D|
      <=
    D.remainderBound * abelVariation D.testValue n := by
  rw [finiteActualPair_eq_main_add_remainder]
  ring_nf
  exact finiteRemainderPair_abs_le D

/--
One-sided form suited to the H2 comparison: preserve the main term with its
sign and pay only the remainder variation budget.
-/
theorem finiteActualPair_le_main_add_remainder_budget
    {n : ℕ} (D : FiniteRvMMainRemainderData n) :
    finiteActualPair D
      <=
    finiteMainPair D
      + D.remainderBound * abelVariation D.testValue n := by
  have h := finiteActualPair_sub_main_abs_le D
  have hdir :
      finiteActualPair D - finiteMainPair D
        <= |finiteActualPair D - finiteMainPair D| :=
    le_abs_self _
  linarith

/--
If a separate Fourier argument supplies an upper bound on the signed smooth
main pairing, this compiler immediately combines it with the RvM remainder
budget.
-/
theorem finiteActualPair_le_of_mainPair_le
    {n : ℕ} (D : FiniteRvMMainRemainderData n)
    {mainUpper : ℝ}
    (hmain : finiteMainPair D <= mainUpper) :
    finiteActualPair D
      <=
    mainUpper + D.remainderBound * abelVariation D.testValue n := by
  exact le_trans
    (finiteActualPair_le_main_add_remainder_budget D)
    (add_le_add_right hmain _)

end Synthesis
