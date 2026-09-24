import Synthesis.RiemannNormalizedRvMMainRemainderCompiler
import Synthesis.RiemannNormalizedRvMSmoothMainDecomposition

/-!
# Cumulative RvM discrepancy -> Abel-prefix compiler

The existing normalized Abel consumer asks for prefix bounds on

  actualIncrement - mainIncrement.

For genuine counting increments this is not a new number-theoretic theorem.
If increments are successive differences of cumulative counting functions, the
prefix telescopes exactly:

  sum_{i<=k} (Delta N_i - Delta M_i) = N_k - M_k.

Therefore any theorem-bearing pointwise cumulative Riemann--von Mangoldt error

  |N_k - M_k| <= B

compiles directly into the prefix hypothesis required by
`FiniteRvMMainRemainderData`.

This file is application-neutral finite algebra.  It does not assert the zeta
RvM error theorem itself; it removes an unnecessary mismatch between the usual
external theorem shape and the repo's Abel consumer.
-/

noncomputable section

open scoped BigOperators

namespace Synthesis

/-- Successive increments of a cumulative sequence, with the zeroth increment
equal to the zeroth cumulative value. -/
def cumulativeIncrement (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | k + 1 => f (k + 1) - f k

theorem abelPrefix_cumulativeIncrement
    (f : ℕ → ℝ) (k : ℕ) :
    abelPrefix (cumulativeIncrement f) k = f k := by
  induction k with
  | zero =>
      simp [abelPrefix, cumulativeIncrement]
  | succ k ih =>
      rw [abelPrefix_succ, ih]
      simp [cumulativeIncrement]

theorem cumulativeIncrement_sub
    (f g : ℕ → ℝ) (k : ℕ) :
    cumulativeIncrement f k - cumulativeIncrement g k
      =
    cumulativeIncrement (fun i => f i - g i) k := by
  cases k with
  | zero =>
      simp [cumulativeIncrement]
  | succ k =>
      simp [cumulativeIncrement]
      ring

theorem abelPrefix_cumulative_discrepancy
    (actual main : ℕ → ℝ) (k : ℕ) :
    abelPrefix
        (fun i =>
          cumulativeIncrement actual i - cumulativeIncrement main i)
        k
      =
    actual k - main k := by
  have hfun :
      (fun i =>
        cumulativeIncrement actual i - cumulativeIncrement main i)
        =
      cumulativeIncrement (fun i => actual i - main i) := by
    funext i
    exact cumulativeIncrement_sub actual main i
  rw [hfun, abelPrefix_cumulativeIncrement]

record FiniteRvMCumulativeDiscrepancyProducer (n : ℕ) : Set where
  field
    actualCount : ℕ → ℝ
    mainCount : ℕ → ℝ
    testValue : ℕ → ℝ
    discrepancyBound : ℝ
    discrepancyBound_nonneg : 0 <= discrepancyBound
    cumulativeDiscrepancyBound :
      ∀ k, k <= n ->
        |actualCount k - mainCount k| <= discrepancyBound

open FiniteRvMCumulativeDiscrepancyProducer

/--
Compile an ordinary cumulative RvM discrepancy theorem into the exact
main/remainder package consumed by finite Abel summation.
-/
def cumulativeDiscrepancyToRvMMainRemainder
    {n : ℕ} (D : FiniteRvMCumulativeDiscrepancyProducer n) :
    FiniteRvMMainRemainderData n where
  actualIncrement := cumulativeIncrement D.actualCount
  mainIncrement := cumulativeIncrement D.mainCount
  testValue := D.testValue
  remainderBound := D.discrepancyBound
  remainderBound_nonneg := D.discrepancyBound_nonneg
  remainderPrefixBound := by
    intro k hk
    rw [abelPrefix_cumulative_discrepancy]
    exact D.cumulativeDiscrepancyBound k hk

theorem cumulativeRvM_actualPair_le_main_add_budget
    {n : ℕ} (D : FiniteRvMCumulativeDiscrepancyProducer n) :
    finiteActualPair (cumulativeDiscrepancyToRvMMainRemainder D)
      <=
    finiteMainPair (cumulativeDiscrepancyToRvMMainRemainder D)
      +
    D.discrepancyBound * abelVariation D.testValue n := by
  exact finiteActualPair_le_main_add_remainder_budget
    (cumulativeDiscrepancyToRvMMainRemainder D)

/--
If the smooth main pairing has already been bounded (or exactly cancelled),
a pointwise cumulative RvM discrepancy theorem is sufficient for the whole
finite normalized counting pair.
-/
theorem cumulativeRvM_actualPair_le_of_mainPair_le
    {n : ℕ} (D : FiniteRvMCumulativeDiscrepancyProducer n)
    {mainUpper : ℝ}
    (hmain :
      finiteMainPair (cumulativeDiscrepancyToRvMMainRemainder D)
        <= mainUpper) :
    finiteActualPair (cumulativeDiscrepancyToRvMMainRemainder D)
      <=
    mainUpper + D.discrepancyBound * abelVariation D.testValue n := by
  exact finiteActualPair_le_of_mainPair_le
    (cumulativeDiscrepancyToRvMMainRemainder D) hmain

end Synthesis
