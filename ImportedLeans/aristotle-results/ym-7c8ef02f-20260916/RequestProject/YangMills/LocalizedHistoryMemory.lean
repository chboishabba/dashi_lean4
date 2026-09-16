/-
# Row A1b — localized irrelevant memory, and the marginal exception

The Row A1 history debt needs a uniform bound on the total memory
`∑_{k<j} |R_{j,k}|`.  The physically available producer is *scale-local
localization*: an irrelevant (polymer) memory kernel inherits a scale-local
majorant `|R^{irr}_{j,k}| ≤ C_loc·γ·θ^{j−k}` with `θ < 1`, and this is uniform
in the history length.

Two things are proved here, and it is important that they are separate.

* `irrelevantMemory_sum_le` / `irrelevantMemory_le_CH_half` : the localized
  irrelevant memory is bounded by `C_loc γ θ/(1−θ)`, uniformly in the shell
  index `j` — i.e. `H_irr ≤ C_H·γ/2` with `C_H = 2 C_loc θ/(1−θ)`.  This is the
  third term of the corrected Row A1 margin.
* `marginalMemory_unbounded` : the *marginal* running coupling is explicitly
  **not** assumed to forget its preceding couplings.  A memory component that
  does not decay at all contributes `j·a` at shell `j`, which exceeds every
  constant.  So the localization theorem must be stated for the irrelevant part
  only, and the marginal part is a genuine residual obligation.

`totalMemory_le_of_split` records what the combination actually buys: a bound on
the full kernel requires a bound on the marginal part as well; localization
alone does not deliver it.
-/
import Mathlib

namespace YangMills

open Finset

/-- Scale-local geometric weight of the irrelevant memory at shell distance. -/
noncomputable def localWeightSum (theta : ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ range j, theta ^ (j - k)

/-- The geometric weight sum is bounded by `θ/(1−θ)`, uniformly in the history
length `j`. -/
theorem localWeightSum_le {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1) (j : ℕ) :
    localWeightSum theta j ≤ theta / (1 - theta) := by
  have hden : 0 < 1 - theta := by linarith
  induction j with
  | zero => simp [localWeightSum]; positivity
  | succ j ih =>
    have hstep : localWeightSum theta (j + 1) = theta * localWeightSum theta j + theta := by
      unfold localWeightSum
      rw [Finset.sum_range_succ]
      have h : ∑ k ∈ range j, theta ^ (j + 1 - k) = theta * ∑ k ∈ range j, theta ^ (j - k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkj : k < j := Finset.mem_range.1 hk
        have : j + 1 - k = (j - k) + 1 := by omega
        rw [this, pow_succ]
        ring
      rw [h]
      simp
    rw [hstep]
    have : theta * localWeightSum theta j ≤ theta * (theta / (1 - theta)) := by
      exact mul_le_mul_of_nonneg_left ih h0
    have hT : theta * (theta / (1 - theta)) + theta = theta / (1 - theta) := by
      field_simp
      ring
    linarith

/-- **Localized irrelevant memory is uniformly summable.**  A scale-local
majorant on the irrelevant memory kernel bounds the whole history sum by
`C_loc·γ·θ/(1−θ)`, with no dependence on the shell index (history length). -/
theorem irrelevantMemory_sum_le {Rirr : ℕ → ℕ → ℝ} {theta Cloc gamma : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta < 1) (hC : 0 ≤ Cloc) (hg : 0 ≤ gamma)
    (hmaj : ∀ j k, k < j → |Rirr j k| ≤ Cloc * gamma * theta ^ (j - k)) (j : ℕ) :
    ∑ k ∈ range j, |Rirr j k| ≤ Cloc * gamma * (theta / (1 - theta)) := by
  have hstep : ∑ k ∈ range j, |Rirr j k| ≤ ∑ k ∈ range j, Cloc * gamma * theta ^ (j - k) :=
    Finset.sum_le_sum fun k hk => hmaj j k (Finset.mem_range.1 hk)
  have hfac : ∑ k ∈ range j, Cloc * gamma * theta ^ (j - k)
      = Cloc * gamma * localWeightSum theta j := by
    rw [localWeightSum, Finset.mul_sum]
  have hbound : Cloc * gamma * localWeightSum theta j
      ≤ Cloc * gamma * (theta / (1 - theta)) :=
    mul_le_mul_of_nonneg_left (localWeightSum_le h0 h1 j) (by positivity)
  rw [hfac] at hstep
  linarith

/-- The localization constant of the corrected margin: `C_H = 2 C_loc θ/(1−θ)`,
so that the localized memory bound reads `H_irr ≤ C_H·γ/2`. -/
noncomputable def CH (Cloc theta : ℝ) : ℝ := 2 * Cloc * (theta / (1 - theta))

/-- The localized memory bound in the shape used by the corrected Row A1
margin. -/
theorem irrelevantMemory_le_CH_half {Rirr : ℕ → ℕ → ℝ} {theta Cloc gamma : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta < 1) (hC : 0 ≤ Cloc) (hg : 0 ≤ gamma)
    (hmaj : ∀ j k, k < j → |Rirr j k| ≤ Cloc * gamma * theta ^ (j - k)) (j : ℕ) :
    ∑ k ∈ range j, |Rirr j k| ≤ CH Cloc theta * gamma / 2 := by
  have h := irrelevantMemory_sum_le h0 h1 hC hg hmaj j
  have : CH Cloc theta * gamma / 2 = Cloc * gamma * (theta / (1 - theta)) := by
    unfold CH; ring
  linarith [this ▸ h]

/-- **The marginal component does not localize.**  A memory component of
constant size `a > 0` at every preceding scale contributes `j·a` at shell `j`,
which exceeds every prescribed constant.  Hence the localization theorem cannot
be applied to the marginal running coupling. -/
theorem marginalMemory_unbounded {a : ℝ} (ha : 0 < a) (D : ℝ) :
    ∃ j : ℕ, D < ∑ _k ∈ range j, a := by
  obtain ⟨n, hn⟩ := exists_nat_gt (D / a)
  refine ⟨n, ?_⟩
  rw [Finset.sum_const, card_range, nsmul_eq_mul]
  rw [div_lt_iff₀ ha] at hn
  linarith

/-- What the split actually buys: the total memory is controlled only once the
marginal part is controlled too. -/
theorem totalMemory_le_of_split {R Rirr Rmarg : ℕ → ℕ → ℝ} {Hirr Hmarg : ℝ}
    (hsplit : ∀ j k, R j k = Rirr j k + Rmarg j k)
    (hirr : ∀ j, ∑ k ∈ range j, |Rirr j k| ≤ Hirr)
    (hmarg : ∀ j, ∑ k ∈ range j, |Rmarg j k| ≤ Hmarg) (j : ℕ) :
    ∑ k ∈ range j, |R j k| ≤ Hirr + Hmarg := by
  have h1 : ∑ k ∈ range j, |R j k|
      ≤ ∑ k ∈ range j, (|Rirr j k| + |Rmarg j k|) := by
    refine Finset.sum_le_sum fun k _ => ?_
    rw [hsplit j k]
    exact abs_add_le _ _
  have h2 : ∑ k ∈ range j, (|Rirr j k| + |Rmarg j k|)
      = (∑ k ∈ range j, |Rirr j k|) + ∑ k ∈ range j, |Rmarg j k| :=
    Finset.sum_add_distrib
  have := hirr j
  have := hmarg j
  linarith [h1, h2 ▸ h1]

end YangMills
