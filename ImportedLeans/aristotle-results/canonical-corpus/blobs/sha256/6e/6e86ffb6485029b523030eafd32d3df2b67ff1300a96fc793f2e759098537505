import Mathlib
import Integration.Experiment.JacobianSensitivity

/-!
# Stage 6, lane 3 — the uncertainty budget derived from the graph

`TOE_STAGE5_INFERENCE.md` frontier item 5 records the gap closed here:

> **The uncertainty budget is still declared.**  `compile` now reports a
> *computed* propagated variance, but the three-way `Budget` is unchanged and
> provably distinct from it.

This file derives a budget instead of declaring one:

```
input covariance  +  certified derivatives   ⟹   output variance
                                             ⟹   per-input contribution shares
```

so that the compiler can say *which measurement contributes most of the
first-order propagated variance* — and so that measurement selection can be
driven by actual uncertainty reduction rather than by a declared modulus.

## The objects

* `totalVariance row S` — the first-order propagated variance
  `∑ᵢ ∑ⱼ (∂f/∂xᵢ) Σᵢⱼ (∂f/∂xⱼ)`, proved equal to the `(0,0)` entry of the
  existing `RCov.push` and to `row ⬝ Σ ⬝ row`;
* `ownShare row S i` — the term `(∂f/∂xᵢ)² σᵢ²` attributable to input `i`;
* `derivedBudget C S` — the budget of a `CertifiedSensitivity`: the row is the
  vector of *proved* partial derivatives, so the number is a consequence of the
  graph rather than an annotation.

## What is proved

* `totalVariance_eq_push`, `totalVariance_eq_dotProduct`, `totalVariance_nonneg`
  — the derived number is the one the propagation layer already computes, and it
  is a variance (nonnegative, by positive semidefiniteness of the input
  covariance);
* `variance_diag_nonneg`, `ownShare_nonneg` — every share is nonnegative;
* `totalVariance_diag` — for independent inputs the total is exactly the sum of
  the shares, so the accounting is complete;
* `shareFraction_sum_eq_one` — the shares are fractions of the total;
* `exists_dominant_input`, `dominant_share_ge_average` — there is a largest
  contributor, and it carries at least `1/n` of the budget;
* `zeroing_removes_exactly_its_share` — eliminating an input's uncertainty
  removes exactly its share, and nothing else;
* `reducing_the_dominant_helps_most` — **the measurement-selection statement**:
  of two inputs, perfecting the larger contributor leaves the smaller residual
  variance;
* `totalVariance_mono` — the budget is monotone in the input variances;
* `derivedBudget_is_from_certified_derivatives` — the row used *is* the vector
  of partial derivatives of the law, discharged by the certificate.

The honest negatives:

* `shares_do_not_account_for_correlation` — with correlated inputs the sum of
  the own-shares is strictly less than the total: share accounting is complete
  only for independent inputs, and a diagonal input covariance is a modelling
  assumption, not a theorem;
* `derived_budget_ignores_model_discrepancy` — the derived number is a
  propagation of *input* uncertainty only; it says nothing about the term the
  Stage-3 `Budget` calls model discrepancy, which no amount of graph information
  supplies.

## What is *not* claimed

First order only (the existing `certificate_does_not_make_propagation_exact`
stands), Gaussian nothing, and no coverage: a variance here is a number computed
from a declared input covariance and proved derivatives, not the variance of a
random variable in a probability space.
-/

namespace Integration.Experiment.VarianceBudget

open Finset Matrix
open Integration.Experiment.JacobianSensitivity

variable {n : ℕ}

/-! ## §1 The derived variance and its shares -/

/-- The first-order propagated variance of a scalar law with sensitivity row
`row` and input covariance `S`. -/
def totalVariance (row : Fin n → ℝ) (S : RCov n) : ℝ :=
  ∑ i, ∑ j, row i * S.toMatrix i j * row j

/-- The sensitivity row as a `1 × n` matrix, so that the existing propagation
machinery applies to it. -/
def rowMatrix (row : Fin n → ℝ) : Matrix (Fin 1) (Fin n) ℝ := fun _ j => row j

/-- **The derived variance is the one the propagation layer computes**: the
`(0,0)` entry of `J Σ Jᵀ`. -/
theorem totalVariance_eq_push (row : Fin n → ℝ) (S : RCov n) :
    totalVariance row S = (RCov.push (rowMatrix row) S).toMatrix 0 0 := by
  simp only [RCov.push_toMatrix, Matrix.mul_apply, Matrix.transpose_apply, rowMatrix,
    totalVariance, Finset.sum_mul]
  exact Finset.sum_comm

theorem totalVariance_eq_dotProduct (row : Fin n → ℝ) (S : RCov n) :
    totalVariance row S = row ⬝ᵥ (S.toMatrix *ᵥ row) := by
  simp only [totalVariance, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- A derived budget is nonnegative — it is a variance. -/
theorem totalVariance_nonneg (row : Fin n → ℝ) (S : RCov n) :
    0 ≤ totalVariance row S := by
  rw [totalVariance_eq_dotProduct]
  exact S.psd row

/-- Every diagonal entry of a covariance matrix is nonnegative. -/
theorem variance_diag_nonneg (S : RCov n) (i : Fin n) : 0 ≤ S.toMatrix i i := by
  have h := S.psd (Pi.single i 1)
  simpa [dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_ite_eq'] using h

/-- The share of the budget attributable to input `i`: `(∂f/∂xᵢ)² σᵢ²`. -/
def ownShare (row : Fin n → ℝ) (S : RCov n) (i : Fin n) : ℝ :=
  row i ^ 2 * S.toMatrix i i

theorem ownShare_nonneg (row : Fin n → ℝ) (S : RCov n) (i : Fin n) :
    0 ≤ ownShare row S i :=
  mul_nonneg (sq_nonneg _) (variance_diag_nonneg S i)

/-- The fraction of the budget carried by input `i`. -/
noncomputable def shareFraction (row : Fin n → ℝ) (S : RCov n) (i : Fin n) : ℝ :=
  ownShare row S i / totalVariance row S

/-! ## §2 Independent inputs: the accounting is complete -/

/-- **For independent inputs the total is exactly the sum of the shares.**  This
is the statement that lets the compiler report contribution shares at all. -/
theorem totalVariance_diag (row d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    totalVariance row (RCov.diag d hd) = ∑ i, ownShare row (RCov.diag d hd) i := by
  simp only [totalVariance, ownShare, RCov.diag, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hj; simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The shares of independent inputs are fractions summing to one. -/
theorem shareFraction_sum_eq_one (row d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (h : totalVariance row (RCov.diag d hd) ≠ 0) :
    ∑ i, shareFraction row (RCov.diag d hd) i = 1 := by
  simp only [shareFraction, ← Finset.sum_div]
  rw [← totalVariance_diag row d hd]
  exact div_self h

/-- There is always a largest contributor. -/
theorem exists_dominant_input [NeZero n] (row : Fin n → ℝ) (S : RCov n) :
    ∃ i, ∀ j, ownShare row S j ≤ ownShare row S i := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 (Nat.pos_of_ne_zero (NeZero.ne n)))
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (ownShare row S) hne
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

/-- **The dominant contributor carries at least `1/n` of the budget.** -/
theorem dominant_share_ge_average (row d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (i : Fin n)
    (hi : ∀ j, ownShare row (RCov.diag d hd) j ≤ ownShare row (RCov.diag d hd) i) :
    totalVariance row (RCov.diag d hd) ≤ n * ownShare row (RCov.diag d hd) i := by
  rw [totalVariance_diag row d hd]
  calc ∑ j, ownShare row (RCov.diag d hd) j
      ≤ ∑ _j : Fin n, ownShare row (RCov.diag d hd) i :=
        Finset.sum_le_sum (fun j _ => hi j)
    _ = n * ownShare row (RCov.diag d hd) i := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## §3 What a measurement improvement buys -/

/-- Perfecting input `i` — driving its variance to zero. -/
def perfect (d : Fin n → ℝ) (i : Fin n) : Fin n → ℝ := Function.update d i 0

theorem perfect_nonneg {d : Fin n → ℝ} (hd : ∀ i, 0 ≤ d i) (i : Fin n) :
    ∀ j, 0 ≤ perfect d i j := by
  intro j
  by_cases h : j = i
  · subst h; simp [perfect]
  · simp [perfect, Function.update_of_ne h, hd j]

/-- **Perfecting an input removes exactly its share, and nothing else.** -/
theorem zeroing_removes_exactly_its_share (row d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (i : Fin n) :
    totalVariance row (RCov.diag (perfect d i) (perfect_nonneg hd i))
      = totalVariance row (RCov.diag d hd) - row i ^ 2 * d i := by
  rw [totalVariance_diag _ _ (perfect_nonneg hd i), totalVariance_diag _ _ hd]
  have hsplit : ∀ (e : Fin n → ℝ) (he : ∀ i, 0 ≤ e i),
      ∑ j, ownShare row (RCov.diag e he) j = ∑ j, row j ^ 2 * e j := by
    intro e he
    exact Finset.sum_congr rfl (fun j _ => by simp [ownShare, RCov.diag])
  rw [hsplit _ (perfect_nonneg hd i), hsplit _ hd]
  rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i) (fun j => row j ^ 2 * perfect d i j),
    Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i) (fun j => row j ^ 2 * d j)]
  have hpi : perfect d i i = 0 := by simp [perfect]
  have hoff : ∀ j ∈ Finset.univ \ {i}, row j ^ 2 * perfect d i j = row j ^ 2 * d j := by
    intro j hj
    have : j ≠ i := by simpa using (Finset.mem_sdiff.1 hj).2
    simp [perfect, Function.update_of_ne this]
  rw [Finset.sum_congr rfl hoff, hpi]
  ring

/-- **Measurement selection by actual uncertainty reduction.**  Of two inputs,
perfecting the one with the larger share leaves the smaller residual variance.
This is the uncertainty-driven counterpart of the declared-modulus ranking of
`Integration.Experiment.NonlinearDiscrimination`. -/
theorem reducing_the_dominant_helps_most (row d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (i j : Fin n)
    (hij : ownShare row (RCov.diag d hd) j ≤ ownShare row (RCov.diag d hd) i) :
    totalVariance row (RCov.diag (perfect d i) (perfect_nonneg hd i))
      ≤ totalVariance row (RCov.diag (perfect d j) (perfect_nonneg hd j)) := by
  rw [zeroing_removes_exactly_its_share row d hd i, zeroing_removes_exactly_its_share row d hd j]
  have hi : ownShare row (RCov.diag d hd) i = row i ^ 2 * d i := by
    simp [ownShare, RCov.diag]
  have hj : ownShare row (RCov.diag d hd) j = row j ^ 2 * d j := by
    simp [ownShare, RCov.diag]
  rw [hi, hj] at hij
  linarith

/-- The budget is monotone in the input variances. -/
theorem totalVariance_mono (row d e : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (he : ∀ i, 0 ≤ e i)
    (hde : ∀ i, d i ≤ e i) :
    totalVariance row (RCov.diag d hd) ≤ totalVariance row (RCov.diag e he) := by
  rw [totalVariance_diag _ _ hd, totalVariance_diag _ _ he]
  refine Finset.sum_le_sum (fun i _ => ?_)
  simp only [ownShare, RCov.diag, Matrix.diagonal_apply_eq]
  exact mul_le_mul_of_nonneg_left (hde i) (sq_nonneg _)

/-! ## §4 The budget of a certified law -/

/-- **The derived budget of a certified law**: the sensitivity row is the
certificate's, i.e. a vector of proved partial derivatives. -/
noncomputable def derivedBudget (C : CertifiedSensitivity n) (S : RCov n) : ℝ :=
  totalVariance C.declared S

/-- **The row the budget is computed from consists of derivatives.**  This is the
sense in which the budget now *comes from the graph*: no number in it is
declared metadata. -/
theorem derivedBudget_is_from_certified_derivatives (C : CertifiedSensitivity n) (S : RCov n) :
    derivedBudget C S
      = totalVariance (fun j => deriv (fun t => C.f (Function.update C.point j t)) (C.point j)) S := by
  simp only [derivedBudget]
  congr 1
  funext j
  exact C.declared_is_the_partial_derivative j

/-! ## §5 Negatives -/

/-- A perfectly correlated two-input covariance. -/
def fullyCorrelated : RCov 2 where
  toMatrix := fun _ _ => 1
  symm := by ext i j; rfl
  psd := by
    intro v
    have h : (((fun _ _ => (1:ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v) = fun _ => v 0 + v 1 := by
      funext i
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [h]
    simp only [dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (v 0 + v 1)]

/-- **Share accounting is complete only for independent inputs.**  With perfectly
correlated inputs the own-shares sum to `2` while the propagated variance is `4`:
the cross terms carry half the budget, so a report of per-input shares is
incomplete unless the input covariance is diagonal. -/
theorem shares_do_not_account_for_correlation :
    totalVariance (fun _ => 1) fullyCorrelated = 4 ∧
      ∑ i, ownShare (fun _ => 1) fullyCorrelated i = 2 := by
  constructor
  · norm_num [totalVariance, Fin.sum_univ_two, fullyCorrelated]
  · norm_num [ownShare, Fin.sum_univ_two, fullyCorrelated]

/-- **The derived budget is an input-propagation number only.**  Two laws with
the same certified row and the same input covariance have the same derived
budget however differently they misdescribe the system: nothing about model
discrepancy is derivable from the graph, so the Stage-3 budget's third entry
remains a genuinely separate declaration. -/
theorem derived_budget_ignores_model_discrepancy (C D : CertifiedSensitivity n) (S : RCov n)
    (h : C.declared = D.declared) : derivedBudget C S = derivedBudget D S := by
  simp [derivedBudget, h]

end Integration.Experiment.VarianceBudget
