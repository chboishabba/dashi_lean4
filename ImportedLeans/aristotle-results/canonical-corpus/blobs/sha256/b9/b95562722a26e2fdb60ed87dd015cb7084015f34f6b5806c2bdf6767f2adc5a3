import Mathlib
import Integration.Experiment.VarianceBudget

/-!
# Stage 7, lane 4 — correlated uncertainty and the failure of per-input attribution

`TOE_STAGE6_INFERENCE.md` frontier item 4 records the gap closed here:

> **Share accounting assumes a diagonal input covariance.**  `shareFraction_sum_eq_one`,
> `zeroing_removes_exactly_its_share` and `reducing_the_dominant_helps_most` are
> stated for `RCov.diag`; the correlated case is only given a negative.

The correlated case is closed here, and the answer is a *negative with an
axiomatic proof*, not a formula.

## The decomposition

For a certified sensitivity row `r` and an input covariance `Σ`, first-order
propagation gives `Σ_y = J Σ_x Jᵀ`; in the scalar-output case its only entry is

```
Var(y)  =  Σᵢ rᵢ² Σᵢᵢ   +   Σᵢ Σ_{j ≠ i} rᵢ rⱼ Σᵢⱼ
        =  (own shares)  +  (cross terms)
```

`totalVariance_split` proves this, `crossTerms_diag` proves the cross terms
vanish exactly for independent inputs, and `totalVariance_two` gives the familiar
`r₀²σ₀² + r₁²σ₁² + 2r₀r₁Cov(x₀,x₁)`.

## The negative

An *attribution scheme* is any rule assigning a number to each input which

1. sums to the propagated variance, and
2. reduces to the own-share `rᵢ²σᵢ²` when the inputs are independent.

These are the two properties every published uncertainty budget claims.
`correlated_variance_has_no_canonical_attribution` exhibits two schemes
satisfying both and disagreeing on a correlated example.  Hence

```
correlated variance  ⇏  unique per-input attribution
```

and any reported per-input breakdown of a correlated budget carries an extra,
undeclared convention.

## What is proved

| Statement | Kind | Content |
|---|---|---|
| `entry_symm`, `two_abs_offdiag_le` | theorem | covariance entries are symmetric, and `2\|Σᵢⱼ\| ≤ Σᵢᵢ + Σⱼⱼ` |
| `totalVariance_split` | theorem | own shares plus cross terms, exactly |
| `crossTerms_diag`, `totalVariance_two` | theorem | independence kills the cross terms; the `n = 2` formula |
| `outputVariance`, `outputVariance_eq_totalVariance` | definition/theorem | the `i`-th output variance of `Σ_y = JΣ_xJᵀ` is the propagated variance of the `i`-th row |
| `correlation_error_bound_two` | theorem | a certified bound on how wrong the diagonal-only budget can be |
| **`correlated_variance_has_no_canonical_attribution`** | negative | two attribution schemes, both correct on the axioms, disagreeing under correlation |
| `neglecting_correlation_underestimates`, `neglecting_correlation_overestimates` | negative | and the error has no fixed sign |

## Claim boundary

A "covariance" here is a declared symmetric positive-semidefinite matrix; no
theorem says any declared `Σ` is the covariance of a real instrument.  The
propagation is first order, as everywhere in this corpus.
-/

namespace Integration.Experiment.CorrelatedUncertainty

open Integration.Experiment.JacobianSensitivity
open Integration.Experiment.VarianceBudget

variable {n : ℕ}

/-! ## §1 Entries of a covariance -/

/-- Covariance entries are symmetric. -/
theorem entry_symm (S : RCov n) (i j : Fin n) : S.toMatrix j i = S.toMatrix i j := by
  have h := congrFun (congrFun S.symm i) j
  simpa [Matrix.transpose_apply] using h

/-- The bilinear form behind the propagated variance. -/
def bil (S : RCov n) (u v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, u i * S.toMatrix i j * v j

theorem bil_self (S : RCov n) (v : Fin n → ℝ) : bil S v v = totalVariance v S := rfl

theorem bil_add_left (S : RCov n) (u u' v : Fin n → ℝ) :
    bil S (u + u') v = bil S u v + bil S u' v := by
  simp only [bil, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem bil_add_right (S : RCov n) (u v v' : Fin n → ℝ) :
    bil S u (v + v') = bil S u v + bil S u v' := by
  simp only [bil, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem bil_single (S : RCov n) (i j : Fin n) (a b : ℝ) :
    bil S (Pi.single i a) (Pi.single j b) = a * S.toMatrix i j * b := by
  classical
  simp [bil, Pi.single_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq']

/-- **The off-diagonal entries are controlled by the diagonal**: `2|Σᵢⱼ| ≤ Σᵢᵢ + Σⱼⱼ`.
This is what makes the correlation error boundable even when it is not
attributable. -/
theorem two_abs_offdiag_le (S : RCov n) (i j : Fin n) :
    2 * |S.toMatrix i j| ≤ S.toMatrix i i + S.toMatrix j j := by
  have key : ∀ c : ℝ, 0 ≤ S.toMatrix i i + 2 * c * S.toMatrix i j + c ^ 2 * S.toMatrix j j := by
    intro c
    have h : 0 ≤ bil S (Pi.single i (1:ℝ) + Pi.single j c) (Pi.single i (1:ℝ) + Pi.single j c) := by
      rw [bil_self]
      exact totalVariance_nonneg _ _
    rw [bil_add_left, bil_add_right, bil_add_right, bil_single, bil_single, bil_single,
      bil_single, entry_symm S i j] at h
    nlinarith [h]
  have h1 := key 1
  have h2 := key (-1)
  rcases abs_cases (S.toMatrix i j) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] <;> nlinarith

/-! ## §2 The exact decomposition -/

/-- **The cross terms** of the propagated variance: everything the per-input own
shares omit. -/
def crossTerms (row : Fin n → ℝ) (S : RCov n) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, row i * S.toMatrix i j * row j

/-- **The exact decomposition** `Var(y) = Σ own shares + cross terms`. -/
theorem totalVariance_split (row : Fin n → ℝ) (S : RCov n) :
    totalVariance row S = (∑ i, ownShare row S i) + crossTerms row S := by
  classical
  rw [totalVariance, crossTerms, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  rw [ownShare]
  ring

/-- Independent inputs have no cross terms. -/
theorem crossTerms_diag (row d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    crossTerms row (RCov.diag d hd) = 0 := by
  classical
  rw [crossTerms]
  refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j hj => ?_))
  have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  simp [RCov.diag, hij]

/-- The two-input formula: `r₀²σ₀² + r₁²σ₁² + 2 r₀ r₁ Cov(x₀, x₁)`. -/
theorem totalVariance_two (row : Fin 2 → ℝ) (S : RCov 2) :
    totalVariance row S
      = row 0 ^ 2 * S.toMatrix 0 0 + row 1 ^ 2 * S.toMatrix 1 1
        + 2 * (row 0 * row 1 * S.toMatrix 0 1) := by
  have hsym := entry_symm S 0 1
  simp only [totalVariance, Fin.sum_univ_two]
  rw [hsym]
  ring

/-! ## §3 The vector output -/

/-- The variance of output `i` after propagation `Σ_y = J Σ_x Jᵀ`. -/
def outputVariance {m : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (S : RCov n) (i : Fin m) : ℝ :=
  (RCov.push J S).toMatrix i i

/-- **Each output variance is the propagated variance of its own sensitivity
row.**  So the scalar theory of `VarianceBudget` applies row by row, and nothing
new is needed for vector outputs — except that the *cross-output* entries of
`Σ_y` are not captured by any row. -/
theorem outputVariance_eq_totalVariance {m : ℕ} (J : Matrix (Fin m) (Fin n) ℝ)
    (S : RCov n) (i : Fin m) :
    outputVariance J S i = totalVariance (fun j => J i j) S := by
  simp only [outputVariance, RCov.push_toMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    totalVariance, Finset.sum_mul]
  exact Finset.sum_comm

/-! ## §4 A certified bound on the correlation error -/

/-- **How wrong the diagonal-only budget can be, with a proof.**  For two inputs
the omitted cross term is bounded by `|r₀r₁|(σ₀² + σ₁²)`. -/
theorem correlation_error_bound_two (row : Fin 2 → ℝ) (S : RCov 2) :
    |totalVariance row S - (ownShare row S 0 + ownShare row S 1)|
      ≤ |row 0 * row 1| * (S.toMatrix 0 0 + S.toMatrix 1 1) := by
  have hsplit := totalVariance_two row S
  have hb := two_abs_offdiag_le S 0 1
  have h : totalVariance row S - (ownShare row S 0 + ownShare row S 1)
      = 2 * (row 0 * row 1 * S.toMatrix 0 1) := by
    rw [hsplit, ownShare, ownShare]; ring
  rw [h, abs_mul, abs_mul, abs_two]
  have habs : |row 0 * row 1| * (2 * |S.toMatrix 0 1|)
      ≤ |row 0 * row 1| * (S.toMatrix 0 0 + S.toMatrix 1 1) :=
    mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  calc 2 * (|row 0 * row 1| * |S.toMatrix 0 1|)
      = |row 0 * row 1| * (2 * |S.toMatrix 0 1|) := by ring
    _ ≤ _ := habs

/-! ## §5 The negative: attribution is not canonical -/

/-- **An attribution scheme**: a rule assigning a number to each input which
sums to the propagated variance and agrees with the own-share when the inputs
are independent.  These are exactly the two properties an uncertainty budget
claims. -/
def IsAttribution (A : (Fin n → ℝ) → RCov n → Fin n → ℝ) : Prop :=
  (∀ row S, ∑ i, A row S i = totalVariance row S) ∧
  (∀ (row d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (i : Fin n),
    A row (RCov.diag d hd) i = ownShare row (RCov.diag d hd) i)

/-- Scheme one: give each input its own share plus *all* the cross terms it
participates in.  (Because `Σ` is symmetric, a pair `{i,j}` then contributes
`rᵢrⱼΣᵢⱼ` to each of the two, which is exactly the pair's total.) -/
def symmetricAttribution (row : Fin n → ℝ) (S : RCov n) (i : Fin n) : ℝ :=
  ownShare row S i + ∑ j ∈ Finset.univ.erase i, row i * S.toMatrix i j * row j

/-- Scheme two: give each input its own share, and dump every cross term on
input `0`.  Equally consistent with the axioms, and a different report. -/
def firstInputAttribution [NeZero n] (row : Fin n → ℝ) (S : RCov n) (i : Fin n) : ℝ :=
  ownShare row S i + (if i = (0 : Fin n) then crossTerms row S else 0)

theorem symmetricAttribution_isAttribution : IsAttribution (n := n) symmetricAttribution := by
  classical
  constructor
  · intro row S
    rw [totalVariance_split]
    simp only [symmetricAttribution]
    rw [Finset.sum_add_distrib]
    rfl
  · intro row d hd i
    rw [symmetricAttribution]
    have : ∑ j ∈ Finset.univ.erase i, row i * (RCov.diag d hd).toMatrix i j * row j = 0 := by
      refine Finset.sum_eq_zero (fun j hj => ?_)
      have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      simp [RCov.diag, hij]
    rw [this, add_zero]

theorem firstInputAttribution_isAttribution [NeZero n] :
    IsAttribution (n := n) firstInputAttribution := by
  classical
  constructor
  · intro row S
    rw [totalVariance_split]
    simp only [firstInputAttribution]
    rw [Finset.sum_add_distrib]
    congr 1
    simp
  · intro row d hd i
    rw [firstInputAttribution, crossTerms_diag]
    simp

/-- A perfectly correlated pair of inputs. -/
def allOnes : RCov 2 := fullyCorrelated

/-- **Correlated variance does not determine a per-input attribution.**  Two
schemes, each satisfying both budget axioms, report different numbers for the
same correlated experiment: the symmetric scheme gives input `1` a share of `2`,
the first-input scheme gives it `1`, out of the same total `4`.

Hence any per-input breakdown of a correlated uncertainty budget is a
*convention*, and reporting one as *the* contribution is an overclaim. -/
theorem correlated_variance_has_no_canonical_attribution :
    ∃ A B : (Fin 2 → ℝ) → RCov 2 → Fin 2 → ℝ,
      IsAttribution A ∧ IsAttribution B ∧ A ≠ B := by
  refine ⟨symmetricAttribution, firstInputAttribution,
    symmetricAttribution_isAttribution, firstInputAttribution_isAttribution, ?_⟩
  intro h
  have he : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  have hs : symmetricAttribution (fun _ => (1 : ℝ)) allOnes 1 = 2 := by
    simp [symmetricAttribution, ownShare, allOnes, fullyCorrelated, he]
    norm_num
  have hf : firstInputAttribution (fun _ => (1 : ℝ)) allOnes 1 = 1 := by
    simp [firstInputAttribution, ownShare, allOnes, fullyCorrelated]
  rw [h, hf] at hs
  norm_num at hs

/-! ## §6 The sign of the error is not fixed -/

/-- Perfectly correlated inputs: the diagonal-only budget **underestimates**
(`2 < 4`). -/
theorem neglecting_correlation_underestimates :
    ∑ i, ownShare (fun _ => (1 : ℝ)) allOnes i < totalVariance (fun _ => (1 : ℝ)) allOnes := by
  have h := shares_do_not_account_for_correlation
  rw [allOnes]
  rw [h.1, h.2]
  norm_num

/-- Perfectly anticorrelated inputs. -/
def antiCorrelated : RCov 2 where
  toMatrix := fun i j => if i = j then 1 else -1
  symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  psd := by
    intro v
    have h : Matrix.mulVec (fun i j => if i = j then (1:ℝ) else -1) v
        = ![v 0 - v 1, v 1 - v 0] := by
      funext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    rw [h]
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [sq_nonneg (v 0 - v 1)]

/-- Perfectly anticorrelated inputs: the diagonal-only budget **overestimates**
(`2 > 0`).  Together with the previous theorem: neglecting correlation is not a
conservative approximation in either direction. -/
theorem neglecting_correlation_overestimates :
    totalVariance (fun _ => (1 : ℝ)) antiCorrelated
      < ∑ i, ownShare (fun _ => (1 : ℝ)) antiCorrelated i := by
  have h1 : totalVariance (fun _ => (1 : ℝ)) antiCorrelated = 0 := by
    norm_num [totalVariance, Fin.sum_univ_two, antiCorrelated]
  have h2 : ∑ i, ownShare (fun _ => (1 : ℝ)) antiCorrelated i = 2 := by
    norm_num [ownShare, Fin.sum_univ_two, antiCorrelated]
  rw [h1, h2]
  norm_num

end Integration.Experiment.CorrelatedUncertainty
