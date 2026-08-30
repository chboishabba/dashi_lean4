/-
# What the one-step source factors have to deliver for the history debt

Item (4) of the literal A1 source package asks for one-step factors with
`|J_i| ≤ θ < 1`, from which `HistoryChainRule.responseDecay_of_chainRule` and
`A1SourcePackage.historyDebt_of_oneStepSources` produce the uniform history debt
`C_R B θ/(1−θ)`.  Two questions are natural about that datum, and this module
answers both.

* **Is a uniform `θ < 1` necessary?**  No — what the budget really consumes is a
  uniformly summable kernel.  `historyDebt_of_summableKernel` gives the debt
  `D·B` from `∑_{k<j} |R_{j,k}| ≤ D` alone, with no decay rate and no chain
  structure, and `summableKernel_of_geometric` shows the geometric datum is the
  special case `D = C_R θ/(1−θ)`.  So a source extraction that produces
  summability without a rate still closes A1b.

* **Can the contraction be dropped at the level of the literal one-step
  factors?**  No.  `marginalChain_debt_unbounded`: if the one-step factors are
  *marginal*, `J_i = 1`, and the head factor does not vanish (`|A_j| ≥ c > 0`),
  then the chain kernel has `∑_{k<j} |R_{j,k}| = j·|A_j| ≥ jc`, which exceeds
  every constant.  So no uniform history debt exists in that case, and the
  requirement `|J_i| ≤ θ < 1` (or some other genuine summability) is
  load-bearing rather than a convenience — it cannot be replaced by the mere
  boundedness `|J_i| ≤ 1` of a marginal effective-coupling map.
-/
import RequestProject.YangMills.A1SourcePackage

namespace YangMills

open Finset

/-- **The history debt from a uniformly summable response kernel.**  No decay
rate and no chain structure are needed: a uniform bound `D` on the total
response of a shell to its whole history gives the uniform debt `D·B`. -/
theorem historyDebt_of_summableKernel {beta : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ}
    {D B : ℝ} (hresp : HasHistoryResponse beta R)
    (hsum : ∀ j, ∑ k ∈ range j, |R j k| ≤ D)
    {g g' : ℕ → ℝ} (hB : ∀ k, |g k - g' k| ≤ B) (j : ℕ) :
    |beta j g - beta j g'| ≤ D * B := by
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  refine le_trans (hresp j g g') ?_
  calc ∑ k ∈ range j, |R j k| * |g k - g' k|
      ≤ ∑ k ∈ range j, |R j k| * B :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (hB k) (abs_nonneg _)
    _ = (∑ k ∈ range j, |R j k|) * B := by rw [Finset.sum_mul]
    _ ≤ D * B := mul_le_mul_of_nonneg_right (hsum j) hBnn

/-- The geometric datum of item (4) is the special case
`D = C_R θ/(1−θ)` of uniform summability. -/
theorem summableKernel_of_geometric {R : ℕ → ℕ → ℝ} {CR theta : ℝ}
    (hdec : HasResponseDecay R CR theta) (hCR : 0 ≤ CR)
    (h0 : 0 ≤ theta) (h1 : theta < 1) (j : ℕ) :
    ∑ k ∈ range j, |R j k| ≤ CR * (theta / (1 - theta)) := by
  calc ∑ k ∈ range j, |R j k| ≤ ∑ k ∈ range j, CR * theta ^ (j - k) :=
        Finset.sum_le_sum fun k hk => hdec j k (Finset.mem_range.mp hk)
    _ = CR * ∑ k ∈ range j, theta ^ (j - k) := by rw [Finset.mul_sum]
    _ ≤ CR * (theta / (1 - theta)) :=
        mul_le_mul_of_nonneg_left (responseSum_le h0 h1 j) hCR

/-- **The Row A1 margin under the weaker summability datum.**  Replacing the
geometric decay of item (4) by uniform summability of the response kernel still
gives a uniform lower bound on the shell coefficient, now with debt `D·B`. -/
theorem A1_lower_bound_of_summableKernel
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ} {bZ Rint D B : ℝ} {j : ℕ}
    (hsplit : ∀ j g, beta j g = betaZ j g + betaInt j g)
    (hresp : HasHistoryResponse betaZ R)
    (hsum : ∀ j, ∑ k ∈ range j, |R j k| ≤ D)
    {g gref : ℕ → ℝ} (hB : ∀ k, |g k - gref k| ≤ B)
    (hZ : bZ ≤ betaZ j gref) (hInt : |betaInt j g| ≤ Rint) :
    bZ - Rint - D * B ≤ beta j g := by
  have hdebt : |betaZ j g - betaZ j gref| ≤ D * B :=
    historyDebt_of_summableKernel hresp hsum hB j
  have h1 := (abs_le.mp hdebt).1
  have h2 := (abs_le.mp hInt).1
  rw [hsplit j g]
  linarith

/-- The total response of a chain kernel with marginal one-step factors
`J_i = 1` is `j · |A_j|`. -/
lemma chainKernelSum_marginal {R : ℕ → ℕ → ℝ} {A : ℕ → ℝ}
    (hfac : HasChainFactorisation R A (fun _ => 1)) (j : ℕ) :
    ∑ k ∈ range j, |R j k| = j * |A j| := by
  have hterm : ∀ k ∈ range j, |R j k| = |A j| := by
    intro k hk
    rw [hfac j k (Finset.mem_range.mp hk)]
    simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **A marginal one-step factor gives no uniform history debt.**  If the
one-step effective-coupling factors are marginal (`J_i = 1`) and the head factor
is bounded away from zero, the total history response exceeds every constant, so
no uniform bound of the form consumed by the Row A1 margin exists.  The
contraction datum `|J_i| ≤ θ < 1` is therefore load-bearing. -/
theorem marginalChain_debt_unbounded {R : ℕ → ℕ → ℝ} {A : ℕ → ℝ} {c : ℝ}
    (hfac : HasChainFactorisation R A (fun _ => 1)) (hc : 0 < c)
    (hA : ∀ j, c ≤ |A j|) (D : ℝ) :
    ∃ j : ℕ, D < ∑ k ∈ range j, |R j k| := by
  obtain ⟨j, hj⟩ := exists_nat_gt (D / c)
  refine ⟨j, ?_⟩
  rw [chainKernelSum_marginal hfac j]
  have hjc : D < j * c := by
    have := (div_lt_iff₀ hc).mp hj
    linarith
  have hmono : (j : ℝ) * c ≤ (j : ℝ) * |A j| :=
    mul_le_mul_of_nonneg_left (hA j) (Nat.cast_nonneg j)
  linarith

end YangMills
