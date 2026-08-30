/-
# Item (4) of the A1 package: producers of the *summability* datum

`HistoryDebtCriteria` isolated the actual margin-facing requirement for the
literal Bałaban response kernel,

    sup_j ∑_{k<j} |R_{j,k}| ≤ D,

and showed that the geometric chain `|J_i| ≤ θ < 1` is one sufficient producer,
`D = C_R θ/(1−θ)`, while marginal factors with a non-vanishing head make the
debt unbounded.  Between those two extremes there is a lot of room, and a source
extraction is much likelier to land in the middle than on either end.  This
module supplies the intermediate producers, each strictly weaker than pointwise
geometric contraction:

* `summableKernel_of_summableProfile` — the weakest one.  Any translation-invariant
  summable profile, `|R_{j,k}| ≤ w(j−k)` with `w ≥ 0` summable, gives
  `D = ∑' m, w(m+1)`.  No rate, no chain structure, no contraction.
* `summableKernel_of_averageContraction` — the chain version without *pointwise*
  contraction: only the *products* `∏_{i∈[k,j)} J_i` need to be geometrically
  bounded, `|∏| ≤ Λθ^{j−k}`.  Individual steps may exceed `1`.
* `prodBound_of_logExcess` — the standard way such a product bound arises for a
  variable-coefficient recursion: `|J_i| ≤ θ·exp(d_i)` with a *summable* excess
  `∑_i d_i ≤ Δ` gives `|∏| ≤ e^Δ θ^{j−k}`.  So a chain that is only
  asymptotically contracting, and may be marginal or expanding at finitely many
  scales, still produces the datum.
* `A1_lower_bound_of_averageContraction` — the Row A1 margin consuming the
  average-contraction datum directly.

Nothing here asserts any property of the literal Bałaban kernel; these are the
alternative shapes of the A1b source obligation, each of which suffices.
-/
import RequestProject.YangMills.HistoryDebtCriteria
import RequestProject.YangMills.HistoryChainRule

namespace YangMills

open Finset

/-! ## The weakest producer: a summable profile -/

/-- **Uniform summability from a summable profile.**  If the response kernel is
dominated by a nonnegative summable function of the scale separation alone, the
total history response is bounded by `∑' m, w(m+1)`, uniformly in the shell
index. -/
theorem summableKernel_of_summableProfile {R : ℕ → ℕ → ℝ} {w : ℕ → ℝ}
    (hw : ∀ m, 0 ≤ w m) (hsum : Summable w)
    (hR : ∀ j k, k < j → |R j k| ≤ w (j - k)) (j : ℕ) :
    ∑ k ∈ range j, |R j k| ≤ ∑' m : ℕ, w (m + 1) := by
  have hshift : Summable (fun m : ℕ => w (m + 1)) := (summable_nat_add_iff 1).mpr hsum
  have hstep : ∑ k ∈ range j, |R j k| ≤ ∑ k ∈ range j, w (j - k) :=
    Finset.sum_le_sum fun k hk => hR j k (Finset.mem_range.mp hk)
  have hreflect : ∑ k ∈ range j, w (j - k) = ∑ i ∈ range j, w (i + 1) := by
    have := Finset.sum_range_reflect (fun i => w (i + 1)) j
    calc ∑ k ∈ range j, w (j - k) = ∑ i ∈ range j, w (j - 1 - i + 1) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have hij : i < j := Finset.mem_range.mp hi
          congr 1
          omega
      _ = ∑ i ∈ range j, w (i + 1) := this
  have hle : ∑ i ∈ range j, w (i + 1) ≤ ∑' m : ℕ, w (m + 1) :=
    hshift.sum_le_tsum _ (fun i _ => hw (i + 1))
  linarith [hstep, hreflect.le, hreflect.ge]

/-! ## Average, rather than pointwise, contraction -/

/-- **Uniform summability from average contraction.**  Only the products of the
one-step factors need to contract geometrically; the individual factors are
unconstrained. -/
theorem summableKernel_of_averageContraction {R : ℕ → ℕ → ℝ} {A J : ℕ → ℝ}
    {CR lam theta : ℝ}
    (hfac : HasChainFactorisation R A J) (hCR : 0 ≤ CR) (hA : ∀ j, |A j| ≤ CR)
    (hlam : 0 ≤ lam)
    (hprod : ∀ k j, k < j → |∏ i ∈ Ico k j, J i| ≤ lam * theta ^ (j - k))
    (h0 : 0 ≤ theta) (h1 : theta < 1) (j : ℕ) :
    ∑ k ∈ range j, |R j k| ≤ CR * lam * (theta / (1 - theta)) := by
  have hterm : ∀ k ∈ range j, |R j k| ≤ (CR * lam) * theta ^ (j - k) := by
    intro k hk
    have hkj : k < j := Finset.mem_range.mp hk
    rw [hfac j k hkj, abs_mul]
    have hp : |∏ i ∈ Ico k j, J i| ≤ lam * theta ^ (j - k) := hprod k j hkj
    have := mul_le_mul (hA j) hp (abs_nonneg _) hCR
    calc |A j| * |∏ i ∈ Ico k j, J i| ≤ CR * (lam * theta ^ (j - k)) := this
      _ = (CR * lam) * theta ^ (j - k) := by ring
  calc ∑ k ∈ range j, |R j k| ≤ ∑ k ∈ range j, (CR * lam) * theta ^ (j - k) :=
        Finset.sum_le_sum hterm
    _ = (CR * lam) * ∑ k ∈ range j, theta ^ (j - k) := by rw [Finset.mul_sum]
    _ ≤ (CR * lam) * (theta / (1 - theta)) :=
        mul_le_mul_of_nonneg_left (responseSum_le h0 h1 j) (mul_nonneg hCR hlam)
    _ = CR * lam * (theta / (1 - theta)) := rfl

/-- **Average contraction from a summable logarithmic excess.**  If the one-step
factors satisfy `|J_i| ≤ θ·exp(d_i)` with `d_i ≥ 0` and the excess summable,
`∑_{i<j} d_i ≤ Δ` for every `j`, then the products contract geometrically with
the constant `Λ = e^Δ`.  Finitely many marginal or expanding steps are therefore
harmless. -/
theorem prodBound_of_logExcess {J d : ℕ → ℝ} {theta Delta : ℝ}
    (h0 : 0 ≤ theta) (hd : ∀ i, 0 ≤ d i)
    (hJ : ∀ i, |J i| ≤ theta * Real.exp (d i))
    (hDelta : ∀ j, ∑ i ∈ range j, d i ≤ Delta) (k j : ℕ) :
    |∏ i ∈ Ico k j, J i| ≤ Real.exp Delta * theta ^ (j - k) := by
  have hcard : (Ico k j).card = j - k := Nat.card_Ico k j
  have habs : |∏ i ∈ Ico k j, J i| = ∏ i ∈ Ico k j, |J i| := by
    rw [Finset.abs_prod]
  have hstep : ∏ i ∈ Ico k j, |J i| ≤ ∏ i ∈ Ico k j, theta * Real.exp (d i) :=
    Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hJ i)
  have hsplit : ∏ i ∈ Ico k j, theta * Real.exp (d i)
      = theta ^ (j - k) * Real.exp (∑ i ∈ Ico k j, d i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, Real.exp_sum]
  have hsub : ∑ i ∈ Ico k j, d i ≤ ∑ i ∈ range j, d i := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hd i)
    intro i hi
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
  have hexp : Real.exp (∑ i ∈ Ico k j, d i) ≤ Real.exp Delta :=
    Real.exp_le_exp.mpr (le_trans hsub (hDelta j))
  have hpow : (0:ℝ) ≤ theta ^ (j - k) := pow_nonneg h0 _
  calc |∏ i ∈ Ico k j, J i| = ∏ i ∈ Ico k j, |J i| := habs
    _ ≤ ∏ i ∈ Ico k j, theta * Real.exp (d i) := hstep
    _ = theta ^ (j - k) * Real.exp (∑ i ∈ Ico k j, d i) := hsplit
    _ ≤ theta ^ (j - k) * Real.exp Delta := mul_le_mul_of_nonneg_left hexp hpow
    _ = Real.exp Delta * theta ^ (j - k) := by ring

/-- **The Row A1 margin under average contraction.**  Combining the two previous
results: an asymptotically contracting chain, with only summable logarithmic
excess, still yields the uniform lower bound with the debt
`C_R e^Δ B θ/(1−θ)`. -/
theorem A1_lower_bound_of_averageContraction
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ} {A J d : ℕ → ℝ}
    {bZ Rint CR theta Delta B : ℝ} {j : ℕ}
    (hsplit : ∀ j g, beta j g = betaZ j g + betaInt j g)
    (hresp : HasHistoryResponse betaZ R)
    (hfac : HasChainFactorisation R A J) (hCR : 0 ≤ CR) (hA : ∀ j, |A j| ≤ CR)
    (h0 : 0 ≤ theta) (h1 : theta < 1) (hd : ∀ i, 0 ≤ d i)
    (hJ : ∀ i, |J i| ≤ theta * Real.exp (d i))
    (hDelta : ∀ j, ∑ i ∈ range j, d i ≤ Delta)
    {g gref : ℕ → ℝ} (hB : ∀ k, |g k - gref k| ≤ B)
    (hZ : bZ ≤ betaZ j gref) (hInt : |betaInt j g| ≤ Rint) :
    bZ - Rint - (CR * Real.exp Delta * (theta / (1 - theta))) * B ≤ beta j g := by
  have hsum : ∀ j, ∑ k ∈ range j, |R j k|
      ≤ CR * Real.exp Delta * (theta / (1 - theta)) := by
    intro j'
    exact summableKernel_of_averageContraction hfac hCR hA (Real.exp_nonneg Delta)
      (fun k j'' _ => prodBound_of_logExcess h0 hd hJ hDelta k j'') h0 h1 j'
  exact A1_lower_bound_of_summableKernel hsplit hresp hsum hB hZ hInt

/-! ## Boundary tests -/

/-- The summable-profile producer is not vacuous: the geometric profile
`w(m) = θ^m` is summable and dominates the geometric kernel. -/
theorem summableProfile_nonvacuous {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1) :
    Summable (fun m : ℕ => theta ^ m)
      ∧ ∀ j k : ℕ, k < j → |(theta ^ (j - k) : ℝ)| ≤ theta ^ (j - k) := by
  refine ⟨summable_geometric_of_lt_one h0 h1, fun j k _ => ?_⟩
  rw [abs_of_nonneg (pow_nonneg h0 _)]

/-- The logarithmic-excess producer genuinely permits marginal steps: with
`θ = 1/2` and `d_i = log 2` for `i = 0` only, the first factor may be `1`
(marginal) while the products still contract. -/
theorem logExcess_permits_marginal_step :
    |(1 : ℝ)| ≤ (1/2 : ℝ) * Real.exp (Real.log 2) := by
  rw [Real.exp_log (by norm_num : (0:ℝ) < 2)]
  norm_num

end YangMills
