/-
# Row A1b, source-facing form: the beta history response kernel

The shell coefficient of a renormalisation-group scheme is not a function of a
single state: it is a function of the whole earlier history of couplings,

    β_j = F_j(g_0, …, g_{j-1}).

Accordingly the quantity to estimate is not a contraction factor of an abstract
state map but the *response kernel*

    R_{j,k} = ∂β_j / ∂g_k,    k < j,

and what the positive-beta budget consumes is the uniform history debt

    sup_j  ∑_{k<j} |R_{j,k}| · B.

This file proves that a geometric response decay `|R_{j,k}| ≤ C θ^{j−k}` with
`θ < 1` delivers exactly that, with the explicit uniform constant
`C · B · θ/(1−θ)` — uniform in the shell index, hence in the number of scales,
the volume and the cutoff.  It also records the adversarial boundary: with no
decay (`θ = 1`) the history debt is unbounded, so the decay hypothesis is
load-bearing.

Nothing here supplies the literal kernel `R_{j,k}` of a renormalisation-group
map; this is the consumer side, stated in the form the source-facing estimate
should be delivered in.
-/
import Mathlib

namespace YangMills

open Finset

/-- `beta` responds to its coupling history with kernel `R`: changing the
history changes the coefficient by at most the response-weighted change. -/
def HasHistoryResponse (beta : ℕ → (ℕ → ℝ) → ℝ) (R : ℕ → ℕ → ℝ) : Prop :=
  ∀ j g g', |beta j g - beta j g'| ≤ ∑ k ∈ range j, |R j k| * |g k - g' k|

/-- Geometric decay of the response kernel in the scale separation `j − k`. -/
def HasResponseDecay (R : ℕ → ℕ → ℝ) (C theta : ℝ) : Prop :=
  ∀ j k, k < j → |R j k| ≤ C * theta ^ (j - k)

/-- The scale-separation sum `∑_{k<j} θ^{j−k}` is bounded by `θ/(1−θ)`,
uniformly in `j`. -/
lemma responseSum_le {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1) (j : ℕ) :
    ∑ k ∈ range j, theta ^ (j - k) ≤ theta / (1 - theta) := by
  have hpos : (0 : ℝ) < 1 - theta := by linarith
  induction j with
  | zero => simp; positivity
  | succ j ih =>
    have hsplit : ∑ k ∈ range (j + 1), theta ^ (j + 1 - k)
        = theta * (1 + ∑ k ∈ range j, theta ^ (j - k)) := by
      rw [Finset.sum_range_succ]
      have hlast : theta ^ (j + 1 - j) = theta := by
        have : j + 1 - j = 1 := by omega
        rw [this, pow_one]
      have hrest : ∀ k ∈ range j, theta ^ (j + 1 - k) = theta * theta ^ (j - k) := by
        intro k hk
        have hkj : k < j := Finset.mem_range.mp hk
        have he : j + 1 - k = (j - k) + 1 := by omega
        rw [he, pow_succ]
        ring
      rw [Finset.sum_congr rfl hrest, hlast, ← Finset.mul_sum]
      ring
    rw [hsplit]
    have hstep : theta * (1 + ∑ k ∈ range j, theta ^ (j - k))
        ≤ theta * (1 + theta / (1 - theta)) := by
      have hadd : 1 + ∑ k ∈ range j, theta ^ (j - k) ≤ 1 + theta / (1 - theta) := by
        linarith [ih]
      exact mul_le_mul_of_nonneg_left hadd h0
    have hid : theta * (1 + theta / (1 - theta)) = theta / (1 - theta) := by
      field_simp
      ring
    linarith [hstep, hid.le, hid.ge]

/-- **`BalabanBetaHistoryResponseDecay` (consumer form).**  A geometrically
decaying response kernel gives a history debt bounded uniformly in the shell
index by `C · B · θ/(1−θ)`. -/
theorem historyResponse_bound {beta : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ} {C theta B : ℝ}
    (hresp : HasHistoryResponse beta R) (hdec : HasResponseDecay R C theta)
    (hC : 0 ≤ C) (h0 : 0 ≤ theta) (h1 : theta < 1)
    {g g' : ℕ → ℝ} (hB : ∀ k, |g k - g' k| ≤ B) (j : ℕ) :
    |beta j g - beta j g'| ≤ C * B * (theta / (1 - theta)) := by
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hterm : ∀ k ∈ range j, |R j k| * |g k - g' k| ≤ C * B * theta ^ (j - k) := by
    intro k hk
    have hkj : k < j := Finset.mem_range.mp hk
    have h2 : |R j k| ≤ C * theta ^ (j - k) := hdec j k hkj
    have hpow : 0 ≤ theta ^ (j - k) := pow_nonneg h0 _
    calc |R j k| * |g k - g' k| ≤ (C * theta ^ (j - k)) * B :=
          mul_le_mul h2 (hB k) (abs_nonneg _) (mul_nonneg hC hpow)
      _ = C * B * theta ^ (j - k) := by ring
  calc |beta j g - beta j g'| ≤ ∑ k ∈ range j, |R j k| * |g k - g' k| := hresp j g g'
    _ ≤ ∑ k ∈ range j, C * B * theta ^ (j - k) := Finset.sum_le_sum hterm
    _ = C * B * ∑ k ∈ range j, theta ^ (j - k) := by rw [Finset.mul_sum]
    _ ≤ C * B * (theta / (1 - theta)) :=
        mul_le_mul_of_nonneg_left (responseSum_le h0 h1 j) (mul_nonneg hC hBnn)

/-- **Positivity gate on a history.**  If the coefficient at the reference
history is at least `b` and the history debt is strictly smaller, the coefficient
on the perturbed history is still positive — uniformly in the shell index. -/
theorem beta_pos_of_historyResponse {beta : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ}
    {C theta B b : ℝ}
    (hresp : HasHistoryResponse beta R) (hdec : HasResponseDecay R C theta)
    (hC : 0 ≤ C) (h0 : 0 ≤ theta) (h1 : theta < 1)
    {g g' : ℕ → ℝ} (hB : ∀ k, |g k - g' k| ≤ B) (j : ℕ)
    (href : b ≤ beta j g') (hgate : C * B * (theta / (1 - theta)) < b) :
    0 < beta j g := by
  have hbound := historyResponse_bound hresp hdec hC h0 h1 hB j
  have := abs_le.mp hbound
  linarith [this.1, this.2]

/-- **Non-vacuity.**  The hypotheses of `historyResponse_bound` are jointly
satisfiable by an actual coefficient family: the geometrically weighted history
`β_j(g) = ∑_{k<j} θ^{j−k} g_k` has response kernel `θ^{j−k}` with `C = 1`. -/
theorem historyResponse_nonvacuous {theta : ℝ} (h0 : 0 ≤ theta) :
    HasHistoryResponse (fun j g => ∑ k ∈ range j, theta ^ (j - k) * g k)
      (fun j k => theta ^ (j - k)) ∧
    HasResponseDecay (fun j k => theta ^ (j - k)) 1 theta := by
  constructor
  · intro j g g'
    have hd : (∑ k ∈ range j, theta ^ (j - k) * g k) - ∑ k ∈ range j, theta ^ (j - k) * g' k
        = ∑ k ∈ range j, theta ^ (j - k) * (g k - g' k) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only []
    rw [hd]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
    intro k _
    rw [abs_mul]
  · intro j k _
    rw [one_mul, abs_of_nonneg (pow_nonneg h0 _)]

/-- **Adversarial boundary: no decay, no budget.**  With `θ = 1` and unit
response the history debt `∑_{k<j} 1` exceeds every constant, so the geometric
decay hypothesis cannot be dropped. -/
theorem no_decay_no_budget (M : ℝ) : ∃ j : ℕ, M < ∑ _k ∈ range j, (1 : ℝ) := by
  obtain ⟨j, hj⟩ := exists_nat_gt M
  refine ⟨j, ?_⟩
  simpa using hj

end YangMills
