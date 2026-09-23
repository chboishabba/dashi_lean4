/-
# Row A1b: geometric response decay from a renormalisation-group chain rule

`BetaHistoryResponse` consumes a geometric bound `|R_{j,k}| ≤ C θ^{j−k}` on the
history-response kernel `R_{j,k} = ∂β_j/∂g_k`.  The recut asks that this bound be
*derived* from renormalisation-group irrelevance rather than postulated.  The
mechanism is the chain rule: an earlier coupling `g_k` reaches the shell
coefficient `β_j` only by being transported through the intervening
renormalisation-group steps,

    ∂β_j/∂g_k = (∂β_j/∂x_j) · ∏_{i=k}^{j−1} (∂x_{i+1}/∂x_i),

so the kernel factorises into a bounded head and a product of one-step transfer
factors.  Irrelevance of the transported operator is exactly the statement that
each one-step factor is at most `L^{−ω} < 1`.

* `HasChainFactorisation` — the chain-rule shape of the kernel.
* `responseDecay_of_chainRule` — a head bounded by `C` and one-step factors
  bounded by `θ ≥ 0` give `HasResponseDecay R C θ`; the exponent `j − k` is
  produced by the cardinality of the intervening steps, not assumed.
* `responseDecay_of_irrelevantChain` — the same with the one-step factors bounded
  by the irrelevance ratio `θ = L^{−ω}`, together with `θ < 1` for `L > 1`,
  `ω > 0`.
* `historyDebt_of_irrelevantChain` — the resulting uniform history debt
  `C · B · θ/(1−θ)`, which is the number entering the Row A1 margin.
* `chainFactorisation_nonvacuous` — the hypotheses are satisfiable by an actual
  kernel.

Nothing here supplies literal one-step derivatives of a renormalisation-group
map; this states precisely which source datum (a uniform one-step irrelevance
factor) suffices, and derives the geometric kernel decay from it.
-/
import RequestProject.YangMills.A1Margin

namespace YangMills

open Finset

/-- **Chain-rule shape of the history-response kernel.**  The response of the
shell coefficient to a coupling `j − k` scales earlier factorises into a head
`A j` and the product of the one-step transfer factors `J i` of the intervening
renormalisation-group steps. -/
def HasChainFactorisation (R : ℕ → ℕ → ℝ) (A J : ℕ → ℝ) : Prop :=
  ∀ j k, k < j → R j k = A j * ∏ i ∈ Ico k j, J i

/-- The product of the intervening one-step factors is bounded by `θ^{j−k}`. -/
lemma abs_prod_chain_le {J : ℕ → ℝ} {theta : ℝ}
    (hJ : ∀ i, |J i| ≤ theta) (k j : ℕ) :
    |∏ i ∈ Ico k j, J i| ≤ theta ^ (j - k) := by
  rw [Finset.abs_prod]
  calc ∏ i ∈ Ico k j, |J i| ≤ ∏ _i ∈ Ico k j, theta :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hJ i)
    _ = theta ^ (j - k) := by rw [Finset.prod_const, Nat.card_Ico]

/-- **Geometric response decay from the chain rule.**  If the kernel has the
chain-rule shape, the head is bounded by `C` and every one-step transfer factor
is bounded by `θ ≥ 0`, then `|R_{j,k}| ≤ C θ^{j−k}`.  The scale-separation
exponent is produced by the number of intervening renormalisation-group steps. -/
theorem responseDecay_of_chainRule {R : ℕ → ℕ → ℝ} {A J : ℕ → ℝ} {C theta : ℝ}
    (hfac : HasChainFactorisation R A J) (hA : ∀ j, |A j| ≤ C)
    (hJ : ∀ i, |J i| ≤ theta) :
    HasResponseDecay R C theta := by
  intro j k hkj
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hA j)
  rw [hfac j k hkj, abs_mul]
  exact mul_le_mul (hA j) (abs_prod_chain_le hJ k j) (abs_nonneg _) hC

/-- **Geometric response decay from renormalisation-group irrelevance.**  If each
one-step transfer factor is suppressed by the irrelevance ratio `L^{−ω}` of the
transported operator, the history-response kernel decays geometrically with
`θ = L^{−ω}`, and that ratio is genuinely `< 1`. -/
theorem responseDecay_of_irrelevantChain {R : ℕ → ℕ → ℝ} {A J : ℕ → ℝ} {C L omega : ℝ}
    (hL : 1 < L) (homega : 0 < omega)
    (hfac : HasChainFactorisation R A J) (hA : ∀ j, |A j| ≤ C)
    (hJ : ∀ i, |J i| ≤ irrelevantRatio L omega) :
    HasResponseDecay R C (irrelevantRatio L omega)
      ∧ irrelevantRatio L omega < 1 := by
  exact ⟨responseDecay_of_chainRule hfac hA hJ, irrelevantRatio_lt_one hL homega⟩

/-- **The history debt produced by an irrelevant chain.**  Combining the chain
rule with irrelevance gives the uniform bound
`|β_j(g) − β_j(g')| ≤ C·B·θ/(1−θ)` with `θ = L^{−ω}`, the third of the three
numbers entering the Row A1 margin. -/
theorem historyDebt_of_irrelevantChain {beta : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ}
    {A J : ℕ → ℝ} {C L omega B : ℝ}
    (hL : 1 < L) (homega : 0 < omega)
    (hresp : HasHistoryResponse beta R)
    (hfac : HasChainFactorisation R A J) (hA : ∀ j, |A j| ≤ C)
    (hJ : ∀ i, |J i| ≤ irrelevantRatio L omega)
    {g g' : ℕ → ℝ} (hB : ∀ k, |g k - g' k| ≤ B) (j : ℕ) :
    |beta j g - beta j g'|
      ≤ C * B * (irrelevantRatio L omega / (1 - irrelevantRatio L omega)) := by
  obtain ⟨hdec, hlt⟩ := responseDecay_of_irrelevantChain hL homega hfac hA hJ
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hA 0)
  exact historyResponse_bound hresp hdec hC
    (irrelevantRatio_nonneg (lt_trans zero_lt_one hL)) hlt hB j

/-- **Non-vacuity.**  The chain-rule hypotheses are satisfiable: the kernel
`R_{j,k} = θ^{j−k}` factorises with head `1` and constant one-step factor `θ`. -/
theorem chainFactorisation_nonvacuous {theta : ℝ} (h0 : 0 ≤ theta) :
    HasChainFactorisation (fun j k => theta ^ (j - k)) (fun _ => 1) (fun _ => theta)
      ∧ HasResponseDecay (fun j k => theta ^ (j - k)) 1 theta := by
  refine ⟨fun j k _ => ?_, ?_⟩
  · simp [Finset.prod_const, Nat.card_Ico]
  · exact responseDecay_of_chainRule (A := fun _ => 1) (J := fun _ => theta)
      (fun j k _ => by simp [Finset.prod_const, Nat.card_Ico])
      (fun j => by simp) (fun i => by rw [abs_of_nonneg h0])

end YangMills
