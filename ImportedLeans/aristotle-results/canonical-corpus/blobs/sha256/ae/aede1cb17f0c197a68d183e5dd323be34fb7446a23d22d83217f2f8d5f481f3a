/-
# Row A1: the literal source package, and what it does and does not buy

The current recut of Row A1 names exactly four literal source data:

    (1)  S^literal ⪯ 0  and a nonzero literal bubble   (paramagnetic sign),
    (2)  β Z_j ≥ b_Z > 0                               uniformly in the shell,
    (3)  |β Int_j| ≤ C_int g_j^ρ,                      ρ > 0,
    (4)  R_{j,k} = A_j ∏_{i=k}^{j-1} J_i  with  |J_i| ≤ θ < 1,  |A_j| ≤ C_R,

and asserts that these produce the Row A1 margin

    b_− = b_Z − C_int γ^ρ − C_R B θ/(1−θ) > 0.

This module proves that assertion, and proves the separation that the recut
insists on: **(1) is a sign, not a floor**.

* `historyDebt_of_oneStepSources` — item (4) in its literal one-step form:
  the head factor `A_j` and the one-step effective-coupling factors `J_i` alone
  (no assumption of a whole-state contraction) give the uniform history debt
  `C_R B θ/(1−θ)`, via the already-proved chain rule.

* `interactionBound_of_couplingBound` — item (3) at a coupling bounded by `γ`
  gives the uniform interaction debt `C_int γ^ρ`.

* `A1LiteralSource` / `A1_literal_lower_bound` / `A1_literal_beta_pos` — the
  assembly: the four data give `β_j(g) ≥ b_−` for every shell `j`, uniformly in
  the number of scales, the volume and the cutoff, hence `β_j(g) > 0` as soon as
  `b_− > 0`.

* `A1LiteralSource.nontrivial` — a witness of the package with genuinely nonzero
  interaction and genuinely nonzero history response and positive margin, so the
  assembly is not vacuous.

* `paramagnetic_sign_not_uniform_floor` and
  `paramagneticFamily_betaTrace_tendsto_zero` — the separation.  Every member of
  an explicit family of literal paramagnetic instances satisfies the sign
  criterion of `betaTrace_pos_of_paramagnetic` (Gram propagator, symmetric first
  variation, negative semidefinite second variation, non-annihilated bubble) and
  therefore has a *strictly positive* one-loop coefficient — yet the coefficients
  tend to `0`.  So "positive at every finite instance" is strictly weaker than
  "≥ b_Z > 0 uniformly": item (2) does not follow from item (1) and remains a
  separate source obligation.

No numerical value of `b_Z`, `C_int`, `ρ`, `γ`, `C_R`, `θ`, `B` is asserted
anywhere in this file.
-/
import RequestProject.YangMills.HistoryChainRule
import RequestProject.YangMills.SeagullSign

namespace YangMills

open Finset Matrix

/-! ## Item (4): the uniform history debt from literal one-step source factors -/

/-- **The uniform history debt from the literal one-step factors.**  If the
response kernel factorises through the actual one-step source data,
`R_{j,k} = A_j ∏_{i=k}^{j−1} J_i`, with a bounded head `|A_j| ≤ C_R` and
one-step effective-coupling factors `|J_i| ≤ θ < 1`, then the shell coefficient
moves by at most `C_R B θ/(1−θ)` over a history displacement budget `B` —
uniformly in the shell index.  No contraction property of a whole-state map is
used. -/
theorem historyDebt_of_oneStepSources {beta : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ}
    {A J : ℕ → ℝ} {CR theta B : ℝ}
    (hresp : HasHistoryResponse beta R) (hfac : HasChainFactorisation R A J)
    (hA : ∀ j, |A j| ≤ CR) (hJ : ∀ i, |J i| ≤ theta) (h1 : theta < 1)
    {g g' : ℕ → ℝ} (hB : ∀ k, |g k - g' k| ≤ B) (j : ℕ) :
    |beta j g - beta j g'| ≤ CR * B * (theta / (1 - theta)) :=
  historyResponse_bound hresp (responseDecay_of_chainRule hfac hA hJ)
    (le_trans (abs_nonneg _) (hA 0)) (le_trans (abs_nonneg _) (hJ 0)) h1 hB j

/-! ## Item (3): the uniform interaction debt at a bounded coupling -/

/-- **The uniform interaction debt.**  A finite-`g` interaction estimate
`|β Int_j| ≤ C_int g_j^ρ` with `ρ > 0` and a coupling bounded by `γ` on the
trajectory gives the uniform bound `C_int γ^ρ`. -/
theorem interactionBound_of_couplingBound {x Cint gamma rho : ℝ}
    (hCint : 0 ≤ Cint) (hrho : 0 ≤ rho) (hx : 0 ≤ x) (hxg : x ≤ gamma)
    {b : ℝ} (hb : |b| ≤ Cint * x ^ rho) :
    |b| ≤ Cint * gamma ^ rho :=
  le_trans hb (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxg hrho) hCint)

/-! ## The assembly -/

/-- **The literal A1 source package.**  A bundle of exactly the four literal
source data of the current Row A1 recut, stated for a shell coefficient
`beta = betaZ + betaInt` along a coupling history `g` with reference history
`gref`. -/
structure A1LiteralSource where
  /-- the shell coefficient -/
  beta : ℕ → (ℕ → ℝ) → ℝ
  /-- its Gaussian (constrained-determinant) part -/
  betaZ : ℕ → (ℕ → ℝ) → ℝ
  /-- its nonlinear interaction part -/
  betaInt : ℕ → (ℕ → ℝ) → ℝ
  /-- the history-response kernel `R_{j,k} = ∂β_j/∂g_k` -/
  R : ℕ → ℕ → ℝ
  /-- the one-step head factors `A_j` -/
  head : ℕ → ℝ
  /-- the one-step effective-coupling factors `J_i` -/
  step : ℕ → ℝ
  /-- the actual coupling history -/
  g : ℕ → ℝ
  /-- the reference history at which the Gaussian floor is available -/
  gref : ℕ → ℝ
  /-- the uniform Gaussian floor `b_Z` -/
  bZ : ℝ
  /-- the interaction constant `C_int` -/
  Cint : ℝ
  /-- the coupling ceiling `γ` -/
  gamma : ℝ
  /-- the interaction exponent `ρ` -/
  rho : ℝ
  /-- the head bound `C_R` -/
  CR : ℝ
  /-- the one-step contraction factor `θ` -/
  theta : ℝ
  /-- the history displacement budget `B` -/
  B : ℝ
  split : ∀ j g, beta j g = betaZ j g + betaInt j g
  resp : HasHistoryResponse betaZ R
  /-- item (4), first half: the chain identification `R_{j,k} = A_j ∏ J_i` -/
  chain : HasChainFactorisation R head step
  /-- item (4), second half: `|A_j| ≤ C_R` -/
  headBound : ∀ j, |head j| ≤ CR
  /-- item (4), second half: `|J_i| ≤ θ` -/
  stepBound : ∀ i, |step i| ≤ theta
  /-- item (4), second half: `θ < 1` -/
  thetaLtOne : theta < 1
  /-- item (2): the uniform Gaussian floor -/
  gaussianFloor : ∀ j, bZ ≤ betaZ j gref
  /-- the history displacement budget -/
  budget : ∀ k, |g k - gref k| ≤ B
  CintNonneg : 0 ≤ Cint
  rhoNonneg : 0 ≤ rho
  couplingNonneg : ∀ j, 0 ≤ g j
  couplingBound : ∀ j, g j ≤ gamma
  /-- item (3): the finite-`g` interaction debt -/
  interaction : ∀ j, |betaInt j g| ≤ Cint * (g j) ^ rho

namespace A1LiteralSource

variable (d : A1LiteralSource)

/-- The Row A1 margin produced by the package:
`b_− = b_Z − C_int γ^ρ − C_R B θ/(1−θ)`. -/
noncomputable def margin : ℝ :=
  a1Margin d.bZ (d.Cint * d.gamma ^ d.rho) d.CR d.B d.theta

lemma margin_eq :
    d.margin = d.bZ - d.Cint * d.gamma ^ d.rho
      - d.CR * d.B * (d.theta / (1 - d.theta)) := rfl

end A1LiteralSource

/-- **Row A1 from the literal source package.**  The four literal source data
give the uniform lower bound `β_j(g) ≥ b_−` for every shell index `j`. -/
theorem A1_literal_lower_bound (d : A1LiteralSource) (j : ℕ) :
    d.margin ≤ d.beta j d.g := by
  have hCR : 0 ≤ d.CR := le_trans (abs_nonneg _) (d.headBound 0)
  have h0 : 0 ≤ d.theta := le_trans (abs_nonneg _) (d.stepBound 0)
  have hdec : HasResponseDecay d.R d.CR d.theta :=
    responseDecay_of_chainRule d.chain d.headBound d.stepBound
  have hInt : |d.betaInt j d.g| ≤ d.Cint * d.gamma ^ d.rho :=
    interactionBound_of_couplingBound d.CintNonneg d.rhoNonneg
      (d.couplingNonneg j) (d.couplingBound j) (d.interaction j)
  exact A1_margin_lower_bound d.split d.resp hdec hCR h0 d.thetaLtOne
    d.budget (d.gaussianFloor j) hInt

/-- **Row A1 closes when the literal margin is positive.** -/
theorem A1_literal_beta_pos (d : A1LiteralSource) (hmargin : 0 < d.margin) (j : ℕ) :
    0 < d.beta j d.g :=
  lt_of_lt_of_le hmargin (A1_literal_lower_bound d j)

/-! ## Non-vacuity of the assembly -/

/-- An explicit inhabitant of `A1LiteralSource` with a genuinely nonzero
interaction part and a genuinely nonzero history-response kernel, whose margin is
strictly positive.  So `A1_literal_beta_pos` is not reached through a
contradictory hypothesis set. -/
noncomputable def witnessSource : A1LiteralSource where
  beta := fun j g => (1 + ∑ k ∈ range j, (1 / 2 : ℝ) * (1 / 2) ^ (j - k) * g k) + g j / 2
  betaZ := fun j g => 1 + ∑ k ∈ range j, (1 / 2 : ℝ) * (1 / 2) ^ (j - k) * g k
  betaInt := fun j g => g j / 2
  R := fun j k => (1 / 2 : ℝ) * (1 / 2) ^ (j - k)
  head := fun _ => 1 / 2
  step := fun _ => 1 / 2
  g := fun _ => 1 / 8
  gref := fun _ => 0
  bZ := 1
  Cint := 1
  gamma := 1 / 8
  rho := 1
  CR := 1
  theta := 1 / 2
  B := 1 / 8
  split := by intro j g; rfl
  resp := by
    intro j g g'
    have h : (1 + ∑ k ∈ range j, (1 / 2 : ℝ) * (1 / 2) ^ (j - k) * g k)
          - (1 + ∑ k ∈ range j, (1 / 2 : ℝ) * (1 / 2) ^ (j - k) * g' k)
        = ∑ k ∈ range j, ((1 / 2 : ℝ) * (1 / 2) ^ (j - k)) * (g k - g' k) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [h]
    calc |∑ k ∈ range j, ((1 / 2 : ℝ) * (1 / 2) ^ (j - k)) * (g k - g' k)|
        ≤ ∑ k ∈ range j, |((1 / 2 : ℝ) * (1 / 2) ^ (j - k)) * (g k - g' k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ range j, |(1 / 2 : ℝ) * (1 / 2) ^ (j - k)| * |g k - g' k| := by
          simp [abs_mul]
  chain := by
    intro j k _
    simp [Finset.prod_const, Nat.card_Ico]
  headBound := by intro j; rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]; norm_num
  stepBound := by intro i; rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
  thetaLtOne := by norm_num
  gaussianFloor := by intro j; simp
  budget := by
    intro k
    rw [show (1:ℝ) / 8 - 0 = 1 / 8 by ring, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 8)]
  CintNonneg := by norm_num
  rhoNonneg := by norm_num
  couplingNonneg := by intro j; norm_num
  couplingBound := by intro j; norm_num
  interaction := by
    intro j
    rw [Real.rpow_one, show (1:ℝ) / 8 / 2 = 1 / 16 by ring,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 16)]
    norm_num

theorem witnessSource_margin_pos : 0 < witnessSource.margin := by
  rw [A1LiteralSource.margin_eq]
  norm_num [witnessSource]

theorem witnessSource_beta_pos (j : ℕ) : 0 < witnessSource.beta j witnessSource.g :=
  A1_literal_beta_pos _ witnessSource_margin_pos j

/-! ## The separation: a sign is not a floor -/

/-- The `1×1` Gram factor `C(ε) = ε·1`, whose Gram propagator is `ε²·1`. -/
noncomputable def scaledGramFactor (eps : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  eps • (1 : Matrix (Fin 1) (Fin 1) ℝ)

/-- The literal one-loop coefficient of the scaled paramagnetic instance:
Gram propagator `ε²·1`, symmetric first variation `1`, second variation
`−0ᵀ0 = 0` (negative semidefinite). -/
lemma betaTrace_scaledGram (eps : ℝ) :
    betaTrace ((scaledGramFactor eps)ᵀ * scaledGramFactor eps) 1 1
        (-((0 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 0)) = 1 / 2 * eps ^ 4 := by
  simp [betaTrace, scaledGramFactor, smul_smul]
  ring

/-- **Positive at every finite instance is not a uniform floor.**  For every
`b > 0` there is a literal instance satisfying the full paramagnetic sign
criterion — Gram propagator, symmetric first variation, negative semidefinite
second variation, and a bubble that the propagator does not annihilate — whose
one-loop coefficient is strictly positive but smaller than `b`.

Hence item (1) of the source package (the seagull sign) cannot be upgraded to
item (2) (the uniform Gaussian floor `β Z_j ≥ b_Z > 0`); the two are genuinely
separate obligations. -/
theorem paramagnetic_sign_not_uniform_floor (b : ℝ) (hb : 0 < b) :
    ∃ C W : Matrix (Fin 1) (Fin 1) ℝ,
      ((Cᵀ * C) * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (Cᵀ * C) ≠ 0) ∧
      (0 < betaTrace (Cᵀ * C) 1 1 (-(Wᵀ * W)) ∧
        betaTrace (Cᵀ * C) 1 1 (-(Wᵀ * W)) < b) := by
  set eps : ℝ := min 1 b with heps
  have heps0 : 0 < eps := lt_min one_pos hb
  have heps1 : eps ≤ 1 := min_le_left _ _
  have hepsb : eps ≤ b := min_le_right _ _
  refine ⟨scaledGramFactor eps, 0, ?_, ?_, ?_⟩
  · have hM : ((scaledGramFactor eps)ᵀ * scaledGramFactor eps)
        * (1 : Matrix (Fin 1) (Fin 1) ℝ)
        * ((scaledGramFactor eps)ᵀ * scaledGramFactor eps)
        = (eps ^ 4) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      simp [scaledGramFactor, smul_smul]
      ring_nf
    rw [hM]
    intro hzero
    have h00 := congrFun (congrFun hzero 0) 0
    simp at h00
    exact absurd h00 (ne_of_gt (by positivity))
  · rw [betaTrace_scaledGram]
    positivity
  · rw [betaTrace_scaledGram]
    have h4 : eps ^ 4 ≤ eps := by
      calc eps ^ 4 ≤ eps ^ 1 := pow_le_pow_of_le_one (le_of_lt heps0) heps1 (by norm_num)
        _ = eps := pow_one _
    nlinarith

/-- The same family, as a sequence: every member has a strictly positive
coefficient by the paramagnetic criterion, and the coefficients tend to `0`. -/
theorem paramagneticFamily_betaTrace_tendsto_zero :
    Filter.Tendsto
      (fun n : ℕ => betaTrace ((scaledGramFactor (1 / (n + 1)))ᵀ
          * scaledGramFactor (1 / (n + 1))) 1 1
        (-((0 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 0)))
      Filter.atTop (nhds 0) := by
  simp only [betaTrace_scaledGram]
  have h : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using (h.pow 4).const_mul (1 / 2 : ℝ)

end YangMills
