/-
# Row A1 — the corrected margin `b_patch − C_β γ⁴ − C_H γ/2`

The reduced margin of `A1ReducedMargin` was
`v²/32 − (A/(1−Kγ))γ^ρ − D·B`, with six generic parameters.  Three of them are
now replaced by physical producers proved elsewhere in this development:

* the Gaussian floor `b_patch` comes from **one positive-volume momentum patch**
  (`PositivePatchEnclosure`) rather than from a single corner momentum — which
  `WilsonCubicVertex` shows to annihilate the diagonal first variation, and
  `SingleModeWeight` shows to carry vanishing normalised weight anyway;
* the interaction debt comes from the **five channelwise quartic majorants**
  (`FiveChannelQuartic`), fixing `ρ = 4` and `C_int = C_β = ∑_k c_k` with no
  Cauchy pair `(A,K)`;
* the history debt comes from **scale-local localization of the irrelevant
  memory** (`LocalizedHistoryMemory`), giving `H_irr ≤ C_H γ/2` uniformly in the
  history length — and *only* for the irrelevant part: the marginal running
  coupling is not assumed to forget its predecessors, which is why the marginal
  memory bound `H_marg` appears explicitly in the margin below.

`correctedMargin` is therefore

    b_patch − C_β γ⁴ − (C_H γ/2 + H_marg)·B,

and `correctedMargin_promptForm` records that with no marginal memory and a unit
displacement budget this is exactly `b_patch − C_β γ⁴ − C_H γ/2`.

`A1_corrected_lower_bound` proves `β_j(g) ≥ correctedMargin` for every shell
index, uniformly in the number of scales, the volume and the cutoff, and
`A1_corrected_beta_pos` converts a positive margin into strict positivity.

**Honest status.**  Nothing here asserts a value for `b_patch`, the channel
coefficients `c_k`, the localization constants `(C_loc, θ)`, or `H_marg` for
Bałaban's construction.  Row A1 is *not* closed; what is closed is everything
downstream of those data.
-/
import RequestProject.YangMills.FiveChannelQuartic
import RequestProject.YangMills.LocalizedHistoryMemory
import RequestProject.YangMills.HistoryDebtCriteria

namespace YangMills

open Finset

/-- The corrected Row A1 margin. -/
noncomputable def correctedMargin (bpatch Cb CHconst gamma Hmarg B : ℝ) : ℝ :=
  bpatch - Cb * gamma ^ 4 - (CHconst * gamma / 2 + Hmarg) * B

/-- With no marginal memory and a unit displacement budget the corrected margin
is exactly `b_patch − C_β γ⁴ − C_H γ/2`. -/
theorem correctedMargin_promptForm (bpatch Cb CHconst gamma : ℝ) :
    correctedMargin bpatch Cb CHconst gamma 0 1
      = bpatch - Cb * gamma ^ 4 - CHconst * gamma / 2 := by
  unfold correctedMargin; ring

/-- Lower-bound variant of `A1_lower_bound_of_summableKernel`: only a *lower*
bound on the interaction remainder is needed, which is what the channelwise
quartic majorants produce. -/
theorem A1_lower_bound_of_lowerInteraction
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ} {bZ Rint D B : ℝ} {j : ℕ}
    (hsplit : ∀ j g, beta j g = betaZ j g + betaInt j g)
    (hresp : HasHistoryResponse betaZ R)
    (hsum : ∀ j, ∑ k ∈ range j, |R j k| ≤ D)
    {g gref : ℕ → ℝ} (hB : ∀ k, |g k - gref k| ≤ B)
    (hZ : bZ ≤ betaZ j gref) (hInt : -Rint ≤ betaInt j g) :
    bZ - Rint - D * B ≤ beta j g := by
  have hdebt : |betaZ j g - betaZ j gref| ≤ D * B :=
    historyDebt_of_summableKernel hresp hsum hB j
  have h1 := (abs_le.mp hdebt).1
  rw [hsplit j g]
  linarith

/-- **Row A1 with the corrected margin.**  From
1. a Gaussian floor `b_patch` for the reference trajectory,
2. the five channelwise quartic majorants for the nonlinear remainder,
3. scale-local localization of the irrelevant memory, and
4. a bound on the marginal memory,
the shell coefficient obeys `β_j(g) ≥ correctedMargin`, uniformly in the shell
index, the number of scales, the volume and the cutoff. -/
theorem A1_corrected_lower_bound
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ}
    {R Rirr Rmarg : ℕ → ℕ → ℝ} {ch : ℕ → BetaChannel → ℝ}
    {c : BetaChannel → ℝ} {g gref : ℕ → ℝ}
    {bpatch gamma theta Cloc Hmarg B : ℝ}
    -- Gaussian floor from the positive-volume patch
    (hZ : ∀ j, bpatch ≤ betaZ j gref)
    (hsplit : ∀ j g, beta j g = betaZ j g + betaInt j g)
    -- five-channel quartic data
    (hchan : ∀ j, betaInt j g = ∑ k, ch j k)
    (hmaj : ∀ j k, |ch j k| ≤ c k * (g j) ^ 4)
    (hc : ∀ k, 0 ≤ c k) (hg0 : ∀ j, 0 ≤ g j) (hgg : ∀ j, g j ≤ gamma)
    -- localized irrelevant memory plus a marginal memory bound
    (hresp : HasHistoryResponse betaZ R)
    (hRsplit : ∀ j k, R j k = Rirr j k + Rmarg j k)
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (hCloc : 0 ≤ Cloc)
    (hgamma : 0 ≤ gamma)
    (hloc : ∀ j k, k < j → |Rirr j k| ≤ Cloc * gamma * theta ^ (j - k))
    (hmarg : ∀ j, ∑ k ∈ range j, |Rmarg j k| ≤ Hmarg)
    (hB : ∀ k, |g k - gref k| ≤ B)
    (j : ℕ) :
    correctedMargin bpatch (Cbeta c) (CH Cloc theta) gamma Hmarg B ≤ beta j g := by
  have hInt : -(Cbeta c * gamma ^ 4) ≤ betaInt j g := by
    have := betaInt_ge_on_trajectory (betaInt := fun t => betaInt j g)
      (ch := fun k _ => ch j k) (c := c) (g := g j) (gamma := gamma)
      (by simpa using hchan j) (fun k => hmaj j k) hc (hg0 j) (hgg j)
    simpa [neg_mul] using this
  have hsum : ∀ i, ∑ k ∈ range i, |R i k| ≤ CH Cloc theta * gamma / 2 + Hmarg := by
    intro i
    exact totalMemory_le_of_split hRsplit
      (fun i' => irrelevantMemory_le_CH_half htheta0 htheta1 hCloc hgamma hloc i')
      hmarg i
  have := A1_lower_bound_of_lowerInteraction (bZ := bpatch)
    (Rint := Cbeta c * gamma ^ 4) (D := CH Cloc theta * gamma / 2 + Hmarg)
    hsplit hresp hsum hB (hZ j) hInt
  simpa [correctedMargin] using this

/-- **Positivity of every shell coefficient once the corrected margin is
positive.** -/
theorem A1_corrected_beta_pos
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ}
    {R Rirr Rmarg : ℕ → ℕ → ℝ} {ch : ℕ → BetaChannel → ℝ}
    {c : BetaChannel → ℝ} {g gref : ℕ → ℝ}
    {bpatch gamma theta Cloc Hmarg B : ℝ}
    (hZ : ∀ j, bpatch ≤ betaZ j gref)
    (hsplit : ∀ j g, beta j g = betaZ j g + betaInt j g)
    (hchan : ∀ j, betaInt j g = ∑ k, ch j k)
    (hmaj : ∀ j k, |ch j k| ≤ c k * (g j) ^ 4)
    (hc : ∀ k, 0 ≤ c k) (hg0 : ∀ j, 0 ≤ g j) (hgg : ∀ j, g j ≤ gamma)
    (hresp : HasHistoryResponse betaZ R)
    (hRsplit : ∀ j k, R j k = Rirr j k + Rmarg j k)
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (hCloc : 0 ≤ Cloc)
    (hgamma : 0 ≤ gamma)
    (hloc : ∀ j k, k < j → |Rirr j k| ≤ Cloc * gamma * theta ^ (j - k))
    (hmarg : ∀ j, ∑ k ∈ range j, |Rmarg j k| ≤ Hmarg)
    (hB : ∀ k, |g k - gref k| ≤ B)
    (hmargin : 0 < correctedMargin bpatch (Cbeta c) (CH Cloc theta) gamma Hmarg B)
    (j : ℕ) :
    0 < beta j g :=
  lt_of_lt_of_le hmargin
    (A1_corrected_lower_bound hZ hsplit hchan hmaj hc hg0 hgg hresp hRsplit htheta0
      htheta1 hCloc hgamma hloc hmarg hB j)

/-! ## The corrected target inequality -/

/-- The closing condition in checkable form. -/
theorem correctedMargin_pos_iff (bpatch Cb CHconst gamma Hmarg B : ℝ) :
    0 < correctedMargin bpatch Cb CHconst gamma Hmarg B
      ↔ Cb * gamma ^ 4 + (CHconst * gamma / 2 + Hmarg) * B < bpatch := by
  unfold correctedMargin
  constructor <;> intro h <;> linarith

/-- The corrected inequality is satisfiable: an explicit admissible tuple. -/
theorem correctedMargin_example :
    0 < correctedMargin (1 / 10) 1 1 (1 / 10) 0 1 := by
  unfold correctedMargin
  norm_num

/-! ## Non-vacuity of the corrected assembly

The hypothesis package of `A1_corrected_lower_bound` is inhabited by an explicit
family with a *nonzero* interaction remainder and a *nonzero* history response,
so the assembly is not vacuous. -/

/-- Witness Gaussian coefficient: a floor plus a genuinely history-dependent
geometrically weighted contribution. -/
noncomputable def witnessBetaZ (j : ℕ) (g : ℕ → ℝ) : ℝ :=
  1 / 2 + (1 / 4) * ∑ k ∈ range j, (1 / 2 : ℝ) ^ (j - k) * g k

/-- Witness interaction remainder: genuinely nonzero and quartic. -/
noncomputable def witnessBetaInt (j : ℕ) (g : ℕ → ℝ) : ℝ := -(g j) ^ 4

noncomputable def witnessBeta (j : ℕ) (g : ℕ → ℝ) : ℝ :=
  witnessBetaZ j g + witnessBetaInt j g

/-- Witness response kernel: nonzero at every preceding scale. -/
noncomputable def witnessKernel (j k : ℕ) : ℝ := (1 / 4) * (1 / 2 : ℝ) ^ (j - k)

theorem witnessKernel_response : HasHistoryResponse witnessBetaZ witnessKernel := by
  intro j g g'
  have hsplit : ∑ k ∈ range j, (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (j - k) * (g k - g' k)
      = (1 / 4) * (∑ k ∈ range j, (1 / 2 : ℝ) ^ (j - k) * g k)
        - (1 / 4) * ∑ k ∈ range j, (1 / 2 : ℝ) ^ (j - k) * g' k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hdiff : witnessBetaZ j g - witnessBetaZ j g'
      = ∑ k ∈ range j, (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (j - k) * (g k - g' k) := by
    rw [hsplit]
    unfold witnessBetaZ
    ring
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, witnessKernel,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 4) * (1 / 2 : ℝ) ^ (j - k))]

/-- **The corrected package is satisfiable.**  Applying `A1_corrected_beta_pos`
to the witness family — nonzero quartic interaction, nonzero history response —
gives strict positivity of every shell coefficient. -/
theorem A1_corrected_nonvacuous (j : ℕ) : 0 < witnessBeta j (fun _ => 1 / 10) := by
  have hcard : ∑ _k : BetaChannel, (1 : ℝ) = 5 := by
    simp [Finset.sum_const, Finset.card_univ]
    rfl
  refine A1_corrected_beta_pos (betaZ := witnessBetaZ) (betaInt := witnessBetaInt)
    (R := witnessKernel) (Rirr := witnessKernel) (Rmarg := fun _ _ => 0)
    (ch := fun j' k => if k = BetaChannel.determinant then -((1 : ℝ) / 10) ^ 4 else 0)
    (c := fun _ => 1) (g := fun _ => 1 / 10) (gref := fun _ => 0)
    (bpatch := 1 / 2) (gamma := 1 / 10) (theta := 1 / 2) (Cloc := 5 / 2)
    (Hmarg := 0) (B := 1 / 10)
    (fun j' => by
      have : (0 : ℝ) ≤ ∑ k ∈ range j', (1 / 2 : ℝ) ^ (j' - k) * 0 := by simp
      simp [witnessBetaZ])
    (fun _ _ => rfl)
    (fun j' => by
      simp [witnessBetaInt, Finset.sum_ite_eq'])
    (fun j' k => by
      by_cases h : k = BetaChannel.determinant <;> simp [h])
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => le_rfl)
    witnessKernel_response (fun _ _ => by ring)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun j' k _ => by
      rw [witnessKernel, abs_of_nonneg (by positivity)]
      have : (5 / 2 : ℝ) * (1 / 10) = 1 / 4 := by norm_num
      rw [this])
    (fun _ => by simp)
    (fun k => by norm_num)
    ?_ j
  have hC : Cbeta (fun _ : BetaChannel => (1 : ℝ)) = 5 := by
    unfold Cbeta; exact hcard
  have hCH : CH (5 / 2 : ℝ) (1 / 2) = 5 := by
    unfold CH; norm_num
  rw [hC, hCH]
  unfold correctedMargin
  norm_num

/-- The corrected margin is genuinely weaker to satisfy than the old reduced
margin at the same data, because the interaction debt is quartic rather than
quadratic: at `γ = 1/10`, `C_β = 1`, the interaction debt drops from `10⁻²` to
`10⁻⁴`. -/
theorem correctedMargin_quartic_gain :
    (1 : ℝ) * (1 / 10 : ℝ) ^ 4 < (1 : ℝ) * (1 / 10 : ℝ) ^ 2 := by norm_num

end YangMills
