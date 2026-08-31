/-
# Row A1 — the disposition of the marginal history memory

The corrected Row A1 margin is

    b_patch − C_β γ⁴ − (C_H γ/2 + H_marg)·B  >  0,

and `LocalizedHistoryMemory` controls only the `C_H γ/2` part: the localization
theorem gives exponential forgetting for the *irrelevant* memory, and
`marginalMemory_unbounded` shows that a marginal kernel with no decay makes the
memory sum diverge with the number of scales.  So `H_marg` must be disposed of
honestly, and there are exactly three possibilities: it vanishes by an identity,
it is absorbed, or it stays in the margin as a separate uniform constant.

This file supplies the *absorption* route, which is the one the structure of a
renormalisation-group recursion actually offers, and it does so without
postulating any forgetting for the marginal sector.

The observation is that a marginal coupling does not enter the recursion through
its value at each earlier scale but through the *increments* of the running
coupling: what a marginal direction transports from scale `k` to scale `k+1` is
`g_k − g_{k+1}`.  Formally:

* `HasIncrementResponse` : `|β_j(g) − β_j(g')| ≤ ∑_{k<j} |S_{j,k}| · |Δ_k g − Δ_k g'|`
  with `Δ_k g = g_k − g_{k+1}`.
* `incrementResponse_bound` : a *uniformly bounded* increment kernel `|S| ≤ a`
  — no decay whatsoever — gives the bound `2 a V` where `V` bounds the total
  variation of the two trajectories, uniformly in the shell index.
* `totalVariation_le_of_antitone` : a monotonically decreasing trajectory inside
  `[0,γ]` has total variation at most `γ`.
* `marginalDebt_le_of_increments` : hence the marginal history debt is at most
  `2 a γ` — order `γ`, exactly like the localized irrelevant memory, and *not*
  growing with the number of scales.
* `absorbedMargin_ge_half` : with the marginal debt in that form, one explicit
  root-free coupling choice absorbs all three debts at once and leaves
  `β ≥ b/2 > 0`.

So the honest disposition is: `H_marg` need not be `0` and need not be forgotten
exponentially; it is `O(γ)` as soon as the marginal response acts on the
increments of a monotone running coupling, and then it is absorbed by the same
small-coupling choice as the quartic and irrelevant debts.  If the source
recursion does *not* have that increment structure, the third outcome stands and
`H_marg` remains a separate uniform constant in the margin — which is why the
`Hmarg` field of `correctedMargin` is kept.
-/
import RequestProject.YangMills.A1CorrectedMargin

namespace YangMills

open Finset

/-! ## 1. Increment response and total variation -/

/-- The increment of a coupling trajectory across one scale. -/
def couplingIncrement (g : ℕ → ℝ) (k : ℕ) : ℝ := g k - g (k + 1)

/-- The shell coefficient responds to the *increments* of the coupling history
with kernel `S`. -/
def HasIncrementResponse (beta : ℕ → (ℕ → ℝ) → ℝ) (S : ℕ → ℕ → ℝ) : Prop :=
  ∀ j g g', |beta j g - beta j g'|
    ≤ ∑ k ∈ range j, |S j k| * |couplingIncrement g k - couplingIncrement g' k|

/-- A trajectory has total variation at most `V`. -/
def TotalVariationLe (g : ℕ → ℝ) (V : ℝ) : Prop :=
  ∀ j, ∑ k ∈ range j, |couplingIncrement g k| ≤ V

/-- **A monotonically decreasing trajectory in `[0,γ]` has total variation at
most `γ`.**  The sum telescopes. -/
theorem totalVariationLe_of_antitone {g : ℕ → ℝ} {gamma : ℝ}
    (hanti : ∀ k, g (k + 1) ≤ g k) (hlow : ∀ k, 0 ≤ g k) (hup : ∀ k, g k ≤ gamma) :
    TotalVariationLe g gamma := by
  intro j
  have habs : ∀ k ∈ range j, |couplingIncrement g k| = g k - g (k + 1) := by
    intro k _
    rw [couplingIncrement, abs_of_nonneg (by linarith [hanti k])]
  rw [Finset.sum_congr rfl habs, Finset.sum_range_sub' g j]
  linarith [hlow j, hup 0]

/-- **The marginal memory bound with no forgetting at all.**  A uniformly
bounded increment kernel and two trajectories of total variation at most `V`
give a shell-uniform bound `2aV`. -/
theorem incrementResponse_bound {beta : ℕ → (ℕ → ℝ) → ℝ} {S : ℕ → ℕ → ℝ} {a V : ℝ}
    (hresp : HasIncrementResponse beta S) (hS : ∀ j k, |S j k| ≤ a)
    {g g' : ℕ → ℝ} (hg : TotalVariationLe g V) (hg' : TotalVariationLe g' V)
    (j : ℕ) : |beta j g - beta j g'| ≤ 2 * a * V := by
  have hann : 0 ≤ a := le_trans (abs_nonneg (S 0 0)) (hS 0 0)
  have hterm : ∀ k ∈ range j,
      |S j k| * |couplingIncrement g k - couplingIncrement g' k|
        ≤ a * (|couplingIncrement g k| + |couplingIncrement g' k|) := by
    intro k _
    have h1 : |couplingIncrement g k - couplingIncrement g' k|
        ≤ |couplingIncrement g k| + |couplingIncrement g' k| := abs_sub _ _
    have h2 : |S j k| * |couplingIncrement g k - couplingIncrement g' k|
        ≤ |S j k| * (|couplingIncrement g k| + |couplingIncrement g' k|) :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have h3 : |S j k| * (|couplingIncrement g k| + |couplingIncrement g' k|)
        ≤ a * (|couplingIncrement g k| + |couplingIncrement g' k|) := by
      have hnn : 0 ≤ |couplingIncrement g k| + |couplingIncrement g' k| := by positivity
      exact mul_le_mul_of_nonneg_right (hS j k) hnn
    linarith
  have hsum := Finset.sum_le_sum hterm
  have hsplit : ∑ k ∈ range j, a * (|couplingIncrement g k| + |couplingIncrement g' k|)
      = a * ((∑ k ∈ range j, |couplingIncrement g k|)
          + ∑ k ∈ range j, |couplingIncrement g' k|) := by
    simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hV : (∑ k ∈ range j, |couplingIncrement g k|)
      + ∑ k ∈ range j, |couplingIncrement g' k| ≤ 2 * V := by
    linarith [hg j, hg' j]
  have hfin : ∑ k ∈ range j, |S j k| * |couplingIncrement g k - couplingIncrement g' k|
      ≤ a * (2 * V) := by
    refine le_trans hsum ?_
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hV hann
  have := hresp j g g'
  linarith [this, hfin]

/-- **The marginal history debt is `O(γ)`.**  With the increment structure and a
monotonically decreasing running coupling inside `[0,γ]`, the marginal memory
contributes at most `2aγ`, uniformly in the shell index — no exponential
forgetting is invoked, and nothing grows with the number of scales. -/
theorem marginalDebt_le_of_increments {beta : ℕ → (ℕ → ℝ) → ℝ} {S : ℕ → ℕ → ℝ}
    {a gamma : ℝ} (hresp : HasIncrementResponse beta S) (hS : ∀ j k, |S j k| ≤ a)
    {g g' : ℕ → ℝ}
    (hanti : ∀ k, g (k + 1) ≤ g k) (hlow : ∀ k, 0 ≤ g k) (hup : ∀ k, g k ≤ gamma)
    (hanti' : ∀ k, g' (k + 1) ≤ g' k) (hlow' : ∀ k, 0 ≤ g' k) (hup' : ∀ k, g' k ≤ gamma)
    (j : ℕ) : |beta j g - beta j g'| ≤ 2 * a * gamma :=
  incrementResponse_bound hresp hS (totalVariationLe_of_antitone hanti hlow hup)
    (totalVariationLe_of_antitone hanti' hlow' hup') j

/-! ## 2. One coupling choice absorbs all three debts -/

/-- The margin in the absorbed form: the quartic interaction debt, the localized
irrelevant memory and the marginal increment debt, all against the Gaussian
floor. -/
noncomputable def absorbedMargin (b Cb CHconst a gamma B : ℝ) : ℝ :=
  b - Cb * gamma ^ 4 - (CHconst * gamma / 2) * B - 2 * a * gamma

/-- The root-free coupling choice: `γ_* = b / (2(C_β + C_H B/2 + 2a + 1))`. -/
noncomputable def absorbedCoupling (b Cb CHconst a B : ℝ) : ℝ :=
  b / (2 * (Cb + CHconst * B / 2 + 2 * a + 1))

theorem absorbedCoupling_pos {b Cb CHconst a B : ℝ} (hb : 0 < b) (hCb : 0 ≤ Cb)
    (hCH : 0 ≤ CHconst) (ha : 0 ≤ a) (hB : 0 ≤ B) : 0 < absorbedCoupling b Cb CHconst a B := by
  have hden : 0 < 2 * (Cb + CHconst * B / 2 + 2 * a + 1) := by positivity
  exact div_pos hb hden

theorem absorbedCoupling_le_one {b Cb CHconst a B : ℝ} (hCb : 0 ≤ Cb)
    (hCH : 0 ≤ CHconst) (ha : 0 ≤ a) (hB : 0 ≤ B) (hb1 : b ≤ 1) :
    absorbedCoupling b Cb CHconst a B ≤ 1 := by
  have hden : 0 < 2 * (Cb + CHconst * B / 2 + 2 * a + 1) := by positivity
  rw [absorbedCoupling, div_le_one hden]
  nlinarith

/-- **All three debts are absorbed at once.**  For any positive Gaussian floor
`b ≤ 1` and any finite nonnegative constants, the explicit root-free coupling
`γ_*` leaves at least half the floor. -/
theorem absorbedMargin_ge_half {b Cb CHconst a B gamma : ℝ}
    (hb1 : b ≤ 1) (hCb : 0 ≤ Cb) (hCH : 0 ≤ CHconst) (ha : 0 ≤ a)
    (hB : 0 ≤ B) (hg0 : 0 < gamma) (hg : gamma ≤ absorbedCoupling b Cb CHconst a B) :
    b / 2 ≤ absorbedMargin b Cb CHconst a gamma B := by
  have hden : 0 < 2 * (Cb + CHconst * B / 2 + 2 * a + 1) := by positivity
  have hg1 : gamma ≤ 1 := le_trans hg (absorbedCoupling_le_one hCb hCH ha hB hb1)
  have hpow : gamma ^ 4 ≤ gamma := by
    have := pow_le_pow_of_le_one hg0.le hg1 (by norm_num : 1 ≤ 4)
    simpa using this
  have hquart : Cb * gamma ^ 4 ≤ Cb * gamma := mul_le_mul_of_nonneg_left hpow hCb
  have hkey : gamma * (2 * (Cb + CHconst * B / 2 + 2 * a + 1)) ≤ b := by
    rw [absorbedCoupling, le_div_iff₀ hden] at hg
    linarith
  have hsum : Cb * gamma + (CHconst * gamma / 2) * B + 2 * a * gamma ≤ b / 2 := by
    nlinarith
  rw [absorbedMargin]
  linarith

/-- **The strict positivity of the absorbed margin.** -/
theorem absorbedMargin_pos {b Cb CHconst a B gamma : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hCb : 0 ≤ Cb) (hCH : 0 ≤ CHconst) (ha : 0 ≤ a)
    (hB : 0 ≤ B) (hg0 : 0 < gamma) (hg : gamma ≤ absorbedCoupling b Cb CHconst a B) :
    0 < absorbedMargin b Cb CHconst a gamma B :=
  lt_of_lt_of_le (by linarith) (absorbedMargin_ge_half hb1 hCb hCH ha hB hg0 hg)

/-- **The absorbed margin is the corrected margin with `H_marg` replaced by its
`O(γ)` increment form.**  Comparing with `correctedMargin`, the marginal memory
enters as `2aγ` instead of a scale-independent constant `H_marg·B`. -/
theorem absorbedMargin_eq_correctedMargin_of_marginalDebt
    (b Cb CHconst a gamma B : ℝ) (hB : B ≠ 0) :
    absorbedMargin b Cb CHconst a gamma B
      = correctedMargin b Cb CHconst gamma (2 * a * gamma / B) B := by
  rw [absorbedMargin, correctedMargin]
  field_simp
  ring

end YangMills
