/-
# Row A1 — the five quartic channel coefficients from fourth-derivative data

`FiveChannelQuartic` reduces the nonlinear beta remainder to five channelwise
majorants `|ch_k(g)| ≤ c_k g⁴` and the single constant `C_β = ∑_k c_k`.  It does
not say where a `c_k` comes from, and the temptation is to postulate "some
finite constant".  This file removes that temptation: each channel coefficient
is *produced* by a uniform bound on the channel's fourth derivative in the
coupling.

* `abs_le_quartic_of_fourthDeriv_bound` : a channel that vanishes to third order
  at zero coupling and whose fourth derivative is bounded by `M` on `[0,γ]`
  satisfies `|ch(g)| ≤ (M/6) g⁴` there — Taylor's theorem with the Lagrange
  bound, no free parameter.
* `channelMajorants_of_fourthDeriv` : applied to all five channels at once.
* `Cbeta_of_fourthDerivBounds` : `C_β = (∑_k M_k)/6`.
* `betaInt_ge_of_fourthDerivBounds` : hence `βInt(g) ≥ −((∑_k M_k)/6)·g⁴`, the
  literal second ingredient of the Row A1 margin.

So the remaining source task for the debt side is exactly five numbers: a
uniform bound on the fourth coupling derivative of the determinant, interaction,
chart, gauge and localization channels.  Vanishing to third order at `g = 0` is
the statement that the channel is a genuine *quartic* remainder — the lower
orders having been accounted for in the Gaussian term and in the running
coupling.

**Honest status.**  The five bounds `M_k` are not computed here for Bałaban's
construction, and neither is the third-order vanishing verified for it.  What is
removed is the need for any constant that is not a fourth-derivative bound.
-/
import RequestProject.YangMills.FiveChannelQuartic

namespace YangMills

open Set

/-- **A quartic majorant from a fourth-derivative bound.**  If a channel
vanishes to third order at zero coupling and its fourth derivative is bounded by
`M` on `[0,γ]`, then `|ch(g)| ≤ (M/6)·g⁴` on `[0,γ]`. -/
theorem abs_le_quartic_of_fourthDeriv_bound {ch : ℝ → ℝ} {gamma M : ℝ}
    (hgam : 0 ≤ gamma)
    (hcd : ContDiffOn ℝ 4 ch (Icc 0 gamma))
    (h0 : ch 0 = 0)
    (h1 : iteratedDerivWithin 1 ch (Icc 0 gamma) 0 = 0)
    (h2 : iteratedDerivWithin 2 ch (Icc 0 gamma) 0 = 0)
    (h3 : iteratedDerivWithin 3 ch (Icc 0 gamma) 0 = 0)
    (hM : ∀ y ∈ Icc 0 gamma, |iteratedDerivWithin 4 ch (Icc 0 gamma) y| ≤ M)
    {g : ℝ} (hg : g ∈ Icc 0 gamma) :
    |ch g| ≤ M / 6 * g ^ 4 := by
  have hcd' : ContDiffOn ℝ ((3 : ℕ) + 1) ch (Icc 0 gamma) := by
    norm_num
    exact hcd
  have hM' : ∀ y ∈ Icc 0 gamma, ‖iteratedDerivWithin ((3 : ℕ) + 1) ch (Icc 0 gamma) y‖ ≤ M := by
    intro y hy
    simpa using hM y hy
  have hmain := taylor_mean_remainder_bound (f := ch) (a := 0) (b := gamma) (x := g)
    (n := 3) hgam hcd' hg hM'
  have hpoly : taylorWithinEval ch 3 (Icc 0 gamma) 0 g = 0 := by
    simp [taylorWithinEval_succ, h0, h1, h2, h3]
  rw [hpoly, sub_zero] at hmain
  have hfac : M * (g - 0) ^ (3 + 1) / (Nat.factorial 3) = M / 6 * g ^ 4 := by
    norm_num [Nat.factorial]
    ring
  rw [hfac] at hmain
  simpa using hmain

/-- **The five channel majorants from five fourth-derivative bounds.** -/
theorem channelMajorants_of_fourthDeriv {ch : BetaChannel → ℝ → ℝ} {M : BetaChannel → ℝ}
    {gamma : ℝ} (hgam : 0 ≤ gamma)
    (hcd : ∀ k, ContDiffOn ℝ 4 (ch k) (Icc 0 gamma))
    (h0 : ∀ k, ch k 0 = 0)
    (h1 : ∀ k, iteratedDerivWithin 1 (ch k) (Icc 0 gamma) 0 = 0)
    (h2 : ∀ k, iteratedDerivWithin 2 (ch k) (Icc 0 gamma) 0 = 0)
    (h3 : ∀ k, iteratedDerivWithin 3 (ch k) (Icc 0 gamma) 0 = 0)
    (hM : ∀ k, ∀ y ∈ Icc 0 gamma, |iteratedDerivWithin 4 (ch k) (Icc 0 gamma) y| ≤ M k)
    {g : ℝ} (hg : g ∈ Icc 0 gamma) (k : BetaChannel) :
    |ch k g| ≤ (M k / 6) * g ^ 4 :=
  abs_le_quartic_of_fourthDeriv_bound hgam (hcd k) (h0 k) (h1 k) (h2 k) (h3 k) (hM k) hg

/-- The resulting channel constant: `C_β = (∑_k M_k)/6`. -/
theorem Cbeta_of_fourthDerivBounds (M : BetaChannel → ℝ) :
    Cbeta (fun k => M k / 6) = (∑ k, M k) / 6 := by
  rw [Cbeta, Finset.sum_div]

/-- **The interaction debt from fourth-derivative data.**  Five uniform bounds
on the fourth coupling derivative of the five channels give the literal quartic
remainder bound with `C_β = (∑_k M_k)/6`. -/
theorem betaInt_ge_of_fourthDerivBounds {betaInt : ℝ → ℝ} {ch : BetaChannel → ℝ → ℝ}
    {M : BetaChannel → ℝ} {gamma : ℝ} (hgam : 0 ≤ gamma)
    (hsum : ∀ g, betaInt g = ∑ k, ch k g)
    (hcd : ∀ k, ContDiffOn ℝ 4 (ch k) (Icc 0 gamma))
    (h0 : ∀ k, ch k 0 = 0)
    (h1 : ∀ k, iteratedDerivWithin 1 (ch k) (Icc 0 gamma) 0 = 0)
    (h2 : ∀ k, iteratedDerivWithin 2 (ch k) (Icc 0 gamma) 0 = 0)
    (h3 : ∀ k, iteratedDerivWithin 3 (ch k) (Icc 0 gamma) 0 = 0)
    (hM : ∀ k, ∀ y ∈ Icc 0 gamma, |iteratedDerivWithin 4 (ch k) (Icc 0 gamma) y| ≤ M k)
    {g : ℝ} (hg : g ∈ Icc 0 gamma) :
    -((∑ k, M k) / 6) * g ^ 4 ≤ betaInt g := by
  have hmaj := betaInt_ge_of_channelMajorants (betaInt := betaInt) (ch := ch)
    (c := fun k => M k / 6) (g := g) (hsum g)
    (fun k => channelMajorants_of_fourthDeriv hgam hcd h0 h1 h2 h3 hM hg k)
  rwa [Cbeta_of_fourthDerivBounds] at hmaj

end YangMills
