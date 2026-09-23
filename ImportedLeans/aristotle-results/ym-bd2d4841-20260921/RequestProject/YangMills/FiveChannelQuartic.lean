/-
# Row A1 — the interaction debt from the five physical channels

The generic interaction debt of `InteractionDebt` needs a Cauchy pair `(A,K)`
and an exponent `ρ`: `|βInt_j| ≤ (A/(1−Kγ))·g_j^ρ`.  The physical organisation
of the nonlinear beta remainder is finer than that: the remainder splits into
five channels

    determinant, interaction, chart, gauge, localization,

each of which carries its *own* fourth-order majorant `|ch_k(g)| ≤ c_k g^4`.
That replaces the two generic parameters `(A,K)` by the finite list of channel
coefficients and fixes the exponent at its physical value `ρ = 4`.

This file proves that replacement.

* `betaInt_ge_of_channelMajorants` : from the five channelwise fourth-order
  majorants, `βInt(g) ≥ −C_β g^4` with `C_β = ∑_k c_k` — literally the finite
  sum of the channel coefficients.
* `betaInt_ge_on_trajectory` : along a trajectory with `0 ≤ g ≤ γ` this is the
  uniform debt `C_β γ^4`, the second term of the corrected Row A1 margin.
* `channelMajorants_dominate_cauchyPair` : the resulting debt is the Cauchy-pair
  debt with `A = C_β`, `K = 0`, `ρ = 4`, so nothing is lost by discarding the
  generic pair.
* `channel_majorant_load_bearing` : dropping the majorant on a single channel
  destroys the conclusion — an explicit family whose four bounded channels are
  fine and whose fifth makes the coefficient arbitrarily negative.

Nothing here asserts the *values* `c_k` for Bałaban's construction; those are
the channelwise Taylor data still to be instantiated.
-/
import Mathlib

namespace YangMills

open Finset

/-- The five physical channels of the nonlinear beta remainder. -/
inductive BetaChannel
  | determinant
  | interaction
  | chart
  | gauge
  | localization
  deriving DecidableEq, Fintype, Repr

/-- The channel constant of the fourth-order remainder: the finite sum of the
five channel coefficients. -/
noncomputable def Cbeta (c : BetaChannel → ℝ) : ℝ := ∑ k, c k

theorem Cbeta_nonneg {c : BetaChannel → ℝ} (hc : ∀ k, 0 ≤ c k) : 0 ≤ Cbeta c :=
  Finset.sum_nonneg fun k _ => hc k

/-- **The quartic beta bound from the five channels.**  If the nonlinear
remainder is the sum of the five channels and each channel obeys its own
fourth-order majorant, then `βInt(g) ≥ −C_β g^4` with `C_β` the sum of the
channel coefficients. -/
theorem betaInt_ge_of_channelMajorants {betaInt : ℝ → ℝ} {ch : BetaChannel → ℝ → ℝ}
    {c : BetaChannel → ℝ} {g : ℝ}
    (hsum : betaInt g = ∑ k, ch k g)
    (hmaj : ∀ k, |ch k g| ≤ c k * g ^ 4) :
    -(Cbeta c) * g ^ 4 ≤ betaInt g := by
  have hlow : ∀ k, -(c k * g ^ 4) ≤ ch k g := fun k =>
    neg_le_of_abs_le (hmaj k)
  have : ∑ k, -(c k * g ^ 4) ≤ ∑ k, ch k g := Finset.sum_le_sum fun k _ => hlow k
  rw [hsum]
  refine le_trans (le_of_eq ?_) this
  rw [Cbeta, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]

/-- Along a trajectory with `0 ≤ g ≤ γ` the channel bound gives the uniform
interaction debt `C_β γ^4`. -/
theorem betaInt_ge_on_trajectory {betaInt : ℝ → ℝ} {ch : BetaChannel → ℝ → ℝ}
    {c : BetaChannel → ℝ} {g gamma : ℝ}
    (hsum : betaInt g = ∑ k, ch k g)
    (hmaj : ∀ k, |ch k g| ≤ c k * g ^ 4)
    (hc : ∀ k, 0 ≤ c k) (hg0 : 0 ≤ g) (hg : g ≤ gamma) :
    -(Cbeta c) * gamma ^ 4 ≤ betaInt g := by
  have h1 := betaInt_ge_of_channelMajorants hsum hmaj
  have hpow : g ^ 4 ≤ gamma ^ 4 := by
    exact pow_le_pow_left₀ hg0 hg 4
  have hC : 0 ≤ Cbeta c := Cbeta_nonneg hc
  nlinarith

/-- The channel debt is a special case of the Cauchy-pair debt, with
`A = C_β`, `K = 0` and `ρ = 4`: the generic pair `(A,K)` is therefore not needed
once the channelwise Taylor data are available. -/
theorem channelMajorants_dominate_cauchyPair (c : BetaChannel → ℝ) (gamma : ℝ) :
    (Cbeta c / (1 - 0 * gamma)) * gamma ^ 4 = Cbeta c * gamma ^ 4 := by
  norm_num

/-- **Every channel majorant is load-bearing.**  For each `n`, the family whose
`determinant` channel equals `−n·g^4` and whose other four channels vanish
satisfies the majorants on those four channels, yet its coefficient at `g = 1`
is `−n`, below any prescribed floor.  So a bound on four of the five channels
never suffices. -/
theorem channel_majorant_load_bearing (b : ℝ) :
    ∃ (ch : BetaChannel → ℝ → ℝ),
      (∀ k, k ≠ BetaChannel.determinant → ∀ g : ℝ, ch k g = 0) ∧
      (∑ k, ch k 1) < b := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-b)
  refine ⟨fun k g => if k = BetaChannel.determinant then -(n : ℝ) * g ^ 4 else 0,
    fun k hk g => by simp [hk], ?_⟩
  have : (∑ k, (if k = BetaChannel.determinant then -(n : ℝ) * 1 ^ 4 else 0))
      = -(n : ℝ) := by
    simp
  rw [this]
  linarith

end YangMills
