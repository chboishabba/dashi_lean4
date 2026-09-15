/-
# A1: `CommutatorOnlySpacetimeBudget568` over `ℝ`, and its reduction

## The payment

Agda `NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact`:

```agda
record CommutatorOnlySpacetimeBudget568 (T) (R) : Set₁ where
  field
    cutoffIndependentCommutatorBound568 : Time → ℚ
    liveCommutatorOnlyBudget568 :
      (cutoff : Nat) (terminal : Time) →
      R567.four567 * integratedGlobalForcingFull T R cutoff terminal
      ≤ cutoffIndependentCommutatorBound568 terminal
```

`CommutatorOnlySpacetimeBudget568` below is the same record over `ℝ`: the bound
is a function of the terminal time only, so the cutoff-independence is enforced
by the *type*, exactly as in the Agda original.

## What this file proves

* `budget568_of_uniform_absorption` — **the A1 reduction.**  A family of
  Galerkin energy balances, indexed by the cutoff, whose commutator-only
  forcing obeys a pointwise absorption receipt with constants `ν, ε, K, E₀`
  *independent of the cutoff*, produces the R568 record with the explicit bound
  `commutatorBudget ν ε K E₀ T`.

* `pointwise_absorption_of_channel_squares` — **the Schur/Young step, applied
  only after the exact signed collapse.**  Given the collapsed channel norms
  `A c = ‖∑_α r_c α • forcing α‖`, `B c = ‖∑_β r_c β • cell β‖` supplied by
  `fullSquareSum_gram_collapse` / `abs_fullSquareSum_gram_collapse_le`, together
  with the two *square* receipts

  ```
  ∑_c (A c)² ≤ c_A · Dissipation ,   ∑_c (B c)² ≤ c_B · Energy ,
  ```

  the absorption receipt holds with `ε = 2θ c_A` and `K = 2 c_B / θ` for every
  `θ > 0`.  Sub-criticality `ε < 2ν` is therefore available as soon as
  `c_A < ∞` uniformly: take `θ < ν / c_A`.  This is the precise statement of
  what the R574 cell control has to deliver.

* `budget568_of_channel_control` — the two combined: the R568 record from
  channel-square receipts alone.

## Consumer

`DASHI.NS.Unforced.DualConsumer414` (the R414 signed-cancellation dual
consumer) reads `CommutatorOnlySpacetimeBudget568` as its *remainder* half.  It
does **not** read the critical half from here; see `A2CriticalCeiling.lean`.

## Status

A1 reduction.  The remaining unproved obligation is exactly the pair of square
receipts `∑ A² ≤ c_A · D`, `∑ B² ≤ c_B · E` with `c_A` small enough — an
honest PDE estimate, not supplied here.
-/
import NSUnforced.SignedFullSquare
import NSUnforced.CutoffUniformBudget

open MeasureTheory

noncomputable section

namespace DASHI.NS.Unforced

/-- **A1, the R568 payment.**  The bound is a function of the terminal time
only; no cutoff may appear in it. -/
structure CommutatorOnlySpacetimeBudget568 (globalForcingFull : ℕ → ℝ → ℝ) where
  /-- `cutoffIndependentCommutatorBound568`. -/
  bound : ℝ → ℝ
  /-- `liveCommutatorOnlyBudget568`, with `R567.four567 = 4`. -/
  budget : ∀ (N : ℕ) (T : ℝ), 0 ≤ T →
    4 * (∫ t in (0 : ℝ)..T, globalForcingFull N t) ≤ bound T

/-- **The A1 reduction.**  A cutoff-indexed family of energy balances whose
factor-four commutator-only square is absorbed, with constants uniform in the
cutoff, pays `CommutatorOnlySpacetimeBudget568`. -/
def budget568_of_uniform_absorption
    (globalForcingFull Energy Dissip : ℕ → ℝ → ℝ)
    {nu eps K E0 : ℝ}
    (hnu : 0 < nu) (heps0 : 0 ≤ eps) (hepsnu : eps < 2 * nu) (hK : 0 ≤ K)
    (hDc : ∀ N, Continuous (Dissip N)) (hGc : ∀ N, Continuous (globalForcingFull N))
    (hEnn : ∀ N t, 0 ≤ Energy N t) (hDnn : ∀ N t, 0 ≤ Dissip N t)
    (hbal : ∀ N t, HasDerivAt (Energy N)
      (-(2 * nu) * Dissip N t + 4 * globalForcingFull N t) t)
    (habs : ∀ N t, 4 * globalForcingFull N t ≤ eps * Dissip N t + K * Energy N t)
    (hE0 : ∀ N, Energy N 0 ≤ E0) :
    CommutatorOnlySpacetimeBudget568 globalForcingFull where
  bound := fun T => commutatorBudget nu eps K E0 T
  budget := fun N _T hT =>
    four_integral_forcing_le hnu heps0 hepsnu hK hT (hDc N) (hGc N)
      (hEnn N) (hDnn N) (hbal N) (habs N) (hE0 N)

/-- **Young/Schur majorisation on the collapsed channels.**

`A c` and `B c` are the norms of the assembled forcing and cell vectors of the
`c`-th Gram channel, i.e. the quantities produced by
`abs_fullSquareSum_gram_collapse_le` *after* all signed cancellation has been
carried out exactly.  Given square receipts against the dissipation and the
energy, the absorption hypothesis of the budget engine follows with
`ε = 2θ c_A` and `K = 2 c_B / θ`, for any split parameter `θ > 0`. -/
theorem pointwise_absorption_of_channel_squares
    {χ : Type*} (C : Finset χ) (A B : χ → ℝ)
    {G Dis En cA cB theta : ℝ} (hth : 0 < theta)
    (hG : G ≤ ∑ c ∈ C, A c * B c)
    (hAsq : ∑ c ∈ C, (A c) ^ 2 ≤ cA * Dis)
    (hBsq : ∑ c ∈ C, (B c) ^ 2 ≤ cB * En) :
    4 * G ≤ (2 * theta * cA) * Dis + (2 / theta * cB) * En := by
  have hyoung : ∀ c ∈ C, A c * B c ≤ theta / 2 * (A c) ^ 2 + 1 / (2 * theta) * (B c) ^ 2 := by
    intro c _
    have hsq : 0 ≤ (theta * A c - B c) ^ 2 := sq_nonneg _
    have h2 : 0 < 2 * theta := by linarith
    have hrw : 2 * theta * (theta / 2 * (A c) ^ 2 + 1 / (2 * theta) * (B c) ^ 2)
        = theta ^ 2 * (A c) ^ 2 + (B c) ^ 2 := by
      field_simp
    refine le_of_mul_le_mul_left ?_ h2
    rw [hrw]
    nlinarith [hsq]
  have hsum : ∑ c ∈ C, A c * B c
      ≤ theta / 2 * (∑ c ∈ C, (A c) ^ 2) + 1 / (2 * theta) * ∑ c ∈ C, (B c) ^ 2 := by
    calc ∑ c ∈ C, A c * B c
        ≤ ∑ c ∈ C, (theta / 2 * (A c) ^ 2 + 1 / (2 * theta) * (B c) ^ 2) :=
          Finset.sum_le_sum hyoung
      _ = theta / 2 * (∑ c ∈ C, (A c) ^ 2) + 1 / (2 * theta) * ∑ c ∈ C, (B c) ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hA : theta / 2 * (∑ c ∈ C, (A c) ^ 2) ≤ theta / 2 * (cA * Dis) :=
    mul_le_mul_of_nonneg_left hAsq (by positivity)
  have hB : 1 / (2 * theta) * (∑ c ∈ C, (B c) ^ 2) ≤ 1 / (2 * theta) * (cB * En) :=
    mul_le_mul_of_nonneg_left hBsq (by positivity)
  have hfin : G ≤ theta / 2 * (cA * Dis) + 1 / (2 * theta) * (cB * En) := by linarith
  have e1 : (2 * theta * cA) * Dis = 4 * (theta / 2 * (cA * Dis)) := by ring
  have e2 : (2 / theta * cB) * En = 4 * (1 / (2 * theta) * (cB * En)) := by
    field_simp
    ring
  rw [e1, e2]
  linarith

/-- **A1 from channel control.**  The R568 record, assembled from the exact
signed Gram collapse plus the two square receipts, with an explicitly
sub-critical split parameter. -/
def budget568_of_channel_control
    {χ : Type*} (C : ℕ → ℝ → Finset χ) (A B : ℕ → ℝ → χ → ℝ)
    (globalForcingFull Energy Dissip : ℕ → ℝ → ℝ)
    {nu cA cB theta E0 : ℝ}
    (hnu : 0 < nu) (hth : 0 < theta) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB)
    (hsub : 2 * theta * cA < 2 * nu)
    (hDc : ∀ N, Continuous (Dissip N)) (hGc : ∀ N, Continuous (globalForcingFull N))
    (hEnn : ∀ N t, 0 ≤ Energy N t) (hDnn : ∀ N t, 0 ≤ Dissip N t)
    (hbal : ∀ N t, HasDerivAt (Energy N)
      (-(2 * nu) * Dissip N t + 4 * globalForcingFull N t) t)
    (hG : ∀ N t, globalForcingFull N t ≤ ∑ c ∈ C N t, A N t c * B N t c)
    (hAsq : ∀ N t, ∑ c ∈ C N t, (A N t c) ^ 2 ≤ cA * Dissip N t)
    (hBsq : ∀ N t, ∑ c ∈ C N t, (B N t c) ^ 2 ≤ cB * Energy N t)
    (hE0 : ∀ N, Energy N 0 ≤ E0) :
    CommutatorOnlySpacetimeBudget568 globalForcingFull :=
  budget568_of_uniform_absorption globalForcingFull Energy Dissip hnu
    (by positivity) hsub (by positivity) hDc hGc hEnn hDnn hbal
    (fun N t => pointwise_absorption_of_channel_squares (C N t) (A N t) (B N t)
      hth (hG N t) (hAsq N t) (hBsq N t))
    hE0

end DASHI.NS.Unforced
