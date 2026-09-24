/-
**The anchored shift ledger: what the determinant costs once the wedge factor is
kept.**

`AnchoredRowVariance.lean` proved the two structural facts that the
norm-and-count budget discards:

    `∑_{j≠0} (G₀₀G_jj − G_{0j}²) = G₀₀ tr G − ‖G_{0,*}‖²`   (row variance), and
    `G₀₀G_jj − G_{0j}² = ‖v₀‖²‖v_j − v₀‖² − ⟪v₀, v_j − v₀⟫²`  (shift form),

so for a translate family the anchored determinant sees only the *displacement*
`v_j − v₀`, never the full vector `v_j`.  This file turns that into a ledger:
it computes the exact scale of the resulting budget at the source parameters and
isolates the single exponent on which the whole route now turns.

The source parameters are: grid spacing `h = 2π/L`, window count `q ≤ A₀ H L`
(the local zero count of a window of height `H`), anchor energy
`‖v₀‖² ≤ Cv L²`, and a *shift-Lipschitz constant* `M ≤ Mc·L^k` for the translate
family — the one quantity the source machinery has not yet pinned down.  Then
(`anchoredMinorSum_source_shift_budget`)

    `∑_{j≠0} Δ_{0j} ≤ 4π² Cv Mc² A₀³ · L^{2k+3} · H³`,

against the coercive floor of order `L⁶`.  The ledger therefore reads

    `2k + 3·(window exponent) < 3`  ⟺  strict gain,

and the two decisive corollaries are:

* `anchored_shift_no_gain_of_large_lipschitz` — if `k ≥ 2`, i.e. the translate
  family moves at least as fast as `L²`, the budget is at least `C L⁶` for every
  window with `H ≥ 1` and `L ≥ 1`: the route is closed, and no window shortening
  rescues it.
* `anchored_shift_gain_of_short_window` — if `k ≤ 1` and the window satisfies
  `H³ ≤ δ L`, the budget is at most `C δ L⁶`: the anchored determinant *does*
  beat the floor, for windows up to `H ≍ L^{1/3}`.

So, in contrast with the norm-and-count model of `ShortWindowPrimeTarget.lean`
— which needed the unavailable exponent `θ > 2` — the anchored determinant has a
live regime.  What it needs is not a short-interval mean-value theorem but a
*shift-Lipschitz bound* for the translated prime-side family, with exponent
`k ≤ 1`.  That is the obligation this ledger isolates; nothing here assumes it.
-/
import RiemannAnalytic.AnchoredRowVariance
import RiemannAnalytic.ShortWindowPrimeTarget

namespace RiemannAnalytic

open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The source-scaled shift budget -/

/-- The shift budget at the source parameters: anchor energy `Cv L²`, shift
constant `Mc L^k`, spacing `2π/L`, window count `A₀ H L`. -/
noncomputable def shiftBudgetScale (Cv Mc A0 : ℝ) (k : ℕ) (L H : ℝ) : ℝ :=
  4 * Real.pi ^ 2 * Cv * Mc ^ 2 * A0 ^ 3 * L ^ (2 * k + 3) * H ^ 3

/-- **The source-scaled anchored budget.**  Feeding the source parameters into
the grid shift budget of `AnchoredRowVariance.lean` gives exactly
`4π² Cv Mc² A₀³ L^{2k+3} H³`. -/
theorem anchoredMinorSum_source_shift_budget {q : ℕ} (v : Fin q → E) (i₀ : Fin q)
    {Cv Mc A0 L H : ℝ} {k : ℕ} (hL : 0 < L) (hMc : 0 ≤ Mc)
    (hv : ‖v i₀‖ ^ 2 ≤ Cv * L ^ 2)
    (hshift : ∀ j : Fin q, ‖v j - v i₀‖ ≤ Mc * L ^ k * |2 * Real.pi / L * ((j : ℕ) : ℝ)|)
    (hq : (q : ℝ) ≤ A0 * H * L) :
    anchorMinorSum v i₀ ≤ shiftBudgetScale Cv Mc A0 k L H := by
  have hbase := anchorMinorSum_grid_shift_budget v i₀ hshift
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have hcube : (q : ℝ) ^ 3 ≤ (A0 * H * L) ^ 3 := pow_le_pow_left₀ hq0 hq 3
  have hMk : 0 ≤ Mc * L ^ k := by positivity
  have hsp : (2 * Real.pi / L) ^ 2 * (q : ℝ) ^ 3
      ≤ (2 * Real.pi / L) ^ 2 * (A0 * H * L) ^ 3 :=
    mul_le_mul_of_nonneg_left hcube (by positivity)
  have hstep : ‖v i₀‖ ^ 2 * ((Mc * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (q : ℝ) ^ 3))
      ≤ (Cv * L ^ 2) * ((Mc * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (A0 * H * L) ^ 3)) := by
    have hinner : (Mc * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (q : ℝ) ^ 3)
        ≤ (Mc * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (A0 * H * L) ^ 3) :=
      mul_le_mul_of_nonneg_left hsp (by positivity)
    have hnn : (0 : ℝ) ≤ (Mc * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (q : ℝ) ^ 3) := by
      positivity
    have hv0 : (0 : ℝ) ≤ ‖v i₀‖ ^ 2 := by positivity
    calc ‖v i₀‖ ^ 2 * ((Mc * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (q : ℝ) ^ 3))
        ≤ (Cv * L ^ 2) * ((Mc * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (q : ℝ) ^ 3)) :=
          mul_le_mul_of_nonneg_right hv hnn
      _ ≤ (Cv * L ^ 2) * ((Mc * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (A0 * H * L) ^ 3)) := by
          refine mul_le_mul_of_nonneg_left hinner ?_
          nlinarith [hv0, hv]
  have hfinal : (Cv * L ^ 2) * ((Mc * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (A0 * H * L) ^ 3))
      = shiftBudgetScale Cv Mc A0 k L H := by
    unfold shiftBudgetScale
    have hLne : L ≠ 0 := ne_of_gt hL
    field_simp
    ring
  calc anchorMinorSum v i₀
      ≤ ‖v i₀‖ ^ 2 * ((Mc * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (q : ℝ) ^ 3)) := hbase
    _ ≤ (Cv * L ^ 2) * ((Mc * L ^ k) ^ 2 * ((2 * Real.pi / L) ^ 2 * (A0 * H * L) ^ 3)) := hstep
    _ = shiftBudgetScale Cv Mc A0 k L H := hfinal

/-! ### Reading the ledger -/

/-- **The route is closed for a fast translate family.**  If the shift-Lipschitz
exponent is `k ≥ 2`, then for every window height `H ≥ 1` and every `L ≥ 1` the
budget is at least the critical scale times the ledger constant: no window
shortening can produce `o(L⁶)`. -/
theorem anchored_shift_no_gain_of_large_lipschitz {Cv Mc A0 L H : ℝ} {k : ℕ}
    (hk : 2 ≤ k) (hCv : 0 < Cv) (hMc : 0 < Mc) (hA0 : 0 < A0) (hL : 1 ≤ L) (hH : 1 ≤ H) :
    4 * Real.pi ^ 2 * Cv * Mc ^ 2 * A0 ^ 3 * L ^ 6 ≤ shiftBudgetScale Cv Mc A0 k L H := by
  unfold shiftBudgetScale
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hC : (0 : ℝ) < 4 * Real.pi ^ 2 * Cv * Mc ^ 2 * A0 ^ 3 := by
    have := Real.pi_pos; positivity
  have hpow : L ^ 6 ≤ L ^ (2 * k + 3) := pow_le_pow_right₀ hL (by omega)
  have hH3 : (1 : ℝ) ≤ H ^ 3 := one_le_pow₀ hH
  have h1 : 4 * Real.pi ^ 2 * Cv * Mc ^ 2 * A0 ^ 3 * L ^ 6
      ≤ 4 * Real.pi ^ 2 * Cv * Mc ^ 2 * A0 ^ 3 * L ^ (2 * k + 3) :=
    mul_le_mul_of_nonneg_left hpow hC.le
  have h2 : 4 * Real.pi ^ 2 * Cv * Mc ^ 2 * A0 ^ 3 * L ^ (2 * k + 3)
      ≤ 4 * Real.pi ^ 2 * Cv * Mc ^ 2 * A0 ^ 3 * L ^ (2 * k + 3) * H ^ 3 := by
    have hpos : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * Cv * Mc ^ 2 * A0 ^ 3 * L ^ (2 * k + 3) := by
      positivity
    nlinarith
  linarith

/-- **The route is open for a slow translate family and a short window.**  If the
shift-Lipschitz exponent is `k ≤ 1` and the window satisfies `H³ ≤ δ L`, then

    `budget ≤ 4π² Cv Mc² A₀³ · δ · L⁶`,

so windows up to `H ≍ (δL)^{1/3}` give a strict gain over the critical scale.
This is the regime that the norm-and-count model of `ShortWindowPrimeTarget.lean`
could not see: there the analogous demand was the unavailable exponent
`θ > 2`. -/
theorem anchored_shift_gain_of_short_window {Cv Mc A0 L H delta : ℝ} {k : ℕ}
    (hk : k ≤ 1) (hCv : 0 ≤ Cv) (hA0 : 0 ≤ A0) (hL : 1 ≤ L) (hH : 0 ≤ H)
    (hwin : H ^ 3 ≤ delta * L) :
    shiftBudgetScale Cv Mc A0 k L H
      ≤ 4 * Real.pi ^ 2 * Cv * Mc ^ 2 * A0 ^ 3 * delta * L ^ 6 := by
  unfold shiftBudgetScale
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hC : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * Cv * Mc ^ 2 * A0 ^ 3 := by
    have := Real.pi_pos; positivity
  have hpow : L ^ (2 * k + 3) ≤ L ^ 5 := pow_le_pow_right₀ hL (by omega)
  have hH3 : 0 ≤ H ^ 3 := by positivity
  have hstep1 : L ^ (2 * k + 3) * H ^ 3 ≤ L ^ 5 * (delta * L) := by
    have : L ^ (2 * k + 3) * H ^ 3 ≤ L ^ 5 * H ^ 3 :=
      mul_le_mul_of_nonneg_right hpow hH3
    have h2 : L ^ 5 * H ^ 3 ≤ L ^ 5 * (delta * L) :=
      mul_le_mul_of_nonneg_left hwin (by positivity)
    linarith
  have hstep2 : 4 * Real.pi ^ 2 * Cv * Mc ^ 2 * A0 ^ 3 * L ^ (2 * k + 3) * H ^ 3
      ≤ 4 * Real.pi ^ 2 * Cv * Mc ^ 2 * A0 ^ 3 * (L ^ 5 * (delta * L)) := by
    have := mul_le_mul_of_nonneg_left hstep1 hC
    nlinarith [this]
  have hrw : 4 * Real.pi ^ 2 * Cv * Mc ^ 2 * A0 ^ 3 * (L ^ 5 * (delta * L))
      = 4 * Real.pi ^ 2 * Cv * Mc ^ 2 * A0 ^ 3 * delta * L ^ 6 := by ring
  linarith [hrw ▸ hstep2]

/-- **The ledger in asymptotic form.**  Along a family with `L → ∞` and windows
obeying `H³ ≤ δ L` with `δ → 0`, the source-scaled anchored budget is `o(L⁶)`
for any shift exponent `k ≤ 1`. -/
theorem anchored_shift_budget_ratio_tendsto_zero {ι : Type*} {l : Filter ι}
    {Cv Mc A0 : ℝ} {k : ℕ} (hk : k ≤ 1) (hCv : 0 ≤ Cv) (hA0 : 0 ≤ A0)
    {L H delta : ι → ℝ} (hL : ∀ i, 1 ≤ L i) (hH : ∀ i, 0 ≤ H i)
    (hwin : ∀ i, H i ^ 3 ≤ delta i * L i)
    (hdelta : Filter.Tendsto delta l (nhds 0)) :
    Filter.Tendsto (fun i => shiftBudgetScale Cv Mc A0 k (L i) (H i) / L i ^ 6) l (nhds 0) := by
  have hC : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * Cv * Mc ^ 2 * A0 ^ 3 := by
    have := Real.pi_pos; positivity
  refine squeeze_zero (fun i => ?_) (fun i => ?_)
    (by simpa using hdelta.const_mul (4 * Real.pi ^ 2 * Cv * Mc ^ 2 * A0 ^ 3))
  · have hL0 : (0 : ℝ) < L i := lt_of_lt_of_le zero_lt_one (hL i)
    have hb : 0 ≤ shiftBudgetScale Cv Mc A0 k (L i) (H i) := by
      unfold shiftBudgetScale
      have := Real.pi_pos
      have := hH i
      positivity
    positivity
  · have hL0 : (0 : ℝ) < L i := lt_of_lt_of_le zero_lt_one (hL i)
    have hbound := anchored_shift_gain_of_short_window (Mc := Mc) hk hCv hA0 (hL i) (hH i)
      (hwin i)
    rw [div_le_iff₀ (by positivity)]
    exact hbound

end RiemannAnalytic
