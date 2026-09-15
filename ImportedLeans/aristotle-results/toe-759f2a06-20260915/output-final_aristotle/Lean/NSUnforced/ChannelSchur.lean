/-
# Schur control of the collapsed Gram channels

`fullSquareSum_gram_collapse` turns the commutator-only full square into the
finite family of assembled vectors

```
A c = ∑_{a ∈ s} r c a • Dvec a ,    B c = ∑_{b ∈ s} r c b • Cvec b .
```

`pointwise_absorption_of_channel_squares` then needs the two *square* receipts
`∑_c ‖A c‖² ≤ c_A · D` and `∑_c ‖B c‖² ≤ c_B · E`.  This file reduces both of
them to a **Schur test on the Gram weight matrix** `r`: if the row sums
`∑_b |r c b|` are bounded by `R_row` and the column sums `∑_c |r c b|` by
`R_col`, then

```
∑_c ‖∑_b r c b • v b‖² ≤ R_row · R_col · ∑_b ‖v b‖² .
```

The constant is therefore purely combinatorial — it does not see the velocity
field at all.  That converts the frontier clauses of `A1ChannelObligation` into
two concrete questions about the R503/R572 spectator-row weights:

* is `R_row · R_col` finite and cutoff-uniform (this pays the energy clause,
  with `c_B = R_row R_col`)?
* is the *forcing* side square `∑_b ‖Dvec b‖²` controlled by the dissipation
  with a small constant (this is where the R571 homochiral gain
  `|λ_q^s − λ_p^s| ≤ ‖k‖` must be spent, and where the heterochiral rows remain
  obstructed)?

## Lineage

R503/R572 (spectator rows and the direct leaf-A compiler, which own the
resolvent weights), R543/R566/R567 (the square carrier), R574 (cell control,
the intended source of the forcing-side constant).

## Status

Infrastructure for A1.  Unconditional; no PDE input.
-/
import NSUnforced.SignedFullSquare

noncomputable section

namespace DASHI.NS.Unforced

open Finset

variable {χ ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **One channel.**  `‖∑_b r b • v b‖² ≤ (∑_b |r b|) · ∑_b |r b| ‖v b‖²`. -/
theorem norm_weighted_sum_sq_le (s : Finset ι) (r : ι → ℝ) (v : ι → E) :
    ‖∑ b ∈ s, r b • v b‖ ^ 2 ≤ (∑ b ∈ s, |r b|) * ∑ b ∈ s, |r b| * ‖v b‖ ^ 2 := by
  have h1 : ‖∑ b ∈ s, r b • v b‖ ≤ ∑ b ∈ s, |r b| * ‖v b‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
  have h2 : ‖∑ b ∈ s, r b • v b‖ ^ 2 ≤ (∑ b ∈ s, |r b| * ‖v b‖) ^ 2 := by
    have hnn : 0 ≤ ‖∑ b ∈ s, r b • v b‖ := norm_nonneg _
    exact pow_le_pow_left₀ hnn h1 2
  have h3 : (∑ b ∈ s, |r b| * ‖v b‖) ^ 2
      ≤ (∑ b ∈ s, |r b|) * ∑ b ∈ s, |r b| * ‖v b‖ ^ 2 := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s
      (fun b _ => abs_nonneg (r b))
      (fun b _ => mul_nonneg (abs_nonneg (r b)) (sq_nonneg _)) ?_
    intro b _
    have : (|r b| * ‖v b‖) ^ 2 = |r b| * (|r b| * ‖v b‖ ^ 2) := by ring
    simpa using this
  linarith

/-- **Schur test on the Gram weights.**  Row and column bounds on the weight
matrix control the total channel square by a purely combinatorial constant. -/
theorem sum_channel_sq_le_schur (C : Finset χ) (s : Finset ι)
    (r : χ → ι → ℝ) (v : ι → E) {Rrow Rcol : ℝ} (hRrow : 0 ≤ Rrow)
    (hrow : ∀ c ∈ C, ∑ b ∈ s, |r c b| ≤ Rrow)
    (hcol : ∀ b ∈ s, ∑ c ∈ C, |r c b| ≤ Rcol) :
    ∑ c ∈ C, ‖∑ b ∈ s, r c b • v b‖ ^ 2 ≤ Rrow * Rcol * ∑ b ∈ s, ‖v b‖ ^ 2 := by
  have step1 : ∀ c ∈ C, ‖∑ b ∈ s, r c b • v b‖ ^ 2
      ≤ Rrow * ∑ b ∈ s, |r c b| * ‖v b‖ ^ 2 := by
    intro c hc
    have hnn : 0 ≤ ∑ b ∈ s, |r c b| * ‖v b‖ ^ 2 :=
      Finset.sum_nonneg fun b _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
    calc ‖∑ b ∈ s, r c b • v b‖ ^ 2
        ≤ (∑ b ∈ s, |r c b|) * ∑ b ∈ s, |r c b| * ‖v b‖ ^ 2 :=
          norm_weighted_sum_sq_le s (r c) v
      _ ≤ Rrow * ∑ b ∈ s, |r c b| * ‖v b‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hrow c hc) hnn
  have step2 : ∑ c ∈ C, ‖∑ b ∈ s, r c b • v b‖ ^ 2
      ≤ Rrow * ∑ b ∈ s, (∑ c ∈ C, |r c b|) * ‖v b‖ ^ 2 := by
    calc ∑ c ∈ C, ‖∑ b ∈ s, r c b • v b‖ ^ 2
        ≤ ∑ c ∈ C, Rrow * ∑ b ∈ s, |r c b| * ‖v b‖ ^ 2 := Finset.sum_le_sum step1
      _ = Rrow * ∑ c ∈ C, ∑ b ∈ s, |r c b| * ‖v b‖ ^ 2 := by rw [Finset.mul_sum]
      _ = Rrow * ∑ b ∈ s, (∑ c ∈ C, |r c b|) * ‖v b‖ ^ 2 := by
          rw [Finset.sum_comm]
          congr 1
          exact Finset.sum_congr rfl fun b _ => by rw [Finset.sum_mul]
  have step3 : ∑ b ∈ s, (∑ c ∈ C, |r c b|) * ‖v b‖ ^ 2 ≤ Rcol * ∑ b ∈ s, ‖v b‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    exact mul_le_mul_of_nonneg_right (hcol b hb) (sq_nonneg _)
  calc ∑ c ∈ C, ‖∑ b ∈ s, r c b • v b‖ ^ 2
      ≤ Rrow * ∑ b ∈ s, (∑ c ∈ C, |r c b|) * ‖v b‖ ^ 2 := step2
    _ ≤ Rrow * (Rcol * ∑ b ∈ s, ‖v b‖ ^ 2) := mul_le_mul_of_nonneg_left step3 hRrow
    _ = Rrow * Rcol * ∑ b ∈ s, ‖v b‖ ^ 2 := by ring

/-- **The energy clause of the frontier, from the Schur test.**  With row/column
control of the Gram weights, the cell-side square receipt holds with
`c_B = R_row R_col`, so the energy clause of `A1ChannelObligation` is reduced to
combinatorics of the resolvent weights plus the Parseval identity
`∑_b ‖cell b‖² ≤ Energy`. -/
theorem channel_energy_receipt (C : Finset χ) (s : Finset ι)
    (r : χ → ι → ℝ) (v : ι → E) {Rrow Rcol En : ℝ} (hRrow : 0 ≤ Rrow)
    (hrow : ∀ c ∈ C, ∑ b ∈ s, |r c b| ≤ Rrow)
    (hcol : ∀ b ∈ s, ∑ c ∈ C, |r c b| ≤ Rcol)
    (hRcol : 0 ≤ Rcol) (hEn : ∑ b ∈ s, ‖v b‖ ^ 2 ≤ En) :
    ∑ c ∈ C, ‖∑ b ∈ s, r c b • v b‖ ^ 2 ≤ (Rrow * Rcol) * En := by
  refine le_trans (sum_channel_sq_le_schur C s r v hRrow hrow hcol) ?_
  exact mul_le_mul_of_nonneg_left hEn (mul_nonneg hRrow hRcol)

end DASHI.NS.Unforced
