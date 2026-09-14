/-
**A finite affine geometry inside the fifteen Ogg (supersingular) primes.**

The fifteen primes dividing the order of the Monster,

    {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71},

contain an exact `2 × 3` affine grid

    {5, 17, 29} + {0, 42} = {5, 17, 29, 47, 59, 71},

i.e. the six points `5 + 12 i + 42 j` for `i < 3`, `j < 2` (`sspGrid_eq_rows`,
`sspGrid_subset_ogg`).  Its horizontal spacing is `12` and its vertical
translation is `42`; the upper row `{47, 59, 71}` is the triple of largest Ogg
primes, whose product is `196883` (`ogg_top_product`).

Everything here is a finite, decidable statement about explicit natural numbers,
checked by the kernel.  Two honest caveats are recorded as theorems rather than
omitted:

* `42` is **not** the only translation carrying `{5, 17, 29}` into the Ogg set:
  the full list of positive translations below `100` is `{2, 12, 42}`
  (`ogg_translations_of_lower_row`), and `42` is the largest
  (`ogg_translation_le_42`);
* the translation `p ↦ p + 42` is **not** the pointed-sign map `p ↦ 2p + 1`
  (`translate42_ne_pointedSign`), which is a genuinely different observer on the
  same set — its own chain `2 → 5 → 11 → 23 → 47` is recorded in
  `pointedSign_chain`.
-/
import Mathlib

namespace RiemannAnalytic

/-! ### The Ogg / supersingular prime set -/

/-- The fifteen supersingular (Ogg) primes: the primes dividing `|𝕄|`. -/
def oggPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71}

theorem oggPrimes_card : oggPrimes.card = 15 := by decide

theorem oggPrimes_prime : ∀ p ∈ oggPrimes, Nat.Prime p := by decide

/-! ### The `2 × 3` affine grid -/

/-- The lower row `{5, 17, 29}` of the grid. -/
def sspLowerRow : Finset ℕ := {5, 17, 29}

/-- The upper row `{47, 59, 71}`: the three largest Ogg primes. -/
def sspUpperRow : Finset ℕ := {47, 59, 71}

/-- The six grid points `5 + 12 i + 42 j`, `i : Fin 3`, `j : Fin 2`. -/
def sspGrid : Finset ℕ :=
  Finset.image (fun ij : Fin 3 × Fin 2 => 5 + 12 * (ij.1 : ℕ) + 42 * (ij.2 : ℕ)) Finset.univ

theorem sspGrid_eq_rows : sspGrid = sspLowerRow ∪ sspUpperRow := by decide

theorem sspGrid_card : sspGrid.card = 6 := by decide

theorem sspGrid_subset_ogg : sspGrid ⊆ oggPrimes := by decide

/-- **The translation by `42` carries the lower row exactly onto the upper row.** -/
theorem ssp_translate_42 : sspLowerRow.image (· + 42) = sspUpperRow := by decide

/-- Equivalently, pointwise: `{5, 17, 29} + 42 = {47, 59, 71}`. -/
theorem ssp_translate_42_pointwise :
    5 + 42 = 47 ∧ 17 + 42 = 59 ∧ 29 + 42 = 71 := by norm_num

/-- Each row is an arithmetic progression of common difference `12`. -/
theorem ssp_row_spacing :
    17 - 5 = 12 ∧ 29 - 17 = 12 ∧ 59 - 47 = 12 ∧ 71 - 59 = 12 := by norm_num

/-- The three largest Ogg primes multiply to the smallest nontrivial Monster
character degree. -/
theorem ogg_top_product : 47 * 59 * 71 = 196883 := by norm_num

/-! ### How special is the translation `42`? -/

/-- The positive translations `d < 100` carrying the whole lower row into the
Ogg set are exactly `2`, `12` and `42`.  (So `42` is distinguished by being the
largest, not by being unique.) -/
theorem ogg_translations_of_lower_row :
    (Finset.range 100).filter
        (fun d => 0 < d ∧ 5 + d ∈ oggPrimes ∧ 17 + d ∈ oggPrimes ∧ 29 + d ∈ oggPrimes)
      = {2, 12, 42} := by decide

theorem ogg_translation_le_42 :
    ∀ d ∈ Finset.range 100, 0 < d → 5 + d ∈ oggPrimes → 17 + d ∈ oggPrimes →
      29 + d ∈ oggPrimes → d ≤ 42 := by decide

/-- The three-term arithmetic progressions of common difference `12` inside the
Ogg set start exactly at `5`, `7`, `17`, `47`. -/
theorem ogg_ap12_starts :
    oggPrimes.filter (fun a => a + 12 ∈ oggPrimes ∧ a + 24 ∈ oggPrimes) = {5, 7, 17, 47} := by
  decide

/-! ### The translation observer is not the pointed-sign observer -/

/-- `p ↦ p + 42` and the pointed-sign map `p ↦ 2p + 1` differ on every point of
the lower row: the affine grid is a different structure from the pointed-sign
genealogy. -/
theorem translate42_ne_pointedSign : ∀ p ∈ sspLowerRow, p + 42 ≠ 2 * p + 1 := by decide

/-- The inverse pointed-sign step at `47` is `23`, not `5`. -/
theorem pointedSign_pred_47 : (47 - 1) / 2 = 23 := by norm_num

/-- The pointed-sign chain `2 → 5 → 11 → 23 → 47` stays inside the Ogg set. -/
theorem pointedSign_chain : ∀ p ∈ ({2, 5, 11, 23} : Finset ℕ), 2 * p + 1 ∈ oggPrimes := by decide

/-- The chain `2 → 5 → 11 → 23 → 47` has five members, all Ogg primes. -/
theorem pointedSign_chain_members : ({2, 5, 11, 23, 47} : Finset ℕ) ⊆ oggPrimes := by decide

end RiemannAnalytic
