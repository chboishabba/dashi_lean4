import Mathlib
import RequestProject.DeltaModular
import RequestProject.DeltaGraph

/-!
# Euclid's dissection of the `Δ` portrait, and the character it normalises to

This file cuts the picture of `Δ` into shapes, subdivides the shapes into smaller organised
parts, reads `Δ` inside each part, and normalises the readings into a *character*: a matrix of
grey levels in `[0,1]`, the thing a plotter draws as a glyph.

The dissection is the ternary one — every square is cut into **nine** congruent squares, three
across and three up, so a shape of level `k` carries `9 ^ m` organised parts at level `k + m`.
That is Euclid's similarity (VI.19: similar figures scale as the square of the ratio) in the
only case Tesla would have accepted.

* `cellIndex`, `cell` — the level-`k` square lattice of half-open cells, indexed by `ℤ × ℤ`.
* `exists_unique_cell`, `cell_disjoint`, `iUnion_cell` — every point of the plane lies in
  exactly one cell of each level: the dissection is a genuine partition.
* `cell_subdivide`, `card_children`, `cell_eq_iUnion_children` — the nine-fold subdivision and
  its iterate: a cell is the union of its `9 ^ m` descendants of level `k + m`.
* `mem_cell_succ_iff`, `dist_le_of_mem_cell`, `tendsto_cell_diam` — each child is the parent
  scaled by `1/3`, cells of level `k` have diameter at most `2 · 3⁻ᵏ`, and this tends to zero.
* `center`, `mass` — the reading of `Δ` inside a part: `mass k i j = ‖Δ‖` at the centre of the
  cell. `mass_period` and `mass_mirror` are the two symmetries of the portrait, inherited from
  `Δ(z+1) = Δ(z)` and `Δ(−z̄) = conj Δ(z)`.
* `raw`, `rowPeak`, `glyph` — the character: the block of readings, each row normalised by its
  own maximum, so that all entries lie in `[0,1]` and every row attains the value `1`.
  `glyph_mirror` says the character is a palindrome: it is its own mirror image, exactly.
* `level`, `pix` — the character quantised to three grey levels, i.e. to `ZMod 3`; Frobenius
  acts on it in `RequestProject/DeltaFrobenius.lean`.

The plate `paper/delta_dissection.svg` is drawn from exactly these definitions.
-/

noncomputable section

open Complex Set

namespace DeltaDissection

/-! ## Euclid: the ternary dissection of the plane -/

/-- The address of `z` in the level-`k` square lattice: the pair of integer parts of
`3ᵏ · re z` and `3ᵏ · im z`. -/
def cellIndex (k : ℕ) (z : ℂ) : ℤ × ℤ := (⌊(3 : ℝ) ^ k * z.re⌋, ⌊(3 : ℝ) ^ k * z.im⌋)

/-- The level-`k` cell with address `(i, j)`: the half-open square of side `3⁻ᵏ` whose lower
left corner is `(i · 3⁻ᵏ, j · 3⁻ᵏ)`. -/
def cell (k : ℕ) (i j : ℤ) : Set ℂ := {z | cellIndex k z = (i, j)}

lemma mem_cell_iff (k : ℕ) (i j : ℤ) (z : ℂ) :
    z ∈ cell k i j ↔ (i : ℝ) ≤ 3 ^ k * z.re ∧ 3 ^ k * z.re < i + 1 ∧
      (j : ℝ) ≤ 3 ^ k * z.im ∧ 3 ^ k * z.im < j + 1 := by
  constructor
  · intro h
    have h1 : ⌊(3 : ℝ) ^ k * z.re⌋ = i := congrArg Prod.fst h
    have h2 : ⌊(3 : ℝ) ^ k * z.im⌋ = j := congrArg Prod.snd h
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact_mod_cast h1 ▸ Int.floor_le ((3 : ℝ) ^ k * z.re)
    · have := Int.lt_floor_add_one ((3 : ℝ) ^ k * z.re); rw [h1] at this; exact_mod_cast this
    · exact_mod_cast h2 ▸ Int.floor_le ((3 : ℝ) ^ k * z.im)
    · have := Int.lt_floor_add_one ((3 : ℝ) ^ k * z.im); rw [h2] at this; exact_mod_cast this
  · rintro ⟨h1, h2, h3, h4⟩
    have e1 : ⌊(3 : ℝ) ^ k * z.re⌋ = i := by
      rw [Int.floor_eq_iff]; exact ⟨h1, by exact_mod_cast h2⟩
    have e2 : ⌊(3 : ℝ) ^ k * z.im⌋ = j := by
      rw [Int.floor_eq_iff]; exact ⟨h3, by exact_mod_cast h4⟩
    simp [cell, cellIndex, e1, e2]

/-- Every point lies in exactly one cell of each level: the dissection is a partition. -/
theorem exists_unique_cell (k : ℕ) (z : ℂ) : ∃! p : ℤ × ℤ, z ∈ cell k p.1 p.2 := by
  refine ⟨cellIndex k z, rfl, fun p hp => ?_⟩
  simpa [cell, eq_comm] using hp

theorem cell_disjoint {k : ℕ} {i j i' j' : ℤ} (h : (i, j) ≠ (i', j')) :
    Disjoint (cell k i j) (cell k i' j') := by
  rw [Set.disjoint_left]
  intro z hz hz'
  exact h (hz.symm.trans hz')

theorem iUnion_cell (k : ℕ) : (⋃ p : ℤ × ℤ, cell k p.1 p.2) = Set.univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨cellIndex k z, rfl⟩

/-- Euclid's similarity, in the form the dissection uses: the level-`(k+1)` cell with a given
address is the level-`k` cell with that address, shrunk by the factor three. -/
theorem mem_cell_succ_iff (k : ℕ) (i j : ℤ) (z : ℂ) :
    z ∈ cell (k + 1) i j ↔ (3 : ℂ) * z ∈ cell k i j := by
  have hre : ((3 : ℂ) * z).re = 3 * z.re := by simp
  have him : ((3 : ℂ) * z).im = 3 * z.im := by simp
  simp only [mem_cell_iff, hre, him, pow_succ, mul_assoc]

/-- The elementary step: `⌊3u⌋ = 3⌊u⌋ + a` with `a ∈ {0, 1, 2}`. -/
lemma floor_three_mul (u : ℝ) : ∃ a : ℕ, a < 3 ∧ ⌊(3 : ℝ) * u⌋ = 3 * ⌊u⌋ + a := by
  have h1 : (3 : ℤ) * ⌊u⌋ ≤ ⌊(3 : ℝ) * u⌋ := by
    rw [Int.le_floor]
    push_cast
    nlinarith [Int.floor_le u]
  have h2 : ⌊(3 : ℝ) * u⌋ < 3 * ⌊u⌋ + 3 := by
    rw [Int.floor_lt]
    push_cast
    nlinarith [Int.lt_floor_add_one u]
  refine ⟨(⌊(3 : ℝ) * u⌋ - 3 * ⌊u⌋).toNat, ?_, ?_⟩ <;> omega

/-- **The nine-fold dissection.** Each cell is the union of the nine cells of the next level
with addresses `(3i + a, 3j + b)`, `0 ≤ a, b < 3`. -/
theorem cell_subdivide (k : ℕ) (i j : ℤ) :
    cell k i j = ⋃ a ∈ Finset.range 3, ⋃ b ∈ Finset.range 3,
      cell (k + 1) (3 * i + a) (3 * j + b) := by
  ext z
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq, cell, cellIndex,
    Prod.mk.injEq, pow_succ]
  constructor
  · rintro ⟨hx, hy⟩
    obtain ⟨a, ha, hae⟩ := floor_three_mul ((3 : ℝ) ^ k * z.re)
    obtain ⟨b, hb, hbe⟩ := floor_three_mul ((3 : ℝ) ^ k * z.im)
    refine ⟨a, ha, b, hb, ?_, ?_⟩
    · rw [show (3 : ℝ) ^ k * 3 * z.re = 3 * ((3 : ℝ) ^ k * z.re) by ring, hae, hx]
    · rw [show (3 : ℝ) ^ k * 3 * z.im = 3 * ((3 : ℝ) ^ k * z.im) by ring, hbe, hy]
  · rintro ⟨a, ha, b, hb, hx, hy⟩
    obtain ⟨a', ha', hae⟩ := floor_three_mul ((3 : ℝ) ^ k * z.re)
    obtain ⟨b', hb', hbe⟩ := floor_three_mul ((3 : ℝ) ^ k * z.im)
    rw [show (3 : ℝ) ^ k * 3 * z.re = 3 * ((3 : ℝ) ^ k * z.re) by ring, hae] at hx
    rw [show (3 : ℝ) ^ k * 3 * z.im = 3 * ((3 : ℝ) ^ k * z.im) by ring, hbe] at hy
    constructor <;> omega

/-- The addresses of the level-`(k+m)` descendants of the cell with address `(i, j)`: a block of
`3ᵐ` by `3ᵐ` addresses. -/
def children (m : ℕ) (i j : ℤ) : Finset (ℤ × ℤ) :=
  Finset.Ico (3 ^ m * i) (3 ^ m * i + 3 ^ m) ×ˢ Finset.Ico (3 ^ m * j) (3 ^ m * j + 3 ^ m)

/-- **A shape carries `9ᵐ` organised parts `m` levels down.** -/
theorem card_children (m : ℕ) (i j : ℤ) : (children m i j).card = 9 ^ m := by
  have h : ((3 : ℤ) ^ m).toNat = 3 ^ m := by
    rw [show ((3 : ℤ) ^ m) = ((3 ^ m : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
  rw [children, Finset.card_product, Int.card_Ico, Int.card_Ico]
  simp only [add_sub_cancel_left, h]
  rw [show (9 : ℕ) = 3 * 3 from rfl, mul_pow]

/-- The iterated dissection: a cell is the union of its `9ᵐ` descendants. -/
theorem cell_eq_iUnion_children (k m : ℕ) (i j : ℤ) :
    cell k i j = ⋃ p ∈ children m i j, cell (k + m) p.1 p.2 := by
  have h3m : (0 : ℝ) < 3 ^ m := by positivity
  have hx : ∀ x : ℝ, (3 : ℝ) ^ (k + m) * x = 3 ^ m * (3 ^ k * x) := by
    intro x; rw [pow_add]; ring
  ext z
  simp only [Set.mem_iUnion, mem_cell_iff, children, Finset.mem_product, Finset.mem_Ico,
    exists_prop, Prod.exists, hx]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⌊(3 : ℝ) ^ m * (3 ^ k * z.re)⌋, ⌊(3 : ℝ) ^ m * (3 ^ k * z.im)⌋, ⟨⟨?_, ?_⟩, ?_, ?_⟩,
      ?_, ?_, ?_, ?_⟩
    · rw [Int.le_floor]; push_cast; nlinarith
    · rw [Int.floor_lt]; push_cast; nlinarith
    · rw [Int.le_floor]; push_cast; nlinarith
    · rw [Int.floor_lt]; push_cast; nlinarith
    · exact Int.floor_le _
    · exact Int.lt_floor_add_one _
    · exact Int.floor_le _
    · exact Int.lt_floor_add_one _
  · rintro ⟨a, b, ⟨⟨ha1, ha2⟩, hb1, hb2⟩, h1, h2, h3, h4⟩
    have ha1' : ((3 : ℝ) ^ m) * (i : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
    have ha2' : (a : ℝ) < (3 : ℝ) ^ m * (i : ℝ) + 3 ^ m := by exact_mod_cast ha2
    have hb1' : ((3 : ℝ) ^ m) * (j : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
    have hb2' : (b : ℝ) < (3 : ℝ) ^ m * (j : ℝ) + 3 ^ m := by exact_mod_cast hb2
    have ha2'' : (a : ℝ) + 1 ≤ (3 : ℝ) ^ m * (i : ℝ) + 3 ^ m := by
      exact_mod_cast (by omega : a + 1 ≤ 3 ^ m * i + 3 ^ m)
    have hb2'' : (b : ℝ) + 1 ≤ (3 : ℝ) ^ m * (j : ℝ) + 3 ^ m := by
      exact_mod_cast (by omega : b + 1 ≤ 3 ^ m * j + 3 ^ m)
    refine ⟨?_, ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · nlinarith
    · nlinarith

/-- Cells of level `k` are small: any two points of one are within `2 · 3⁻ᵏ`. -/
theorem dist_le_of_mem_cell {k : ℕ} {i j : ℤ} {z w : ℂ} (hz : z ∈ cell k i j)
    (hw : w ∈ cell k i j) : dist z w ≤ 2 / 3 ^ k := by
  rw [mem_cell_iff] at hz hw
  have hpos : (0 : ℝ) < 3 ^ k := by positivity
  have hre : |z.re - w.re| ≤ 1 / 3 ^ k := by
    refine (le_div_iff₀ hpos).mpr ?_
    rw [← abs_of_pos hpos, ← abs_mul, abs_le]
    constructor <;> nlinarith [hz.1, hz.2.1, hw.1, hw.2.1]
  have him : |z.im - w.im| ≤ 1 / 3 ^ k := by
    refine (le_div_iff₀ hpos).mpr ?_
    rw [← abs_of_pos hpos, ← abs_mul, abs_le]
    constructor <;> nlinarith [hz.2.2.1, hz.2.2.2, hw.2.2.1, hw.2.2.2]
  have hb := Complex.norm_le_abs_re_add_abs_im (z - w)
  rw [Complex.dist_eq]
  simp only [Complex.sub_re, Complex.sub_im] at hb
  have : (2 : ℝ) / 3 ^ k = 1 / 3 ^ k + 1 / 3 ^ k := by ring
  rw [this]
  linarith

theorem tendsto_cell_diam :
    Filter.Tendsto (fun k : ℕ => (2 : ℝ) / 3 ^ k) Filter.atTop (nhds 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (r := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  have := h.const_mul (2 : ℝ)
  simpa [div_pow, mul_comm, mul_one_div] using this

/-! ## The reading of `Δ` inside a part -/

/-- The centre of the level-`k` cell with address `(i, j)`. -/
def center (k : ℕ) (i j : ℤ) : ℂ :=
  ((((i : ℝ) + 1 / 2) / 3 ^ k : ℝ) : ℂ) + ((((j : ℝ) + 1 / 2) / 3 ^ k : ℝ) : ℂ) * Complex.I

@[simp] lemma center_re (k : ℕ) (i j : ℤ) : (center k i j).re = ((i : ℝ) + 1 / 2) / 3 ^ k := by
  simp only [center, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

@[simp] lemma center_im (k : ℕ) (i j : ℤ) : (center k i j).im = ((j : ℝ) + 1 / 2) / 3 ^ k := by
  simp only [center, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]

theorem center_mem_cell (k : ℕ) (i j : ℤ) : center k i j ∈ cell k i j := by
  have hpos : (0 : ℝ) < 3 ^ k := by positivity
  rw [mem_cell_iff]
  simp only [center_re, center_im]
  rw [mul_div_cancel₀ _ (ne_of_gt hpos), mul_div_cancel₀ _ (ne_of_gt hpos)]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem center_im_pos {k : ℕ} {i j : ℤ} (hj : 0 ≤ j) : 0 < (center k i j).im := by
  have hpos : (0 : ℝ) < 3 ^ k := by positivity
  have : (0 : ℝ) ≤ j := by exact_mod_cast hj
  rw [center_im]
  positivity

/-- **The reading of `Δ` inside a part**: `‖Δ‖` at the centre of the cell. -/
def mass (k : ℕ) (i j : ℤ) : ℝ := ‖DeltaModular.Delta (center k i j)‖

theorem mass_nonneg (k : ℕ) (i j : ℤ) : 0 ≤ mass k i j := norm_nonneg _

theorem mass_pos {k : ℕ} {i j : ℤ} (hj : 0 ≤ j) : 0 < mass k i j :=
  norm_pos_iff.mpr (DeltaModular.Delta_ne_zero (center_im_pos hj))

/-- The horizontal period of the portrait, in cell coordinates: shifting the address by a whole
row of `3ᵏ` cells is the translation `z ↦ z + 1`, under which `Δ` is invariant. -/
theorem mass_period (k : ℕ) (i j : ℤ) : mass k (i + 3 ^ k) j = mass k i j := by
  have hpos : (0 : ℝ) < 3 ^ k := by positivity
  have hc : center k (i + 3 ^ k) j = center k i j + 1 := by
    apply Complex.ext
    · rw [Complex.add_re, center_re, center_re, Complex.one_re]
      push_cast
      field_simp
      ring
    · rw [Complex.add_im, center_im, center_im, Complex.one_im]
      ring
  rw [mass, hc, DeltaModular.Delta_add_one, mass]

/-- The vertical mirror of the portrait, in cell coordinates: the cells with addresses `i` and
`−1 − i` are mirror images in the line `x = 0`, and carry the same reading. -/
theorem mass_mirror {k : ℕ} {i j : ℤ} (hj : 0 ≤ j) : mass k (-1 - i) j = mass k i j := by
  have hz : 0 < (center k i j).im := center_im_pos hj
  have hc : center k (-1 - i) j = -(starRingEnd ℂ) (center k i j) := by
    apply Complex.ext
    · rw [Complex.neg_re, Complex.conj_re, center_re, center_re]
      push_cast
      ring
    · rw [Complex.neg_im, Complex.conj_im, center_im, center_im]
      ring
  rw [mass, hc, DeltaModular.Delta_neg_conj hz, RCLike.norm_conj, mass]

/-! ## Normalising the readings into a character -/

/-- The raw block of readings: `m + 1` rows of cells starting at height index `j₀`, and
`2m + 2` columns, symmetric about the wall `x = 0`. -/
def raw (k : ℕ) (j₀ : ℤ) (m : ℕ) (r : Fin (m + 1)) (c : Fin (2 * m + 2)) : ℝ :=
  mass k ((c : ℤ) - (m + 1)) (j₀ + (r : ℤ))

/-- The largest reading in a row of the block: the normalising constant of that row of the
character. Normalising row by row is what makes the character legible: `‖Δ‖` collapses so
fast with height that a single constant would flatten every row but the lowest. -/
def rowPeak (k : ℕ) (j₀ : ℤ) (m : ℕ) (r : Fin (m + 1)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun c : Fin (2 * m + 2) => raw k j₀ m r c

/-- **The character.** The block of readings of `Δ`, each row divided by its own maximum: a
matrix of grey levels in `[0, 1]`, which is what `paper/delta_dissection.svg` plots as a
glyph. -/
def glyph (k : ℕ) (j₀ : ℤ) (m : ℕ) (r : Fin (m + 1)) (c : Fin (2 * m + 2)) : ℝ :=
  raw k j₀ m r c / rowPeak k j₀ m r

theorem raw_le_rowPeak (k : ℕ) (j₀ : ℤ) (m : ℕ) (r : Fin (m + 1)) (c : Fin (2 * m + 2)) :
    raw k j₀ m r c ≤ rowPeak k j₀ m r :=
  Finset.le_sup' (f := fun c : Fin (2 * m + 2) => raw k j₀ m r c) (Finset.mem_univ c)

theorem raw_nonneg (k : ℕ) (j₀ : ℤ) (m : ℕ) (r : Fin (m + 1)) (c : Fin (2 * m + 2)) :
    0 ≤ raw k j₀ m r c := mass_nonneg _ _ _

theorem rowPeak_pos {k : ℕ} {j₀ : ℤ} (hj : 0 ≤ j₀) {m : ℕ} (r : Fin (m + 1)) :
    0 < rowPeak k j₀ m r := by
  have hj' : (0 : ℤ) ≤ j₀ + (r : ℤ) := by positivity
  calc (0 : ℝ) < mass k (-((m : ℤ) + 1)) (j₀ + (r : ℤ)) := mass_pos (k := k) hj'
    _ = raw k j₀ m r ⟨0, by omega⟩ := by simp [raw]
    _ ≤ rowPeak k j₀ m r := raw_le_rowPeak _ _ _ _ _

theorem glyph_nonneg {k : ℕ} {j₀ : ℤ} (hj : 0 ≤ j₀) {m : ℕ} (r : Fin (m + 1))
    (c : Fin (2 * m + 2)) : 0 ≤ glyph k j₀ m r c :=
  div_nonneg (raw_nonneg _ _ _ _ _) (rowPeak_pos hj r).le

theorem glyph_le_one {k : ℕ} {j₀ : ℤ} (hj : 0 ≤ j₀) {m : ℕ} (r : Fin (m + 1))
    (c : Fin (2 * m + 2)) : glyph k j₀ m r c ≤ 1 :=
  (div_le_one (rowPeak_pos hj r)).mpr (raw_le_rowPeak _ _ _ _ _)

/-- The character is normalised row by row: every row of the glyph has a black pixel. -/
theorem glyph_row_eq_one {k : ℕ} {j₀ : ℤ} (hj : 0 ≤ j₀) {m : ℕ} (r : Fin (m + 1)) :
    ∃ c, glyph k j₀ m r c = 1 := by
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty)
    (f := fun c : Fin (2 * m + 2) => raw k j₀ m r c)
  have hpk : rowPeak k j₀ m r = raw k j₀ m r c := hc
  exact ⟨c, by rw [glyph, ← hpk, div_self (ne_of_gt (rowPeak_pos (k := k) hj r))]⟩

/-- The mirror of a column index: the reflection of the block in the wall `x = 0`. -/
def mirrorCol {m : ℕ} (c : Fin (2 * m + 2)) : Fin (2 * m + 2) :=
  ⟨2 * m + 1 - (c : ℕ), by omega⟩

theorem mirrorCol_involutive {m : ℕ} (c : Fin (2 * m + 2)) : mirrorCol (mirrorCol c) = c := by
  have hc : (c : ℕ) < 2 * m + 2 := c.isLt
  ext
  simp only [mirrorCol]
  omega

/-- **The character is a palindrome.** Reflecting the block in the wall `x = 0` leaves every
pixel unchanged — the exact image of `Δ(−z̄) = conj Δ(z)`. -/
theorem glyph_mirror {k : ℕ} {j₀ : ℤ} (hj : 0 ≤ j₀) {m : ℕ} (r : Fin (m + 1))
    (c : Fin (2 * m + 2)) : glyph k j₀ m r (mirrorCol c) = glyph k j₀ m r c := by
  have hc : (c : ℕ) < 2 * m + 2 := c.isLt
  have hidx : ((mirrorCol c : Fin (2 * m + 2)) : ℤ) - (m + 1) = -1 - ((c : ℤ) - (m + 1)) := by
    simp only [mirrorCol, Fin.val_mk]
    omega
  have hj' : (0 : ℤ) ≤ j₀ + (r : ℤ) := by positivity
  rw [glyph, glyph, raw, raw, hidx, mass_mirror hj']

/-! ## Quantising the character to three grey levels -/

/-- The three grey levels of the ternary quantisation, matching the ternary dissection. -/
def level (x : ℝ) : ℕ := if x < 1 / 3 then 0 else if x < 2 / 3 then 1 else 2

theorem level_lt_three (x : ℝ) : level x < 3 := by
  unfold level
  split
  · omega
  · split <;> omega

/-- The character quantised into `ZMod 3`: the three-shade glyph the plate prints. -/
def pix (k : ℕ) (j₀ : ℤ) (m : ℕ) (r : Fin (m + 1)) (c : Fin (2 * m + 2)) : ZMod 3 :=
  (level (glyph k j₀ m r c) : ZMod 3)

theorem pix_mirror {k : ℕ} {j₀ : ℤ} (hj : 0 ≤ j₀) {m : ℕ} (r : Fin (m + 1))
    (c : Fin (2 * m + 2)) : pix k j₀ m r (mirrorCol c) = pix k j₀ m r c := by
  rw [pix, pix, glyph_mirror hj]

end DeltaDissection
