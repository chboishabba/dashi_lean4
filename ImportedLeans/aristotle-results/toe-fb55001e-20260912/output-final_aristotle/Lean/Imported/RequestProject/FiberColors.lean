/-
# Colouring the prime-power fibers

This file attaches a colour to every natural number according to which prime-power fiber
(`PrimeFibers.primePowerFiber p N`) it belongs to: the fiber of `2` is red, the fiber of `3`
is blue, each of the remaining first twenty primes gets its own colour, and everything that
is not a power of one of those twenty primes gets a neutral background colour.

The colouring is *computable*, so it can be rendered (see `RequestProject/FiberSvg.lean`),
and it is proved to be a faithful picture of the fibers:

* `fiberColor` is injective on `first20Primes` (twenty pairwise distinct colours);
* `cellColor` is constant on each fiber, equal to that fiber's colour
  (`cellColor_of_mem_primePowerFiber`);
* `cellColor n` is red exactly on the fiber of `2` and blue exactly on the fiber of `3`
  (`cellColor_eq_red_iff`, `cellColor_eq_blue_iff`);
* `cellColor n` is the neutral colour exactly off the union of the twenty fibers
  (`cellColor_ne_neutral_iff_mem_firstTwentyFibers`).
-/
import RequestProject.PrimeFibers

namespace PrimeFibers

/-! ## A computable test for being a positive power of `p` -/

/-- Computable test: `n` is `p ^ k` for some `k ≥ 1`. -/
def isPosPowOf (p n : ℕ) : Bool := 2 ≤ n && n == p ^ Nat.log p n

theorem isPosPowOf_iff {p n : ℕ} (hp : 1 < p) :
    isPosPowOf p n = true ↔ ∃ k, 0 < k ∧ n = p ^ k := by
  constructor
  · intro h
    rw [isPosPowOf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hn, heq⟩ := h
    refine ⟨Nat.log p n, ?_, heq⟩
    rcases Nat.eq_zero_or_pos (Nat.log p n) with h0 | h0
    · rw [h0, pow_zero] at heq; omega
    · exact h0
  · rintro ⟨k, hk, rfl⟩
    have h2 : 2 ≤ p ^ k := by
      calc 2 ≤ p := hp
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
    rw [isPosPowOf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.log_pow hp]
    exact ⟨h2, rfl⟩

theorem mem_primePowerFiber_iff_isPosPowOf {p N n : ℕ} (hp : 1 < p) :
    n ∈ primePowerFiber p N ↔ (isPosPowOf p n = true ∧ n ≤ N) := by
  rw [mem_primePowerFiber, isPosPowOf_iff hp]
  constructor
  · rintro ⟨⟨-, hle⟩, hk⟩; exact ⟨hk, hle⟩
  · rintro ⟨⟨k, hk, rfl⟩, hle⟩
    exact ⟨⟨Nat.pow_pos (by omega), hle⟩, ⟨k, hk, rfl⟩⟩

/-- If `n` is a positive power of a prime `p`, then `p` is its least prime factor. -/
theorem minFac_of_isPosPowOf {p n : ℕ} (hp : p.Prime) (h : isPosPowOf p n = true) :
    n.minFac = p := by
  obtain ⟨k, hk, rfl⟩ := (isPosPowOf_iff hp.one_lt).1 h
  exact Nat.Prime.pow_minFac hp hk.ne'

/-! ## The first twenty primes, as a list -/

/-- The list of the first twenty primes, in increasing order (a computable version of
`first20Primes`, used for rendering and for `decide`-style checks). -/
def primeList : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]

/-- The list agrees with the `Finset` of the first twenty primes. -/
theorem primeList_toFinset : primeList.toFinset = first20Primes := by decide

/-- Membership in `first20Primes` is membership in `primeList`. -/
theorem mem_primeList_iff {p : ℕ} : p ∈ primeList ↔ p ∈ first20Primes := by
  rw [← primeList_toFinset, List.mem_toFinset]

/-! ## The palette -/

/-- The neutral background colour, used for every number that is not a power of one of the
first twenty primes. -/
def neutralColor : String := "#eceff4"

/-- The colour of the fiber of `2`. -/
def redColor : String := "#e6194b"

/-- The colour of the fiber of `3`. -/
def blueColor : String := "#4363d8"

/-- The colour attached to a prime: red for `2`, blue for `3`, a distinct colour for each of
the other first twenty primes, and the neutral colour for anything else. -/
def fiberColor (p : ℕ) : String :=
  if p = 2 then redColor
  else if p = 3 then blueColor
  else if p = 5 then "#3cb44b"
  else if p = 7 then "#f58231"
  else if p = 11 then "#911eb4"
  else if p = 13 then "#42d4f4"
  else if p = 17 then "#f032e6"
  else if p = 19 then "#bfef45"
  else if p = 23 then "#fabed4"
  else if p = 29 then "#008080"
  else if p = 31 then "#dcbeff"
  else if p = 37 then "#9a6324"
  else if p = 41 then "#ffd8b1"
  else if p = 43 then "#800000"
  else if p = 47 then "#aaffc3"
  else if p = 53 then "#808000"
  else if p = 59 then "#ffe119"
  else if p = 61 then "#000075"
  else if p = 67 then "#a9a9a9"
  else if p = 71 then "#00bfa0"
  else neutralColor

theorem fiberColor_two : fiberColor 2 = redColor := rfl

theorem fiberColor_three : fiberColor 3 = blueColor := rfl

/-- Each of the twenty primes gets a colour different from the background. -/
theorem fiberColor_ne_neutral {p : ℕ} (hp : p ∈ first20Primes) :
    fiberColor p ≠ neutralColor := by
  fin_cases hp <;> decide

/-- Anything that is not one of the first twenty primes gets the neutral colour. -/
theorem fiberColor_of_not_mem_first20Primes {p : ℕ} (h : p ∉ first20Primes) :
    fiberColor p = neutralColor := by
  have h2 : p ≠ 2 := by rintro rfl; exact h (by decide)
  have h3 : p ≠ 3 := by rintro rfl; exact h (by decide)
  have h5 : p ≠ 5 := by rintro rfl; exact h (by decide)
  have h7 : p ≠ 7 := by rintro rfl; exact h (by decide)
  have h11 : p ≠ 11 := by rintro rfl; exact h (by decide)
  have h13 : p ≠ 13 := by rintro rfl; exact h (by decide)
  have h17 : p ≠ 17 := by rintro rfl; exact h (by decide)
  have h19 : p ≠ 19 := by rintro rfl; exact h (by decide)
  have h23 : p ≠ 23 := by rintro rfl; exact h (by decide)
  have h29 : p ≠ 29 := by rintro rfl; exact h (by decide)
  have h31 : p ≠ 31 := by rintro rfl; exact h (by decide)
  have h37 : p ≠ 37 := by rintro rfl; exact h (by decide)
  have h41 : p ≠ 41 := by rintro rfl; exact h (by decide)
  have h43 : p ≠ 43 := by rintro rfl; exact h (by decide)
  have h47 : p ≠ 47 := by rintro rfl; exact h (by decide)
  have h53 : p ≠ 53 := by rintro rfl; exact h (by decide)
  have h59 : p ≠ 59 := by rintro rfl; exact h (by decide)
  have h61 : p ≠ 61 := by rintro rfl; exact h (by decide)
  have h67 : p ≠ 67 := by rintro rfl; exact h (by decide)
  have h71 : p ≠ 71 := by rintro rfl; exact h (by decide)
  unfold fiberColor
  rw [if_neg h2, if_neg h3, if_neg h5, if_neg h7, if_neg h11, if_neg h13, if_neg h17,
    if_neg h19, if_neg h23, if_neg h29, if_neg h31, if_neg h37, if_neg h41, if_neg h43,
    if_neg h47, if_neg h53, if_neg h59, if_neg h61, if_neg h67, if_neg h71]

/-- Only the first twenty primes get a non-neutral colour. -/
theorem mem_first20Primes_of_fiberColor_ne_neutral {p : ℕ} (h : fiberColor p ≠ neutralColor) :
    p ∈ first20Primes := by
  by_contra hc
  exact h (fiberColor_of_not_mem_first20Primes hc)

/-- The twenty fibers get twenty pairwise distinct colours. -/
theorem fiberColor_injOn :
    ∀ p ∈ first20Primes, ∀ q ∈ first20Primes, fiberColor p = fiberColor q → p = q := by
  decide

/-- Only the fiber of `2` is red. -/
theorem eq_two_of_fiberColor_eq_red {p : ℕ} (h : fiberColor p = redColor) : p = 2 := by
  by_contra hne
  have hmem : p ∈ first20Primes :=
    mem_first20Primes_of_fiberColor_ne_neutral (by rw [h]; decide)
  exact hne (fiberColor_injOn p hmem 2 (by decide) (by rw [h, fiberColor_two]))

/-- Only the fiber of `3` is blue. -/
theorem eq_three_of_fiberColor_eq_blue {p : ℕ} (h : fiberColor p = blueColor) : p = 3 := by
  by_contra hne
  have hmem : p ∈ first20Primes :=
    mem_first20Primes_of_fiberColor_ne_neutral (by rw [h]; decide)
  exact hne (fiberColor_injOn p hmem 3 (by decide) (by rw [h, fiberColor_three]))

/-! ## The colour of a cell -/

/-- The colour of the number `n` in the picture: the colour of the fiber containing `n`, or
the neutral colour if `n` lies in none of the twenty fibers. -/
def cellColor (n : ℕ) : String :=
  if isPosPowOf n.minFac n then fiberColor n.minFac else neutralColor

/-- On the fiber of one of the first twenty primes, the cell colour is that fiber's colour. -/
theorem cellColor_of_mem_primePowerFiber {p N n : ℕ} (hp : p ∈ first20Primes)
    (hn : n ∈ primePowerFiber p N) : cellColor n = fiberColor p := by
  have hpp := prime_of_mem_first20Primes hp
  have h : isPosPowOf p n = true :=
    ((mem_primePowerFiber_iff_isPosPowOf hpp.one_lt).1 hn).1
  have hmin : n.minFac = p := minFac_of_isPosPowOf hpp h
  rw [cellColor, hmin, if_pos h]

/-- A cell is non-neutral exactly when it lies in one of the twenty fibers. -/
theorem cellColor_ne_neutral_iff {n : ℕ} :
    cellColor n ≠ neutralColor ↔
      (isPosPowOf n.minFac n = true ∧ n.minFac ∈ first20Primes) := by
  constructor
  · intro h
    rw [cellColor] at h
    by_cases hpow : isPosPowOf n.minFac n = true
    · rw [if_pos hpow] at h
      exact ⟨hpow, mem_first20Primes_of_fiberColor_ne_neutral h⟩
    · rw [if_neg hpow] at h; exact absurd rfl h
  · rintro ⟨hpow, hmem⟩
    rw [cellColor, if_pos hpow]
    exact fiberColor_ne_neutral hmem

/-- The picture is faithful: within the displayed range `n ≤ N`, a cell is coloured exactly
when the number belongs to the union of the twenty fibers. -/
theorem cellColor_ne_neutral_iff_mem_firstTwentyFibers {N n : ℕ} (hn : n ≤ N) :
    cellColor n ≠ neutralColor ↔ n ∈ firstTwentyFibers N := by
  rw [cellColor_ne_neutral_iff, firstTwentyFibers, Finset.mem_biUnion]
  constructor
  · rintro ⟨hpow, hmem⟩
    exact ⟨n.minFac, hmem,
      (mem_primePowerFiber_iff_isPosPowOf
        (prime_of_mem_first20Primes hmem).one_lt).2 ⟨hpow, hn⟩⟩
  · rintro ⟨p, hp, hnp⟩
    have hpp := prime_of_mem_first20Primes hp
    have h : isPosPowOf p n = true :=
      ((mem_primePowerFiber_iff_isPosPowOf hpp.one_lt).1 hnp).1
    have hmin : n.minFac = p := minFac_of_isPosPowOf hpp h
    exact ⟨by rw [hmin]; exact h, by rw [hmin]; exact hp⟩

/-- The red region of the picture is exactly the fiber of `2`. -/
theorem cellColor_eq_red_iff {n : ℕ} :
    cellColor n = redColor ↔ ∃ k, 0 < k ∧ n = 2 ^ k := by
  constructor
  · intro h
    have hne : cellColor n ≠ neutralColor := by rw [h]; decide
    obtain ⟨hpow, -⟩ := cellColor_ne_neutral_iff.1 hne
    rw [cellColor, if_pos hpow] at h
    have hmin : n.minFac = 2 := eq_two_of_fiberColor_eq_red h
    rw [hmin] at hpow
    exact (isPosPowOf_iff (by norm_num)).1 hpow
  · rintro ⟨k, hk, rfl⟩
    have hpow : isPosPowOf 2 (2 ^ k) = true :=
      (isPosPowOf_iff (by norm_num)).2 ⟨k, hk, rfl⟩
    have hmin : (2 ^ k).minFac = 2 := minFac_of_isPosPowOf Nat.prime_two hpow
    rw [cellColor, hmin, if_pos hpow, fiberColor_two]

/-- The blue region of the picture is exactly the fiber of `3`. -/
theorem cellColor_eq_blue_iff {n : ℕ} :
    cellColor n = blueColor ↔ ∃ k, 0 < k ∧ n = 3 ^ k := by
  constructor
  · intro h
    have hne : cellColor n ≠ neutralColor := by rw [h]; decide
    obtain ⟨hpow, -⟩ := cellColor_ne_neutral_iff.1 hne
    rw [cellColor, if_pos hpow] at h
    have hmin : n.minFac = 3 := eq_three_of_fiberColor_eq_blue h
    rw [hmin] at hpow
    exact (isPosPowOf_iff (by norm_num)).1 hpow
  · rintro ⟨k, hk, rfl⟩
    have hpow : isPosPowOf 3 (3 ^ k) = true :=
      (isPosPowOf_iff (by norm_num)).2 ⟨k, hk, rfl⟩
    have hmin : (3 ^ k).minFac = 3 := minFac_of_isPosPowOf Nat.prime_three hpow
    rw [cellColor, hmin, if_pos hpow, fiberColor_three]

/-- Red and blue never meet: no cell is both. -/
theorem red_ne_blue : redColor ≠ blueColor := by decide

/-! ## Counting the coloured cells of the picture -/

/-- The red cells of the picture of `1, …, N` are exactly the fiber of `2`. -/
theorem filter_red_eq_primePowerFiber (N : ℕ) :
    (Finset.Icc 1 N).filter (fun n => cellColor n = redColor) = primePowerFiber 2 N := by
  ext n
  rw [Finset.mem_filter, Finset.mem_Icc, mem_primePowerFiber, cellColor_eq_red_iff]
  constructor
  · rintro ⟨⟨-, hle⟩, hk⟩
    exact ⟨⟨by obtain ⟨k, hk0, rfl⟩ := hk; exact Nat.pow_pos (by norm_num), hle⟩, hk⟩
  · rintro ⟨⟨hpos, hle⟩, hk⟩
    exact ⟨⟨hpos, hle⟩, hk⟩

/-- The blue cells of the picture of `1, …, N` are exactly the fiber of `3`. -/
theorem filter_blue_eq_primePowerFiber (N : ℕ) :
    (Finset.Icc 1 N).filter (fun n => cellColor n = blueColor) = primePowerFiber 3 N := by
  ext n
  rw [Finset.mem_filter, Finset.mem_Icc, mem_primePowerFiber, cellColor_eq_blue_iff]
  constructor
  · rintro ⟨⟨-, hle⟩, hk⟩
    exact ⟨⟨by obtain ⟨k, hk0, rfl⟩ := hk; exact Nat.pow_pos (by norm_num), hle⟩, hk⟩
  · rintro ⟨⟨hpos, hle⟩, hk⟩
    exact ⟨⟨hpos, hle⟩, hk⟩

/-- The coloured cells of the picture of `1, …, N` are exactly the union of the twenty
fibers. -/
theorem filter_colored_eq_firstTwentyFibers (N : ℕ) :
    (Finset.Icc 1 N).filter (fun n => cellColor n ≠ neutralColor) = firstTwentyFibers N := by
  ext n
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨-, hle⟩, h⟩
    exact (cellColor_ne_neutral_iff_mem_firstTwentyFibers hle).1 h
  · intro h
    have hle : n ≤ N := by
      rw [firstTwentyFibers, Finset.mem_biUnion] at h
      obtain ⟨p, -, hnp⟩ := h
      exact (mem_primePowerFiber.1 hnp).1.2
    have hpos : 1 ≤ n := by
      rw [firstTwentyFibers, Finset.mem_biUnion] at h
      obtain ⟨p, -, hnp⟩ := h
      exact (mem_primePowerFiber.1 hnp).1.1
    exact ⟨⟨hpos, hle⟩, (cellColor_ne_neutral_iff_mem_firstTwentyFibers hle).2 h⟩

/-- There are `Nat.log 2 N` red cells in the picture of `1, …, N`. -/
theorem card_red_cells {N : ℕ} (hN : N ≠ 0) :
    ((Finset.Icc 1 N).filter (fun n => cellColor n = redColor)).card = Nat.log 2 N := by
  rw [filter_red_eq_primePowerFiber, card_primePowerFiber (by norm_num) hN]

/-- There are `Nat.log 3 N` blue cells in the picture of `1, …, N`. -/
theorem card_blue_cells {N : ℕ} (hN : N ≠ 0) :
    ((Finset.Icc 1 N).filter (fun n => cellColor n = blueColor)).card = Nat.log 3 N := by
  rw [filter_blue_eq_primePowerFiber, card_primePowerFiber (by norm_num) hN]

/-- In the rendered picture of `1, …, 256` there are `8` red cells. -/
theorem card_red_cells_256 :
    ((Finset.Icc 1 256).filter (fun n => cellColor n = redColor)).card = 8 := by
  rw [card_red_cells (by norm_num)]
  decide

/-- In the rendered picture of `1, …, 256` there are `5` blue cells. -/
theorem card_blue_cells_256 :
    ((Finset.Icc 1 256).filter (fun n => cellColor n = blueColor)).card = 5 := by
  rw [card_blue_cells (by norm_num)]
  decide

/-- In the rendered picture of `1, …, 256` there are `36` coloured cells in total. -/
theorem card_colored_cells_256 :
    ((Finset.Icc 1 256).filter (fun n => cellColor n ≠ neutralColor)).card = 36 := by
  rw [filter_colored_eq_firstTwentyFibers, card_firstTwentyFibers (by norm_num)]
  decide

/-! ## The two-colour picture of the fibers of `2` and `3` -/

/-- The restricted colouring showing only the fiber of `2` (red) and the fiber of `3`
(blue). -/
def twoThreeColor (n : ℕ) : String :=
  if isPosPowOf 2 n then redColor else if isPosPowOf 3 n then blueColor else neutralColor

/-- The red region of the two-colour picture is exactly the fiber of `2`. -/
theorem twoThreeColor_eq_red_iff {n : ℕ} :
    twoThreeColor n = redColor ↔ ∃ k, 0 < k ∧ n = 2 ^ k := by
  rw [twoThreeColor]
  constructor
  · intro h
    by_cases h2 : isPosPowOf 2 n = true
    · exact (isPosPowOf_iff (by norm_num)).1 h2
    · rw [if_neg h2] at h
      split_ifs at h <;> exact absurd h (by decide)
  · rintro ⟨k, hk, rfl⟩
    rw [if_pos ((isPosPowOf_iff (by norm_num)).2 ⟨k, hk, rfl⟩)]

/-- The blue region of the two-colour picture is exactly the fiber of `3`. -/
theorem twoThreeColor_eq_blue_iff {n : ℕ} :
    twoThreeColor n = blueColor ↔ ∃ k, 0 < k ∧ n = 3 ^ k := by
  rw [twoThreeColor]
  constructor
  · intro h
    by_cases h2 : isPosPowOf 2 n = true
    · rw [if_pos h2] at h; exact absurd h (by decide)
    · rw [if_neg h2] at h
      by_cases h3 : isPosPowOf 3 n = true
      · exact (isPosPowOf_iff (by norm_num)).1 h3
      · rw [if_neg h3] at h; exact absurd h (by decide)
  · rintro ⟨k, hk, rfl⟩
    have h3 : isPosPowOf 3 (3 ^ k) = true := (isPosPowOf_iff (by norm_num)).2 ⟨k, hk, rfl⟩
    have h2 : isPosPowOf 2 (3 ^ k) ≠ true := by
      intro h2
      have e2 : (3 ^ k).minFac = 2 := minFac_of_isPosPowOf Nat.prime_two h2
      have e3 : (3 ^ k).minFac = 3 := minFac_of_isPosPowOf Nat.prime_three h3
      omega
    rw [if_neg h2, if_pos h3]

/-- Where the two-colour picture is not neutral, it agrees with the full colouring. -/
theorem twoThreeColor_eq_cellColor {n : ℕ} (h : twoThreeColor n ≠ neutralColor) :
    twoThreeColor n = cellColor n := by
  rw [twoThreeColor] at h ⊢
  by_cases h2 : isPosPowOf 2 n = true
  · rw [if_pos h2, (cellColor_eq_red_iff).2 ((isPosPowOf_iff (by norm_num)).1 h2)]
  · rw [if_neg h2] at h ⊢
    by_cases h3 : isPosPowOf 3 n = true
    · rw [if_pos h3, (cellColor_eq_blue_iff).2 ((isPosPowOf_iff (by norm_num)).1 h3)]
    · rw [if_neg h3] at h; exact absurd rfl h

/-- The two-colour picture is coloured exactly on the union of the fibers of `2` and `3`. -/
theorem twoThreeColor_ne_neutral_iff {N n : ℕ} (hn : n ≤ N) :
    twoThreeColor n ≠ neutralColor ↔
      n ∈ primePowerFiber 2 N ∪ primePowerFiber 3 N := by
  rw [Finset.mem_union, mem_primePowerFiber_iff_isPosPowOf (by norm_num),
    mem_primePowerFiber_iff_isPosPowOf (by norm_num), twoThreeColor]
  constructor
  · intro h
    by_cases h2 : isPosPowOf 2 n = true
    · exact Or.inl ⟨h2, hn⟩
    · rw [if_neg h2] at h
      by_cases h3 : isPosPowOf 3 n = true
      · exact Or.inr ⟨h3, hn⟩
      · rw [if_neg h3] at h; exact absurd rfl h
  · rintro (⟨h2, -⟩ | ⟨h3, -⟩)
    · rw [if_pos h2]; decide
    · by_cases h2 : isPosPowOf 2 n = true
      · rw [if_pos h2]; decide
      · rw [if_neg h2, if_pos h3]; decide

end PrimeFibers
