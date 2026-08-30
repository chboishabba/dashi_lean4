/-
# The graph of the modular form, with the prime-power fibers highlighted

This file specifies the picture drawn in `RequestProject/ModularSvg.lean`: the graph of the
`q`-expansion coefficients `τ(n)` of the modular discriminant `Δ = η^24` for `n = 1, …, 256`,
in which the point `n` is highlighted (in the colour of `RequestProject/FiberColors.lean`)
exactly when `n` lies in one of the prime-power fibers of the first twenty primes.

Everything about the picture that can be stated mathematically is proved here:

* which points are highlighted (`isHighlighted_iff_mem_firstTwentyFibers`) and in which colour
  (`pointColor_of_mem_primePowerFiber`);
* how many highlighted points there are (`card_highlighted`, `card_highlighted_red`,
  `card_highlighted_blue`);
* the vertical coordinate: the plotted quantity is the Deligne-normalised value
  `τ(n) / n^{11/2}`, whose square `plotValueSq n` is bounded by `d(n)²` (`plotValueSq_le`)
  and is nonzero on the whole displayed range (`plotValueSq_ne_zero`), so no plotted point sits
  on the axis;
* the highlighted points of each fiber obey the Hecke recursion (`hecke_on_highlighted`) and
  the twenty highlighted primes obey Ramanujan's congruence mod `691` (`tau_congr_691`, in
  `RequestProject/RamanujanTau.lean`).
-/
import RequestProject.RamanujanTau

namespace ModularGraph

open PrimeFibers RamanujanTau

/-- The number of points drawn on the horizontal axis: `n = 1, …, 256`. -/
def displayN : ℕ := RamanujanTau.displayN

theorem displayN_eq : displayN = 256 := rfl

/-! ## Which points are highlighted, and in which colour -/

/-- The colour of the plotted point `(n, τ(n)/n^{11/2})`: the colour of the fiber containing
`n`, or the neutral colour if `n` is in none of the twenty fibers. -/
def pointColor (n : ℕ) : String := cellColor n

/-- A point of the graph is highlighted when it is not painted in the neutral colour. -/
def isHighlighted (n : ℕ) : Bool := pointColor n ≠ neutralColor

theorem isHighlighted_iff {n : ℕ} : isHighlighted n = true ↔ pointColor n ≠ neutralColor := by
  simp [isHighlighted]

/-- A point of the graph is highlighted exactly when it belongs to the union of the twenty
prime-power fibers. -/
theorem isHighlighted_iff_mem_firstTwentyFibers {n : ℕ} (hn : n ≤ displayN) :
    isHighlighted n = true ↔ n ∈ firstTwentyFibers displayN := by
  rw [isHighlighted_iff, pointColor]
  exact cellColor_ne_neutral_iff_mem_firstTwentyFibers hn

/-- A point lying in the fiber of `p` is highlighted in that fiber's colour. -/
theorem pointColor_of_mem_primePowerFiber {p N n : ℕ} (hp : p ∈ first20Primes)
    (hn : n ∈ primePowerFiber p N) : pointColor n = fiberColor p :=
  cellColor_of_mem_primePowerFiber hp hn

/-- Points in the fiber of `p` are highlighted. -/
theorem isHighlighted_of_mem_primePowerFiber {p N n : ℕ} (hp : p ∈ first20Primes)
    (hn : n ∈ primePowerFiber p N) : isHighlighted n = true := by
  rw [isHighlighted_iff, pointColor_of_mem_primePowerFiber hp hn]
  exact fiberColor_ne_neutral hp

/-- Powers `p^k` (`k ≥ 1`) inside the displayed range are highlighted in the colour of `p`. -/
theorem isHighlighted_pow {p k : ℕ} (hp : p ∈ first20Primes) (hk : 0 < k)
    (hle : p ^ k ≤ displayN) : isHighlighted (p ^ k) = true := by
  refine isHighlighted_of_mem_primePowerFiber (N := displayN) hp ?_
  have hpp := prime_of_mem_first20Primes hp
  exact mem_primePowerFiber.2 ⟨⟨Nat.pow_pos hpp.pos, hle⟩, ⟨k, hk, rfl⟩⟩

/-! ## Counting the highlighted points -/

theorem filter_highlighted (N : ℕ) :
    (Finset.Icc 1 N).filter (fun n => isHighlighted n = true) = firstTwentyFibers N := by
  rw [← filter_colored_eq_firstTwentyFibers N]
  exact Finset.filter_congr fun n _ => by simp [isHighlighted, pointColor]

/-- The picture highlights exactly `36` of its `256` points. -/
theorem card_highlighted :
    ((Finset.Icc 1 displayN).filter (fun n => isHighlighted n = true)).card = 36 := by
  rw [filter_highlighted, displayN_eq, card_firstTwentyFibers (by norm_num)]
  decide

/-- Exactly `8` points are red, namely `2, 4, 8, …, 256`. -/
theorem card_highlighted_red :
    ((Finset.Icc 1 displayN).filter (fun n => pointColor n = redColor)).card = 8 :=
  card_red_cells_256

/-- Exactly `5` points are blue, namely `3, 9, 27, 81, 243`. -/
theorem card_highlighted_blue :
    ((Finset.Icc 1 displayN).filter (fun n => pointColor n = blueColor)).card = 5 :=
  card_blue_cells_256

/-! ## The vertical coordinate -/

/-- The square of the plotted (Deligne-normalised) value `τ(n) / n^{11/2}`. -/
def plotValueSq (n : ℕ) : ℚ := ((tau n : ℚ)) ^ 2 / (n : ℚ) ^ 11

/-- The plotted values stay inside the Deligne band: `|τ(n)/n^{11/2}| ≤ d(n)`. -/
theorem plotValueSq_le {n : ℕ} (hn : 0 < n) (hn' : n ≤ displayN) :
    plotValueSq n ≤ ((n.divisors.card : ℚ)) ^ 2 := by
  have h := tau_sq_le_deligne (n := n) hn'
  have hpos : (0 : ℚ) < (n : ℚ) ^ 11 := by positivity
  rw [plotValueSq, div_le_iff₀ hpos]
  have hq : ((tau n : ℚ)) ^ 2 ≤ ((n.divisors.card : ℚ)) ^ 2 * (n : ℚ) ^ 11 := by
    exact_mod_cast (by exact_mod_cast h : ((tau n ^ 2 : ℤ) : ℚ) ≤
      (((n.divisors.card : ℤ) ^ 2 * (n : ℤ) ^ 11 : ℤ) : ℚ))
  simpa using hq

/-- No plotted point sits on the horizontal axis. -/
theorem plotValueSq_ne_zero {n : ℕ} (hn : 0 < n) (hn' : n ≤ displayN) : plotValueSq n ≠ 0 := by
  have h := tau_ne_zero_of_le hn hn'
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have h0 : ((tau n : ℚ)) ≠ 0 := Int.cast_ne_zero.2 h
  rw [plotValueSq]
  positivity

/-! ## Arithmetic visible along the highlighted points -/

/-- Along each fiber, consecutive highlighted points are tied together by the Hecke recursion
`τ(p^{k+2}) = τ(p) τ(p^{k+1}) - p^{11} τ(p^k)`; the two larger points are indeed highlighted. -/
theorem hecke_on_highlighted {p k : ℕ} (hp : p ∈ first20Primes) (hk : p ^ (k + 2) ≤ displayN) :
    isHighlighted (p ^ (k + 2)) = true ∧ isHighlighted (p ^ (k + 1)) = true ∧
      tau (p ^ (k + 2)) = tau p * tau (p ^ (k + 1)) - (p : ℤ) ^ 11 * tau (p ^ k) := by
  have hpp := prime_of_mem_first20Primes hp
  have hle1 : p ^ (k + 1) ≤ p ^ (k + 2) := Nat.pow_le_pow_right hpp.pos (by omega)
  refine ⟨isHighlighted_pow hp (by omega) hk, isHighlighted_pow hp (by omega) (by omega), ?_⟩
  exact tau_hecke_on_fiber hp hk

/-! ## The two-colour graph (fibers of `2` and `3` only) -/

/-- The colour of the point `n` in the restricted picture showing only the fibers of `2` and
`3`. -/
def twoThreePointColor (n : ℕ) : String := twoThreeColor n

/-- In the restricted picture, a point is coloured exactly when it is a positive power of `2`
or of `3`. -/
theorem twoThreePointColor_ne_neutral_iff {n : ℕ} (hn : n ≤ displayN) :
    twoThreePointColor n ≠ neutralColor ↔
      n ∈ primePowerFiber 2 displayN ∪ primePowerFiber 3 displayN :=
  twoThreeColor_ne_neutral_iff hn

/-- Where the restricted picture is coloured, it agrees with the full one. -/
theorem twoThreePointColor_eq_pointColor {n : ℕ} (h : twoThreePointColor n ≠ neutralColor) :
    twoThreePointColor n = pointColor n :=
  twoThreeColor_eq_cellColor h

end ModularGraph
