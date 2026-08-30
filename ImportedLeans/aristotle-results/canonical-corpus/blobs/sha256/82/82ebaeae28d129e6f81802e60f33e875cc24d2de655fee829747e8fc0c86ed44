import Mathlib
import RequestProject.SvgCore
import RequestProject.Frobenius
import RequestProject.FrobeniusOrbit

/-!
# Six posters for students

A second, *pedagogical* gallery.  Where the pictures of `RequestProject/Visualization.lean`
and friends record what the project proves, the six posters drawn here are meant to be put on
a wall: each one takes a single idea of the project, draws it as large and as concretely as
possible, and ends with an invitation to check the next case by hand.

The rule of the project is kept: everything numerical that is drawn is *computed in Lean* and
pinned down by kernel computation or by a proof, so a student copying numbers off a poster is
copying verified numbers.

* `svg/student-1-freshmans-dream.svg` (`StudentViz.dreamSvg`) — Pascal's triangle mod `3`.
  Why `x ↦ xᵖ` is additive at all: the interior of row `p` is divisible by `p`
  (`StudentViz.interior_row_prime_dvd`), so `(x+y)ᵖ = xᵖ + yᵖ`
  (`StudentViz.freshmans_dream`), and the same happens in every row `pʲ`
  (`StudentViz.interior_row_prime_pow_dvd`).
* `svg/student-2-cyclotomic-clocks.svg` (`StudentViz.clocksSvg`) — Frobenius orbits without
  ever building a field: on `GF(pᵏ)ˣ ≅ ℤ/(pᵏ−1)` the map `x ↦ xᵖ` is `j ↦ p·j`, so the orbits
  are the *cyclotomic cosets*.  Drawn for `GF(8)`, `GF(9)`, `GF(16)`; the fixed points are
  proved to be exactly the multiples of `(pᵏ−1)/(p−1)`, i.e. `𝔽ₚˣ`
  (`StudentViz.clock8_fixed_iff`, `StudentViz.clock9_fixed_iff`, `StudentViz.clock16_fixed_iff`).
* `svg/student-3-subfield-tower.svg` (`StudentViz.towerSvg`) — the subfields of `GF(2¹²)` as
  the divisors of `12` (`StudentViz.subfieldDegrees_eq`, `StudentViz.coverEdges_eq`), each one
  the fixed field of an iterate of Frobenius; the prime subfield at the bottom is the fixed
  field of Frobenius itself.
* `svg/student-4-dictionary.svg` (`StudentViz.dictionarySvg`) — the two halves of the project
  side by side as a dictionary: centre ↔ prime subfield, transfer ↔ orbit product, index ↔
  `1 + p + ⋯ + p^(k−1)`.
* `svg/student-5-orbit-spiral.svg` (`StudentViz.spiralSvg`) — the orbit product
  `N(x) = x · xᵖ ⋯ x^(p^(k−1)) = x^(1+p+⋯+p^(k−1))` as a spiral closing up on the prime
  subfield, with the exponent identity `(p−1)·(1+p+⋯+p^(k−1)) = pᵏ − 1`
  (`FrobeniusOrbit.geom_sum_mul_pred`) as the reason it lands there.
* `svg/student-6-exercise-ladder.svg` (`StudentViz.ladderSvg`) — ten exercises, easiest first,
  each naming the theorem in this project that answers it.
-/

namespace StudentViz

open SvgCore

/-! ## Poster 1: Pascal's triangle mod p -/

/-- Row `n` of Pascal's triangle. -/
def pascalRow (n : Nat) : List Nat := (List.range (n + 1)).map (Nat.choose n)

/-- The entry drawn in cell `(n, i)` of the poster: `C(n,i) mod p`. -/
def pascalCell (p n i : Nat) : Nat := Nat.choose n i % p

/-- A cell of the poster is drawn pale exactly when the binomial coefficient it holds is
divisible by `p`. -/
theorem pascalCell_eq_zero_iff (p n i : Nat) : pascalCell p n i = 0 ↔ p ∣ Nat.choose n i := by
  simp [pascalCell, Nat.dvd_iff_mod_eq_zero]

/-- **The gap in row `p`.**  Every interior entry of row `p` of Pascal's triangle is divisible
by `p` — the fact that makes `x ↦ xᵖ` additive. -/
theorem interior_row_prime_dvd {p : Nat} (hp : p.Prime) {i : Nat} (h0 : i ≠ 0) (hi : i < p) :
    p ∣ Nat.choose p i :=
  hp.dvd_choose_self h0 hi

/-- **The gap in row `pʲ`.**  The same holds in every row a power of `p`, which is why every
iterate `x ↦ x^(pʲ)` is additive too. -/
theorem interior_row_prime_pow_dvd {p : Nat} (hp : p.Prime) {j i : Nat} (h0 : i ≠ 0)
    (hi : i < p ^ j) : p ∣ Nat.choose (p ^ j) i :=
  hp.dvd_choose_pow h0 (Nat.ne_of_lt hi)

/-- **The freshman's dream**, the statement the poster is about: in a commutative ring of
characteristic `p`, the Frobenius map is additive. -/
theorem freshmans_dream {R : Type*} [CommRing R] (p : Nat) [Fact p.Prime] [CharP R p]
    (x y : R) : (x + y) ^ p = x ^ p + y ^ p := add_pow_char x y p

/-- Row `3` mod `3` really is `1 0 0 1`, as drawn. -/
theorem pascalRow_three_mod : (pascalRow 3).map (· % 3) = [1, 0, 0, 1] := by decide

/-- Row `9` mod `3` really is `1 0 0 0 0 0 0 0 0 1`, as drawn. -/
theorem pascalRow_nine_mod :
    (pascalRow 9).map (· % 3) = [1, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by decide

/-! ## Poster 2: cyclotomic cosets, i.e. Frobenius orbits on the exponent clock -/

/-- One tick of the clock: on `GF(pᵏ)ˣ ≅ ℤ/m` with `m = pᵏ − 1`, Frobenius `x ↦ xᵖ` is the
map `j ↦ p·j` on exponents. -/
def clockStep (p m j : Nat) : Nat := p * j % m

/-- The Frobenius orbit (cyclotomic coset) of the exponent `j`. -/
def cosetOf (p m k j : Nat) : List Nat := ((List.range k).map fun i => p ^ i * j % m).dedup

/-- The partition of the clock `ℤ/m` into Frobenius orbits, one entry per orbit, each orbit
listed from its smallest element. -/
def cosets (p m k : Nat) : List (List Nat) :=
  ((List.range m).filter fun j => (cosetOf p m k j).all fun i => decide (j ≤ i)).map
    (cosetOf p m k)

/-- `GF(8)`: the clock `ℤ/7` splits into `{0}` and two orbits of size `3`. -/
theorem cosets8_eq : cosets 2 7 3 = [[0], [1, 2, 4], [3, 6, 5]] := by decide

/-- `GF(9)`: the clock `ℤ/8` splits into `{0}`, `{4}` and three orbits of size `2`. -/
theorem cosets9_eq : cosets 3 8 2 = [[0], [1, 3], [2, 6], [4], [5, 7]] := by decide

/-- `GF(16)`: the clock `ℤ/15` splits into `{0}`, `{5,10}` and three orbits of size `4`. -/
theorem cosets16_eq :
    cosets 2 15 4 = [[0], [1, 2, 4, 8], [3, 6, 12, 9], [5, 10], [7, 14, 13, 11]] := by decide

/-- Every position of the `GF(8)` clock lies in exactly one drawn orbit. -/
theorem cosets8_cover (j : Nat) (hj : j < 7) : (cosets 2 7 3).flatten.count j = 1 := by
  have h : ∀ j ∈ List.range 7, (cosets 2 7 3).flatten.count j = 1 := by decide
  exact h j (List.mem_range.2 hj)

/-- Every position of the `GF(9)` clock lies in exactly one drawn orbit. -/
theorem cosets9_cover (j : Nat) (hj : j < 8) : (cosets 3 8 2).flatten.count j = 1 := by
  have h : ∀ j ∈ List.range 8, (cosets 3 8 2).flatten.count j = 1 := by decide
  exact h j (List.mem_range.2 hj)

/-- Every position of the `GF(16)` clock lies in exactly one drawn orbit. -/
theorem cosets16_cover (j : Nat) (hj : j < 15) : (cosets 2 15 4).flatten.count j = 1 := by
  have h : ∀ j ∈ List.range 15, (cosets 2 15 4).flatten.count j = 1 := by decide
  exact h j (List.mem_range.2 hj)

/-- **The gold points of the `GF(8)` clock are `𝔽₂ˣ`**: the only fixed exponent is `0`, i.e.
the only Frobenius-fixed unit is `1`, and `7/(2−1) = 7`. -/
theorem clock8_fixed_iff (j : Nat) (hj : j < 7) : clockStep 2 7 j = j ↔ 7 ∣ j := by
  have h : ∀ j ∈ List.range 7, (clockStep 2 7 j = j ↔ 7 ∣ j) := by decide
  exact h j (List.mem_range.2 hj)

/-- **The gold points of the `GF(9)` clock are `𝔽₃ˣ`**: the fixed exponents are `0` and `4`,
i.e. the multiples of `8/(3−1) = 4`. -/
theorem clock9_fixed_iff (j : Nat) (hj : j < 8) : clockStep 3 8 j = j ↔ 4 ∣ j := by
  have h : ∀ j ∈ List.range 8, (clockStep 3 8 j = j ↔ 4 ∣ j) := by decide
  exact h j (List.mem_range.2 hj)

/-- **The gold points of the `GF(16)` clock are `𝔽₂ˣ`**: again only `0`, and
`15/(2−1) = 15`. -/
theorem clock16_fixed_iff (j : Nat) (hj : j < 15) : clockStep 2 15 j = j ↔ 15 ∣ j := by
  have h : ∀ j ∈ List.range 15, (clockStep 2 15 j = j ↔ 15 ∣ j) := by decide
  exact h j (List.mem_range.2 hj)

/-- Every orbit length divides the degree `k` — the fact that turns the orbit picture into the
subfield picture of poster 3.  Here for the three drawn clocks. -/
theorem coset_length_dvd :
    (∀ o ∈ cosets 2 7 3, o.length ∣ 3) ∧ (∀ o ∈ cosets 3 8 2, o.length ∣ 2) ∧
      (∀ o ∈ cosets 2 15 4, o.length ∣ 4) := by decide

/-! ## Poster 3: the subfields of `GF(2¹²)` -/

/-- The degrees of the subfields of `GF(p¹²)`: the divisors of `12`. -/
def subfieldDegrees : List Nat := (List.range 13).filter fun d => decide (0 < d ∧ d ∣ 12)

theorem subfieldDegrees_eq : subfieldDegrees = [1, 2, 3, 4, 6, 12] := by decide

/-- The covering relations of the divisor lattice of `12`: the edges of the Hasse diagram
drawn on the poster. -/
def coverEdges : List (Nat × Nat) :=
  (subfieldDegrees.flatMap fun d => subfieldDegrees.map fun e => (d, e)).filter
    fun (d, e) => decide (d ∣ e ∧ d ≠ e ∧ ∀ c ∈ subfieldDegrees, d ∣ c → c ∣ e → c = d ∨ c = e)

theorem coverEdges_eq :
    coverEdges = [(1, 2), (1, 3), (2, 4), (2, 6), (3, 6), (4, 12), (6, 12)] := by decide

/-- **Why the tower is the divisor lattice.**  Inside a field of `pⁿ` elements, the fixed
field of the `k`-th Frobenius iterate has `p^gcd(k,n)` elements; taking `k ∣ n` gives one
subfield of size `p^k` for each divisor `k` of `n`.  (Proved in
`RequestProject/FrobeniusOrbit.lean`; restated here as the poster's caption.) -/
theorem tower_card {K : Type*} [Field K] [Fintype K] {p : Nat} [Fact p.Prime] [CharP K p]
    {n : Nat} (hK : Nat.card K = p ^ n) (hn : n ≠ 0) (k : Nat) :
    Nat.card (FrobeniusPrimeSubfield.fixedSubfield K p k) = p ^ Nat.gcd k n :=
  FrobeniusPrimeSubfield.card_fixedSubfield hK hn k

/-! ## Poster 5: the orbit product and its exponent -/

/-- The exponent of the orbit product: `N(x) = x^(1 + p + ⋯ + p^(k−1))`. -/
def normExp (p k : Nat) : Nat := ∑ i ∈ Finset.range k, p ^ i

/-- The exponent drawn on the poster for `GF(27)` is `13`. -/
theorem normExp_three_three : normExp 3 3 = 13 := by decide

/-- The exponents drawn for `GF(8)`, `GF(9)`, `GF(16)`, `GF(81)`. -/
theorem normExp_samples :
    normExp 2 3 = 7 ∧ normExp 3 2 = 4 ∧ normExp 2 4 = 15 ∧ normExp 3 4 = 40 := by decide

/-- **Why the orbit product lands in `𝔽ₚ`**: its exponent is `(pᵏ − 1)/(p − 1)`, so
`N(x)^(p−1) = x^(pᵏ−1) = 1` for `x ≠ 0`. -/
theorem normExp_mul_pred (p k : Nat) (hp : 1 ≤ p) : normExp p k * (p - 1) = p ^ k - 1 :=
  FrobeniusPrimeSubfield.geom_sum_mul_pred p k hp

end StudentViz
