/-
# More primes in the diagram: the first fifty primes

The pictures of `RequestProject/FiberSvg.lean` used the first twenty primes `2, …, 71`.
This file widens that to the **first fifty primes** `2, 3, 5, …, 229`, keeping every colour
of the old palette so the new picture extends the old one rather than replacing it.

What is proved here:

* `PrimeFibers.first50Primes` is exactly the set of primes `≤ 229` (so it really is an
  initial segment of the primes) and has cardinality `50`; it contains `first20Primes`, the
  eighteen primes of the sporadic groups and the fifteen primes of the Monster;
* `PrimeFibers.extFiberColor` gives the fifty fibers fifty pairwise distinct colours, and
  agrees with the old `fiberColor` on the first twenty primes;
* `PrimeFibers.extCellColor` is constant on each fiber, and is non-neutral exactly on the
  union `first50Fibers N` of the fifty fibers;
* the union has `∑_{p ≤ 229} log_p N` elements, `66` of them for `N = 256` and `76` for
  `N = 1024`, against `36` and `40` for the twenty-prime picture;
* on the zeta side, `Sporadic.extendedEulerProduct s = ∏_{p ≤ 229} (1 - p^{-s})⁻¹` sits
  between the Monster's fifteen-factor Euler product and `ζ(s)`:
  `∑_{d ∣ |M|} d^{-s} ≤ ∏_{p ∣ |M|} (1-p^{-s})⁻¹ ≤ ∏_{p ≤ 229} (1-p^{-s})⁻¹ ≤ ζ(s)`.
-/
import RequestProject.MonsterZeta
import RequestProject.FiberColors

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace PrimeFibers

open Finset

/-! ## The first fifty primes -/

/-- The first fifty prime numbers, `2, 3, 5, …, 229`. -/
def first50Primes : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163,
   167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229}

/-- There are fifty of them. -/
theorem card_first50Primes : first50Primes.card = 50 := by decide

/-- `first50Primes` is precisely the set of primes below `230`: an initial segment of the
primes. -/
theorem first50Primes_eq_filter :
    first50Primes = (Finset.range 230).filter Nat.Prime := by decide

theorem mem_first50Primes_iff {p : ℕ} : p ∈ first50Primes ↔ p.Prime ∧ p ≤ 229 := by
  rw [first50Primes_eq_filter]
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  tauto

theorem prime_of_mem_first50Primes {p : ℕ} (hp : p ∈ first50Primes) : p.Prime :=
  (mem_first50Primes_iff.1 hp).1

theorem le_of_mem_first50Primes {p : ℕ} (hp : p ∈ first50Primes) : p ≤ 229 :=
  (mem_first50Primes_iff.1 hp).2

/-- The new list of primes extends the old one. -/
theorem first20Primes_subset_first50Primes : first20Primes ⊆ first50Primes := by decide

/-- Every prime dividing the order of a sporadic simple group is one of the fifty. -/
theorem sporadicPrimes_subset_first50Primes : Sporadic.sporadicPrimes ⊆ first50Primes := by
  decide

/-- Every prime dividing the order of the Monster is one of the fifty. -/
theorem monsterPrimes_subset_first50Primes : Sporadic.monsterPrimes ⊆ first50Primes := by
  decide

/-- The list of the first fifty primes, in increasing order (a computable version of
`first50Primes`, used for rendering and for `decide`-style checks). -/
def extPrimeList : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163,
   167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229]

theorem extPrimeList_length : extPrimeList.length = 50 := rfl

theorem extPrimeList_toFinset : extPrimeList.toFinset = first50Primes := by decide

theorem mem_extPrimeList_iff {p : ℕ} : p ∈ extPrimeList ↔ p ∈ first50Primes := by
  rw [← extPrimeList_toFinset, List.mem_toFinset]

/-- The old twenty-prime list is an initial segment of the new one. -/
theorem primeList_prefix : extPrimeList.take 20 = primeList := rfl

/-! ## The extended palette -/

/-- Fifty pairwise distinct colours, one per prime; the first twenty are exactly the colours
already used by `fiberColor`, so the wider picture extends the earlier one. -/
def extPalette : List String :=
  ["#e6194b", "#4363d8", "#3cb44b", "#f58231", "#911eb4", "#42d4f4", "#f032e6", "#bfef45",
   "#fabed4", "#008080", "#dcbeff", "#9a6324", "#ffd8b1", "#800000", "#aaffc3", "#808000",
   "#ffe119", "#000075", "#a9a9a9", "#00bfa0",
   "#b30059", "#1f77b4", "#2ca02c", "#d62728", "#9467bd", "#8c564b", "#e377c2", "#7f7f7f",
   "#bcbd22", "#17becf", "#393b79", "#637939", "#8c6d31", "#843c39", "#7b4173", "#5254a3",
   "#8ca252", "#bd9e39", "#ad494a", "#a55194", "#6b6ecf", "#b5cf6b", "#e7ba52", "#d6616b",
   "#ce6dbd", "#9c9ede", "#cedb9c", "#e7cb94", "#e7969c", "#de9ed6"]

theorem extPalette_length : extPalette.length = 50 := rfl

/-- The fifty colours are pairwise distinct. -/
theorem extPalette_nodup : extPalette.Nodup := by decide

/-- The colour attached to a prime in the wider picture: the colour of its position in
`extPrimeList`, or the neutral background colour for anything that is not one of the fifty
primes. -/
def extFiberColor (p : ℕ) : String := extPalette.getD (extPrimeList.idxOf p) neutralColor

/-- On the first twenty primes the new palette reproduces the old one, so the earlier
pictures are unchanged inside the wider one. -/
theorem extFiberColor_eq_fiberColor : ∀ p ∈ first20Primes, extFiberColor p = fiberColor p := by
  decide

/-- Each of the fifty primes gets a colour different from the background. -/
theorem extFiberColor_ne_neutral {p : ℕ} (hp : p ∈ first50Primes) :
    extFiberColor p ≠ neutralColor := by
  revert hp
  revert p
  decide

/-- Anything that is not one of the fifty primes gets the neutral colour. -/
theorem extFiberColor_of_not_mem {p : ℕ} (hp : p ∉ first50Primes) :
    extFiberColor p = neutralColor := by
  have hL : p ∉ extPrimeList := fun h => hp (mem_extPrimeList_iff.1 h)
  have hidx : extPrimeList.idxOf p = extPrimeList.length := List.idxOf_eq_length_iff.2 hL
  rw [extFiberColor, List.getD_eq_default]
  rw [hidx, extPrimeList_length, extPalette_length]

theorem mem_first50Primes_of_extFiberColor_ne_neutral {p : ℕ}
    (h : extFiberColor p ≠ neutralColor) : p ∈ first50Primes := by
  by_contra hc
  exact h (extFiberColor_of_not_mem hc)

/-- The fifty fibers get fifty pairwise distinct colours. -/
theorem extFiberColor_injOn :
    ∀ p ∈ first50Primes, ∀ q ∈ first50Primes, extFiberColor p = extFiberColor q → p = q := by
  decide

/-! ## The colour of a cell in the wider picture -/

/-- The colour of the number `n` in the wider picture: the colour of the fiber containing
`n`, or the neutral colour if `n` lies in none of the fifty fibers. -/
def extCellColor (n : ℕ) : String :=
  if isPosPowOf n.minFac n then extFiberColor n.minFac else neutralColor

/-- On the fiber of one of the fifty primes, the cell colour is that fiber's colour. -/
theorem extCellColor_of_mem_primePowerFiber {p N n : ℕ} (hp : p ∈ first50Primes)
    (hn : n ∈ primePowerFiber p N) : extCellColor n = extFiberColor p := by
  have hpp := prime_of_mem_first50Primes hp
  have h : isPosPowOf p n = true :=
    ((mem_primePowerFiber_iff_isPosPowOf hpp.one_lt).1 hn).1
  have hmin : n.minFac = p := minFac_of_isPosPowOf hpp h
  rw [extCellColor, hmin, if_pos h]

/-- A cell of the wider picture is non-neutral exactly when it is a power of one of the
fifty primes. -/
theorem extCellColor_ne_neutral_iff {n : ℕ} :
    extCellColor n ≠ neutralColor ↔
      (isPosPowOf n.minFac n = true ∧ n.minFac ∈ first50Primes) := by
  constructor
  · intro h
    rw [extCellColor] at h
    by_cases hpow : isPosPowOf n.minFac n = true
    · rw [if_pos hpow] at h
      exact ⟨hpow, mem_first50Primes_of_extFiberColor_ne_neutral h⟩
    · rw [if_neg hpow] at h; exact absurd rfl h
  · rintro ⟨hpow, hmem⟩
    rw [extCellColor, if_pos hpow]
    exact extFiberColor_ne_neutral hmem

/-! ## The union of the fifty fibers -/

/-- All `n ≤ N` that are powers of one of the first fifty primes. -/
noncomputable def first50Fibers (N : ℕ) : Finset ℕ :=
  first50Primes.biUnion (fun p => primePowerFiber p N)

theorem mem_first50Fibers {N n : ℕ} :
    n ∈ first50Fibers N ↔ n ≤ N ∧ IsPrimePow n ∧ n.minFac ∈ first50Primes := by
  constructor
  · intro hn
    rw [first50Fibers, Finset.mem_biUnion] at hn
    obtain ⟨p, hp, hnp⟩ := hn
    obtain ⟨⟨-, hle⟩, k, hk, rfl⟩ := mem_primePowerFiber.1 hnp
    have hpp := prime_of_mem_first50Primes hp
    refine ⟨hle, ⟨p, k, hpp.prime, hk, rfl⟩, ?_⟩
    rwa [Nat.Prime.pow_minFac hpp hk.ne']
  · rintro ⟨hle, hpp, hmin⟩
    have hn0 : 0 < n := hpp.pos
    rw [first50Fibers, Finset.mem_biUnion]
    refine ⟨n.minFac, hmin, mem_primePowerFiber.2 ⟨⟨hn0, hle⟩, ?_⟩⟩
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    exact ⟨k, hk, by rw [Nat.Prime.pow_minFac hp.nat_prime hk.ne']⟩

/-- The wider picture contains the earlier one: every cell coloured before is still
coloured. -/
theorem firstTwentyFibers_subset_first50Fibers (N : ℕ) :
    firstTwentyFibers N ⊆ first50Fibers N := by
  intro n hn
  obtain ⟨hle, hpp, hmin⟩ := mem_firstTwentyFibers.1 hn
  exact mem_first50Fibers.2 ⟨hle, hpp, first20Primes_subset_first50Primes hmin⟩

/-- Sums over the union split into the fifty fiber sums. -/
theorem sum_first50Fibers (N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ first50Fibers N, f n = ∑ p ∈ first50Primes, ∑ n ∈ primePowerFiber p N, f n := by
  refine Finset.sum_biUnion ?_
  intro p hp q hq hpq
  exact disjoint_primePowerFiber (prime_of_mem_first50Primes hp)
    (prime_of_mem_first50Primes hq) hpq

/-- The size of the union, as a sum of `Nat.log p N` over the fifty primes. -/
theorem card_first50Fibers {N : ℕ} (hN : N ≠ 0) :
    (first50Fibers N).card = ∑ p ∈ first50Primes, Nat.log p N := by
  rw [first50Fibers, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun p hp =>
      card_primePowerFiber (prime_of_mem_first50Primes hp).one_lt hN
  · intro p hp q hq hpq
    exact disjoint_primePowerFiber (prime_of_mem_first50Primes hp)
      (prime_of_mem_first50Primes hq) hpq

/-- In the range `1, …, 256` the wider picture colours `66` cells, against the `36` of the
twenty-prime picture. -/
theorem card_first50Fibers_256 : (first50Fibers 256).card = 66 := by
  rw [card_first50Fibers (by norm_num)]
  decide

/-- In the range `1, …, 1024` — the range of the new picture — the fifty fibers cover
exactly `76` numbers. -/
theorem card_first50Fibers_1024 : (first50Fibers 1024).card = 76 := by
  rw [card_first50Fibers (by norm_num)]
  decide

/-- The twenty-prime picture covers only `46` of the numbers `1, …, 1024`, so the extra
thirty primes contribute `30` new cells. -/
theorem card_firstTwentyFibers_1024 : (firstTwentyFibers 1024).card = 46 := by
  rw [card_firstTwentyFibers (by norm_num)]
  decide

/-- The fiber of `2` in the new range has ten points, `2^1, …, 2^10`. -/
theorem card_primePowerFiber_two_1024 : (primePowerFiber 2 1024).card = 10 := by
  rw [card_primePowerFiber (by norm_num) (by norm_num)]
  decide

/-- Faithfulness of the wider picture: within the displayed range, a cell is coloured
exactly when the number belongs to the union of the fifty fibers. -/
theorem extCellColor_ne_neutral_iff_mem_first50Fibers {N n : ℕ} (hn : n ≤ N) :
    extCellColor n ≠ neutralColor ↔ n ∈ first50Fibers N := by
  rw [extCellColor_ne_neutral_iff, first50Fibers, Finset.mem_biUnion]
  constructor
  · rintro ⟨hpow, hmem⟩
    exact ⟨n.minFac, hmem,
      (mem_primePowerFiber_iff_isPosPowOf
        (prime_of_mem_first50Primes hmem).one_lt).2 ⟨hpow, hn⟩⟩
  · rintro ⟨p, hp, hnp⟩
    have hpp := prime_of_mem_first50Primes hp
    have h : isPosPowOf p n = true :=
      ((mem_primePowerFiber_iff_isPosPowOf hpp.one_lt).1 hnp).1
    have hmin : n.minFac = p := minFac_of_isPosPowOf hpp h
    exact ⟨by rw [hmin]; exact h, by rw [hmin]; exact hp⟩

/-- The coloured cells of the wider picture of `1, …, N` are exactly the union of the fifty
fibers. -/
theorem filter_colored_eq_first50Fibers (N : ℕ) :
    (Finset.Icc 1 N).filter (fun n => extCellColor n ≠ neutralColor) = first50Fibers N := by
  ext n
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨-, hle⟩, h⟩
    exact (extCellColor_ne_neutral_iff_mem_first50Fibers hle).1 h
  · intro h
    obtain ⟨p, -, hnp⟩ := Finset.mem_biUnion.1 h
    obtain ⟨hpos, hle⟩ := (mem_primePowerFiber.1 hnp).1
    exact ⟨⟨hpos, hle⟩, (extCellColor_ne_neutral_iff_mem_first50Fibers hle).2 h⟩

/-- Wherever the old picture was coloured, the wider one paints the same colour. -/
theorem extCellColor_eq_cellColor {n : ℕ} (h : cellColor n ≠ neutralColor) :
    extCellColor n = cellColor n := by
  obtain ⟨hpow, hmem⟩ := cellColor_ne_neutral_iff.1 h
  rw [extCellColor, if_pos hpow, cellColor, if_pos hpow,
    extFiberColor_eq_fiberColor _ hmem]

/-- The wider picture is still red exactly on the fiber of `2`. -/
theorem extCellColor_eq_red_iff {n : ℕ} :
    extCellColor n = redColor ↔ ∃ k, 0 < k ∧ n = 2 ^ k := by
  constructor
  · intro h
    have hne : extCellColor n ≠ neutralColor := by rw [h]; decide
    obtain ⟨hpow, hmem⟩ := extCellColor_ne_neutral_iff.1 hne
    rw [extCellColor, if_pos hpow] at h
    have hmin : n.minFac = 2 :=
      extFiberColor_injOn _ hmem 2 (by decide) (by rw [h]; decide)
    rw [hmin] at hpow
    exact (isPosPowOf_iff (by norm_num)).1 hpow
  · rintro ⟨k, hk, rfl⟩
    have hpow : isPosPowOf 2 (2 ^ k) = true :=
      (isPosPowOf_iff (by norm_num)).2 ⟨k, hk, rfl⟩
    have hmin : (2 ^ k).minFac = 2 := minFac_of_isPosPowOf Nat.prime_two hpow
    rw [extCellColor, hmin, if_pos hpow]
    decide

/-! ## Von Mangoldt weight of the wider picture -/

open scoped ArithmeticFunction in
/-- The total von Mangoldt weight of the fifty fibers. -/
theorem sum_vonMangoldt_first50Fibers {N : ℕ} (hN : N ≠ 0) :
    ∑ n ∈ first50Fibers N, Λ n = ∑ p ∈ first50Primes, (Nat.log p N : ℝ) * Real.log p := by
  rw [sum_first50Fibers]
  exact Finset.sum_congr rfl fun p hp =>
    sum_vonMangoldt_primePowerFiber (prime_of_mem_first50Primes hp) hN

open scoped ArithmeticFunction in
/-- The Chebyshev-type aggregate bound over the fifty fibers. -/
theorem sum_vonMangoldt_sq_div_first50Fibers (N : ℕ) :
    ∑ n ∈ first50Fibers N, (Λ n) ^ 2 / n ≤ ∑ p ∈ first50Primes, (Real.log p) ^ 2 := by
  rw [sum_first50Fibers]
  exact Finset.sum_le_sum fun p hp =>
    sum_vonMangoldt_sq_div_primePowerFiber (prime_of_mem_first50Primes hp)

open scoped ArithmeticFunction in
/-- A crude numerical form of the aggregate bound over the fifty fibers. -/
theorem sum_vonMangoldt_sq_div_first50Fibers_le (N : ℕ) :
    ∑ n ∈ first50Fibers N, (Λ n) ^ 2 / n ≤ 50 * (Real.log 229) ^ 2 := by
  refine (sum_vonMangoldt_sq_div_first50Fibers N).trans ?_
  have hbound : ∀ p ∈ first50Primes, (Real.log p) ^ 2 ≤ (Real.log 229) ^ 2 := by
    intro p hp
    have hple : (p : ℝ) ≤ 229 := by exact_mod_cast le_of_mem_first50Primes hp
    have h0 : (0:ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
    have hmono : Real.log p ≤ Real.log 229 := by
      rcases eq_or_lt_of_le hple with h | h
      · rw [h]
      · exact le_of_lt (Real.log_lt_log
          (by exact_mod_cast (prime_of_mem_first50Primes hp).pos) h)
    nlinarith
  calc ∑ p ∈ first50Primes, (Real.log p) ^ 2
      ≤ ∑ _p ∈ first50Primes, (Real.log 229) ^ 2 := Finset.sum_le_sum hbound
    _ = 50 * (Real.log 229) ^ 2 := by
        rw [Finset.sum_const, card_first50Primes, nsmul_eq_mul]
        norm_num

end PrimeFibers

/-! ## The zeta side: fifty Euler factors -/

namespace Sporadic

open Finset PrimeFibers

variable {s : ℝ}

/-- The Euler product of `ζ` truncated to the first fifty primes,
`∏_{p ≤ 229} (1 - p^{-s})⁻¹`. -/
noncomputable def extendedEulerProduct (s : ℝ) : ℝ :=
  ∏ p ∈ first50Primes, eulerFactor p s

/-- Fifty Euler factors still stay below `ζ(s)`. -/
theorem extendedEulerProduct_le_zeta (hs : 1 < s) : extendedEulerProduct s ≤ zetaR s :=
  prod_eulerFactor_le_zeta hs first50Primes (fun _ hp => prime_of_mem_first50Primes hp)

/-- A product of real numbers that are all at least `1` is at least `1`. -/
theorem one_le_prod_of_one_le (t : Finset ℕ) (f : ℕ → ℝ) (h : ∀ i ∈ t, 1 ≤ f i) :
    1 ≤ ∏ i ∈ t, f i := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.prod_insert ha]
      have h1 : 1 ≤ f a := h a (by simp)
      have h2 : 1 ≤ ∏ i ∈ t, f i := ih (fun i hi => h i (by simp [hi]))
      nlinarith

/-- Adding primes only increases the product: the Monster's fifteen Euler factors are part
of the fifty. -/
theorem monsterEulerProduct_le_extendedEulerProduct (hs : 0 < s) :
    monsterEulerProduct s ≤ extendedEulerProduct s := by
  classical
  have hsplit : (∏ p ∈ first50Primes \ monsterPrimes, eulerFactor p s) *
      (∏ p ∈ monsterPrimes, eulerFactor p s) = ∏ p ∈ first50Primes, eulerFactor p s :=
    Finset.prod_sdiff monsterPrimes_subset_first50Primes
  have h1 : 1 ≤ ∏ p ∈ first50Primes \ monsterPrimes, eulerFactor p s :=
    one_le_prod_of_one_le _ _ fun p hp =>
      one_le_eulerFactor
        (prime_of_mem_first50Primes (Finset.mem_sdiff.1 hp).1).two_le hs
  have h0 : 0 ≤ ∏ p ∈ monsterPrimes, eulerFactor p s :=
    Finset.prod_nonneg fun p hp =>
      (eulerFactor_pos (prime_of_mem_sporadicPrimes p (monsterPrimes_subset hp)).two_le hs).le
  rw [monsterEulerProduct, extendedEulerProduct, ← hsplit]
  nlinarith

/-- **The widened comparison.** For every real `s > 1`,
`∑_{d ∣ |M|} d^{-s} ≤ ∏_{p ∣ |M|} (1-p^{-s})⁻¹ ≤ ∏_{p ≤ 229} (1-p^{-s})⁻¹ ≤ ζ(s)`. -/
theorem monsterDivisorSum_le_extendedEulerProduct (hs : 1 < s) :
    monsterDivisorSum s ≤ extendedEulerProduct s :=
  le_trans (monsterDivisorSum_le_monsterEulerProduct (by linarith))
    (monsterEulerProduct_le_extendedEulerProduct (by linarith))

/-- At `s = 2` the fifty-factor Euler product is still below `π²/6`. -/
theorem extendedEulerProduct_two_le : extendedEulerProduct 2 ≤ Real.pi ^ 2 / 6 := by
  rw [← zetaR_two]
  exact extendedEulerProduct_le_zeta (by norm_num)

end Sporadic
