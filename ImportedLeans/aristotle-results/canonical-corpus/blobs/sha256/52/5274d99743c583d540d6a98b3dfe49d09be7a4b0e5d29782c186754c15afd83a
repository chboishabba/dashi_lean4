/-
# Prime-power fibers over the first twenty primes

This file isolates and develops the "prime-power fiber" construction that appears in the
prime side of the Zeta23 formalization (see `reference/zeta23`, e.g. the fiber decomposition
`U p = {n ≤ x : n = p ^ k, k ≥ 1}` used in `Zeta23/ThmE/ChebCoprime.lean`), and specializes
it to the first twenty primes `2, 3, …, 71`.

The main results are:

* `PrimeFibers.first20Primes` is exactly the set of primes `≤ 71`, and has cardinality `20`;
* the fibers `primePowerFiber p N` are pairwise disjoint for distinct primes;
* each fiber is the image of the exponent range `Icc 1 (Nat.log p N)`, hence has
  cardinality `Nat.log p N`;
* any sum over the union of the fibers splits as a sum of the fiber sums;
* the von Mangoldt function is constant `Real.log p` on the fiber of `p`, so the fiber sum
  of `Λ` is `Nat.log p N * Real.log p`;
* the Chebyshev-type weighted fiber bound `∑ Λ(n)² / n ≤ (log p)²`, and its aggregate form
  over the first twenty primes.
-/
import Mathlib

open Finset
open scoped BigOperators ArithmeticFunction

namespace PrimeFibers

/-! ## The first twenty primes -/

/-- The first twenty prime numbers, `2, 3, 5, …, 71`. -/
def first20Primes : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71}

/-- There are twenty of them. -/
theorem card_first20Primes : first20Primes.card = 20 := by decide

/-- `first20Primes` is precisely the set of primes below `72`, i.e. it really is an initial
segment of the primes. -/
theorem first20Primes_eq_filter :
    first20Primes = (Finset.range 72).filter Nat.Prime := by decide

theorem mem_first20Primes_iff {p : ℕ} : p ∈ first20Primes ↔ p.Prime ∧ p ≤ 71 := by
  rw [first20Primes_eq_filter]
  simp [Finset.mem_filter, Nat.lt_succ_iff]
  tauto

theorem prime_of_mem_first20Primes {p : ℕ} (hp : p ∈ first20Primes) : p.Prime :=
  (mem_first20Primes_iff.1 hp).1

theorem le_of_mem_first20Primes {p : ℕ} (hp : p ∈ first20Primes) : p ≤ 71 :=
  (mem_first20Primes_iff.1 hp).2

/-! ## Prime-power fibers -/

open scoped Classical in
/-- The prime-power fiber of `p` inside `(0, N]`: the set of `p ^ k` with `k ≥ 1` and
`p ^ k ≤ N`. -/
noncomputable def primePowerFiber (p N : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter (fun n => ∃ k, 0 < k ∧ n = p ^ k)

theorem mem_primePowerFiber {p N n : ℕ} :
    n ∈ primePowerFiber p N ↔ (0 < n ∧ n ≤ N) ∧ ∃ k, 0 < k ∧ n = p ^ k := by
  classical
  simp [primePowerFiber, Finset.mem_filter, Finset.mem_Ioc, and_assoc]

theorem primePowerFiber_subset (p N : ℕ) : primePowerFiber p N ⊆ Finset.Ioc 0 N :=
  fun _ hn => Finset.mem_Ioc.2 (mem_primePowerFiber.1 hn).1

/-- Fibers over distinct primes are disjoint. -/
theorem disjoint_primePowerFiber {p q N : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Disjoint (primePowerFiber p N) (primePowerFiber q N) := by
  rw [Finset.disjoint_left]
  intro n hn₁ hn₂
  obtain ⟨-, k₁, hk₁, rfl⟩ := mem_primePowerFiber.1 hn₁
  obtain ⟨-, k₂, hk₂, he⟩ := mem_primePowerFiber.1 hn₂
  exact hpq (((Nat.prime_dvd_prime_iff_eq hq hp).1
    (hq.dvd_of_dvd_pow (he ▸ dvd_pow_self q hk₂.ne'))).symm)

/-- The fiber of `p` is the image of the exponent range `Icc 1 (Nat.log p N)`. -/
theorem primePowerFiber_eq_image {p N : ℕ} (hp : 1 < p) (hN : N ≠ 0) :
    primePowerFiber p N = (Finset.Icc 1 (Nat.log p N)).image (fun k => p ^ k) := by
  ext n
  simp only [mem_primePowerFiber, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨-, hle⟩, k, hk, rfl⟩
    exact ⟨k, ⟨hk, (Nat.le_log_iff_pow_le hp hN).2 hle⟩, rfl⟩
  · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
    exact ⟨⟨Nat.pow_pos (by omega), (Nat.le_log_iff_pow_le hp hN).1 hk2⟩, k, hk1, rfl⟩

/-- The fiber of `p` in `(0, N]` has exactly `Nat.log p N` elements. -/
theorem card_primePowerFiber {p N : ℕ} (hp : 1 < p) (hN : N ≠ 0) :
    (primePowerFiber p N).card = Nat.log p N := by
  rw [primePowerFiber_eq_image hp hN,
    Finset.card_image_of_injective _ (Nat.pow_right_injective hp), Nat.card_Icc]
  omega

/-! ## The union of the fibers over the first twenty primes -/

/-- All `n ≤ N` that are powers of one of the first twenty primes. -/
noncomputable def firstTwentyFibers (N : ℕ) : Finset ℕ :=
  first20Primes.biUnion (fun p => primePowerFiber p N)

/-- Membership in the union: `n` is a prime power `≤ N` whose prime is one of the first
twenty primes. -/
theorem mem_firstTwentyFibers {N n : ℕ} :
    n ∈ firstTwentyFibers N ↔ n ≤ N ∧ IsPrimePow n ∧ n.minFac ∈ first20Primes := by
  constructor
  · intro hn
    rw [firstTwentyFibers, Finset.mem_biUnion] at hn
    obtain ⟨p, hp, hnp⟩ := hn
    obtain ⟨⟨-, hle⟩, k, hk, rfl⟩ := mem_primePowerFiber.1 hnp
    have hpp := prime_of_mem_first20Primes hp
    refine ⟨hle, ⟨p, k, hpp.prime, hk, rfl⟩, ?_⟩
    rwa [Nat.Prime.pow_minFac hpp hk.ne']
  · rintro ⟨hle, hpp, hmin⟩
    have hn0 : 0 < n := hpp.pos
    rw [firstTwentyFibers, Finset.mem_biUnion]
    refine ⟨n.minFac, hmin, mem_primePowerFiber.2 ⟨⟨hn0, hle⟩, ?_⟩⟩
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    have hpn : p.Prime := hp.nat_prime
    exact ⟨k, hk, by rw [Nat.Prime.pow_minFac hpn hk.ne']⟩

/-- Sums over the union split into the fiber sums. -/
theorem sum_firstTwentyFibers (N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ firstTwentyFibers N, f n
      = ∑ p ∈ first20Primes, ∑ n ∈ primePowerFiber p N, f n := by
  refine Finset.sum_biUnion ?_
  intro p hp q hq hpq
  exact disjoint_primePowerFiber (prime_of_mem_first20Primes hp)
    (prime_of_mem_first20Primes hq) hpq

/-- The number of elements of the union, as a sum of `Nat.log p N` over the first twenty
primes. -/
theorem card_firstTwentyFibers {N : ℕ} (hN : N ≠ 0) :
    (firstTwentyFibers N).card = ∑ p ∈ first20Primes, Nat.log p N := by
  rw [firstTwentyFibers, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun p hp =>
      card_primePowerFiber (prime_of_mem_first20Primes hp).one_lt hN
  · intro p hp q hq hpq
    exact disjoint_primePowerFiber (prime_of_mem_first20Primes hp)
      (prime_of_mem_first20Primes hq) hpq

/-! ## Von Mangoldt weights on a fiber -/

/-- `Λ` is constant, equal to `log p`, on the fiber of a prime `p`. -/
theorem vonMangoldt_of_mem_primePowerFiber {p N n : ℕ} (hp : p.Prime)
    (hn : n ∈ primePowerFiber p N) : Λ n = Real.log p := by
  obtain ⟨-, k, hk, rfl⟩ := mem_primePowerFiber.1 hn
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- The fiber sum of the von Mangoldt function. -/
theorem sum_vonMangoldt_primePowerFiber {p N : ℕ} (hp : p.Prime) (hN : N ≠ 0) :
    ∑ n ∈ primePowerFiber p N, Λ n = (Nat.log p N : ℝ) * Real.log p := by
  rw [Finset.sum_congr rfl (fun n hn => vonMangoldt_of_mem_primePowerFiber hp hn),
    Finset.sum_const, card_primePowerFiber hp.one_lt hN, nsmul_eq_mul]

/-- A geometric tail bound: for `0 ≤ r ≤ 1/2` one has `∑_{k=1}^{L} r^k ≤ 1 - r^L ≤ 1`. -/
theorem geom_tail_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (L : ℕ) :
    ∑ k ∈ Finset.Icc 1 L, r ^ k ≤ 1 - r ^ L := by
  induction L with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hpow : (0:ℝ) ≤ r ^ n := pow_nonneg hr0 n
      have : r ^ (n + 1) = r ^ n * r := by ring
      nlinarith [ih]

/-- The Chebyshev-type weighted fiber bound: `∑_{n ∈ fiber p} Λ(n)²/n ≤ (log p)²`. -/
theorem sum_vonMangoldt_sq_div_primePowerFiber {p N : ℕ} (hp : p.Prime) :
    ∑ n ∈ primePowerFiber p N, (Λ n) ^ 2 / n ≤ (Real.log p) ^ 2 := by
  have hlog : (0:ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · have : primePowerFiber p 0 = ∅ := by
      ext n
      simp [mem_primePowerFiber]
      omega
    rw [this, Finset.sum_empty]
    positivity
  have hN : N ≠ 0 := hNpos.ne'
  have hp1 : 1 < p := hp.one_lt
  have hpR : (1:ℝ) < (p : ℝ) := by exact_mod_cast hp1
  rw [primePowerFiber_eq_image hp1 hN,
    Finset.sum_image (fun a _ b _ h => Nat.pow_right_injective hp1 h)]
  have hterm : ∀ k ∈ Finset.Icc 1 (Nat.log p N),
      (Λ (p ^ k)) ^ 2 / ((p : ℝ) ^ k) = (Real.log p) ^ 2 * ((1 / (p:ℝ)) ^ k) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    rw [div_pow, one_pow]
    ring
  calc ∑ k ∈ Finset.Icc 1 (Nat.log p N), (Λ (p ^ k)) ^ 2 / ((p ^ k : ℕ) : ℝ)
      = ∑ k ∈ Finset.Icc 1 (Nat.log p N), (Real.log p) ^ 2 * ((1 / (p:ℝ)) ^ k) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Nat.cast_pow]
        exact hterm k hk
    _ = (Real.log p) ^ 2 * ∑ k ∈ Finset.Icc 1 (Nat.log p N), ((1 / (p:ℝ)) ^ k) := by
        rw [Finset.mul_sum]
    _ ≤ (Real.log p) ^ 2 * 1 := by
        have hr0 : (0:ℝ) ≤ 1 / (p:ℝ) := by positivity
        have hr : (1:ℝ) / (p:ℝ) ≤ 1 / 2 := by
          have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
          exact one_div_le_one_div_of_le (by norm_num) this
        have := geom_tail_le hr0 hr (Nat.log p N)
        have hpow : (0:ℝ) ≤ (1 / (p:ℝ)) ^ (Nat.log p N) := by positivity
        nlinarith [sq_nonneg (Real.log p)]
    _ = (Real.log p) ^ 2 := by ring

/-- Aggregate bound over the first twenty primes. -/
theorem sum_vonMangoldt_sq_div_firstTwentyFibers (N : ℕ) :
    ∑ n ∈ firstTwentyFibers N, (Λ n) ^ 2 / n ≤ ∑ p ∈ first20Primes, (Real.log p) ^ 2 := by
  rw [sum_firstTwentyFibers]
  exact Finset.sum_le_sum fun p hp =>
    sum_vonMangoldt_sq_div_primePowerFiber (prime_of_mem_first20Primes hp)

/-- A crude numerical form of the aggregate bound. -/
theorem sum_vonMangoldt_sq_div_firstTwentyFibers_le (N : ℕ) :
    ∑ n ∈ firstTwentyFibers N, (Λ n) ^ 2 / n ≤ 20 * (Real.log 71) ^ 2 := by
  refine (sum_vonMangoldt_sq_div_firstTwentyFibers N).trans ?_
  have hbound : ∀ p ∈ first20Primes, (Real.log p) ^ 2 ≤ (Real.log 71) ^ 2 := by
    intro p hp
    have hple : (p : ℝ) ≤ 71 := by exact_mod_cast le_of_mem_first20Primes hp
    have h0 : (0:ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
    have hmono : Real.log p ≤ Real.log 71 := by
      rcases eq_or_lt_of_le hple with h | h
      · rw [h]
      · exact le_of_lt (Real.log_lt_log (by
          exact_mod_cast (prime_of_mem_first20Primes hp).pos) h)
    nlinarith
  calc ∑ p ∈ first20Primes, (Real.log p) ^ 2
      ≤ ∑ _p ∈ first20Primes, (Real.log 71) ^ 2 := Finset.sum_le_sum hbound
    _ = 20 * (Real.log 71) ^ 2 := by
        rw [Finset.sum_const, card_first20Primes, nsmul_eq_mul]
        norm_num

/-- The total von Mangoldt weight of the union of the fibers. -/
theorem sum_vonMangoldt_firstTwentyFibers {N : ℕ} (hN : N ≠ 0) :
    ∑ n ∈ firstTwentyFibers N, Λ n
      = ∑ p ∈ first20Primes, (Nat.log p N : ℝ) * Real.log p := by
  rw [sum_firstTwentyFibers]
  exact Finset.sum_congr rfl fun p hp =>
    sum_vonMangoldt_primePowerFiber (prime_of_mem_first20Primes hp) hN

/-- A concrete instance: there are exactly `30` numbers `≤ 100` that are powers of one of the
first twenty primes. -/
theorem card_firstTwentyFibers_hundred : (firstTwentyFibers 100).card = 30 := by
  rw [card_firstTwentyFibers (by norm_num)]
  decide

end PrimeFibers
