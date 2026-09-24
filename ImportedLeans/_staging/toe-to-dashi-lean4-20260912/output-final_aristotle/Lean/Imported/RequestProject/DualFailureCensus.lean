import RequestProject.TwistSeries
import RequestProject.MultiplicativeRepairIff

/-!
# Dual failures: where *both* dials are dead, and how many there are

`GF(q)`, `q = pᵏ`, has two canonical maps onto its prime subfield `𝔽ₚ`, both built from the
Frobenius orbit of a point: the orbit product `N(x) = x·x^p⋯x^(p^(k-1))` and the orbit sum
`Tr(x) = x + x^p + ⋯ + x^(p^(k-1))`.  Restricted to `𝔽ₚ` they degenerate to the degree `k`:
`N(a) = a^k`, `Tr(a) = k·a`.  So

* the **additive dial** dies exactly when `p ∣ k` (then `Tr` annihilates `𝔽ₚ` and no rescaling
  `c·Tr` repairs it — `FrobeniusPrimeSubfield.scalar_repair_iff_not_dvd`), and
* the **multiplicative dial** — the orbit product itself — fails exactly when
  `¬ (p - 1) ∣ (k - 1)`, i.e. when the error count `frobDefect p k` is nonzero
  (`FieldSizeScan.frobDefect_eq_zero_iff`).

A size where both happen is a **dual failure**.  The census in `RequestProject/TwistSeries.lean`
found exactly one below `1825`, namely `729 = 3⁶`.  This file explains and extends that:

* `isDualFailure_iff` — the classification: a dual failure is precisely an **odd** prime `p`
  together with `k = m·p` where `m ≢ 1 (mod p - 1)`.  In particular characteristic `2` never
  produces one (`not_isDualFailure_two`), and `k = p` never does (`not_isDualFailure_self`).
* `isDualFailure_two_mul` and `min_size` — for each odd prime `p` the smallest dual failure is
  `k = 2p`, i.e. `q = p^(2p)`, and over *all* finite fields the smallest dual failure size is
  `729 = 3⁶`.
* `card_dualExponents` — the exact count for a fixed odd prime `p` and bound `M`:
  with `mmax p M` the largest `m` with `p^(m·p) ≤ M`,
  `#{k : dual failure, p^k ≤ M} = mmax - (mmax - 1)/(p - 1) - 1`.
* Complete censuses at `10³`, `10⁶`, `10⁹` and `10¹²` (`census_1e3` … `census_1e12`), listing
  every dual-failure pair `(p, k)` and every dual-failure size below the bound.  The counts are
  `1, 2, 4, 7`.  (Note the last one: below `10¹²` there are **seven**, not six — `5¹⁵ =
  30517578125` is a dual failure, since `15 ≡ 3 (mod 4)`.)
-/

namespace DualDial

open Finset

/-! ## The predicate and its classification -/

/-- **A dual failure**: a prime power `pᵏ` (`k ≥ 1`) whose additive dial is dead (`p ∣ k`, so
the Frobenius orbit sum annihilates the prime subfield) *and* whose multiplicative dial is dead
(`¬ (p-1) ∣ (k-1)`, so the Frobenius orbit product moves a point of the prime subfield).  For
such a size neither canonical map can be repaired by rescaling; only the twist
`R(x) = Tr(c·x)` remains. -/
def IsDualFailure (p k : ℕ) : Prop :=
  p.Prime ∧ 1 ≤ k ∧ p ∣ k ∧ ¬ (p - 1) ∣ (k - 1)

instance (p k : ℕ) : Decidable (IsDualFailure p k) := by
  unfold IsDualFailure; infer_instance

/-- The multiplicative half of the definition is exactly a nonzero Frobenius error count. -/
theorem isDualFailure_iff_frobDefect {p k : ℕ} (hp : p.Prime) :
    IsDualFailure p k ↔ (1 ≤ k ∧ p ∣ k ∧ FieldSizeScan.frobDefect p k ≠ 0) := by
  rw [Ne, FieldSizeScan.frobDefect_eq_zero_iff hp]
  exact ⟨fun h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨hp, h.1, h.2.1, h.2.2⟩⟩

/-- The arithmetic heart: writing `k = m·p`, we have `k - 1 = m·(p-1) + (m-1)`, so the
multiplicative criterion `(p-1) ∣ (k-1)` is the congruence `m ≡ 1 (mod p - 1)`. -/
theorem dvd_mul_sub_one_iff {p m : ℕ} (hp : 1 ≤ p) (hm : 1 ≤ m) :
    (p - 1) ∣ (m * p - 1) ↔ (p - 1) ∣ (m - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, p = d + 1 := ⟨p - 1, by omega⟩
  have hms : m * (d + 1) = m * d + m := Nat.mul_succ m d
  have h : m * (d + 1) - 1 = m * d + (m - 1) := by omega
  simp only [Nat.add_sub_cancel, h]
  exact Nat.dvd_add_right (dvd_mul_left d m)

/-- **Classification of dual failures.**  `pᵏ` is a dual failure iff `p` is an *odd* prime and
`k = m·p` with `m` not congruent to `1` modulo `p - 1`.  Thus `(p - 2)` out of every `(p - 1)`
multiples of `p` give a dual failure. -/
theorem isDualFailure_iff {p k : ℕ} :
    IsDualFailure p k ↔
      p.Prime ∧ p ≠ 2 ∧ ∃ m, 1 ≤ m ∧ k = m * p ∧ ¬ (p - 1) ∣ (m - 1) := by
  constructor
  · rintro ⟨hp, hk1, ⟨m, rfl⟩, hnd⟩
    have hp1 : 1 ≤ p := hp.one_lt.le.trans' (by omega)
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp at hk1
      · exact h
    have hcomm : p * m = m * p := Nat.mul_comm p m
    refine ⟨hp, ?_, m, hm, hcomm, ?_⟩
    · rintro rfl
      exact hnd (by simp)
    · rw [hcomm] at hnd
      exact fun hd => hnd ((dvd_mul_sub_one_iff hp1 hm).2 hd)
  · rintro ⟨hp, -, m, hm, rfl, hnd⟩
    have hp1 : 1 ≤ p := hp.one_lt.le.trans' (by omega)
    refine ⟨hp, Nat.one_le_iff_ne_zero.2 (by positivity), Dvd.intro_left m rfl, ?_⟩
    exact fun hd => hnd ((dvd_mul_sub_one_iff hp1 hm).1 hd)

/-- **Characteristic `2` never fails twice.**  Since `p - 1 = 1` divides everything, the orbit
product of a field of characteristic `2` is always a retraction; the dead additive dials
`4, 16, 64, 256, 1024` of the census are all repaired multiplicatively. -/
theorem not_isDualFailure_two (k : ℕ) : ¬ IsDualFailure 2 k := by
  rintro ⟨-, -, -, hnd⟩
  exact hnd (by simp)

/-- **`k = p` never fails twice**: `k - 1 = p - 1`, so the orbit product is a retraction.  This
is why `27 = 3³` and `3125 = 5⁵`, dead additive dials both, are not dual failures. -/
theorem not_isDualFailure_self (p : ℕ) : ¬ IsDualFailure p p := by
  rintro ⟨-, -, -, hnd⟩
  exact hnd dvd_rfl

/-- **The minimal dual failure of each odd characteristic**: `k = 2p`, i.e. `q = p^(2p)`. -/
theorem isDualFailure_two_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsDualFailure p (2 * p) := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  refine isDualFailure_iff.2 ⟨hp, hp2, 2, by norm_num, by ring, ?_⟩
  intro hd
  have := Nat.le_of_dvd (by norm_num) hd
  omega

/-! ## Size bounds: the smallest dual failure is `729` -/

theorem three_le_of_isDualFailure {p k : ℕ} (h : IsDualFailure p k) : 3 ≤ p := by
  obtain ⟨hp, hp2, -⟩ := isDualFailure_iff.1 h
  have := hp.two_le
  omega

theorem two_mul_le_of_isDualFailure {p k : ℕ} (h : IsDualFailure p k) : 2 * p ≤ k := by
  obtain ⟨hp, -, m, hm, rfl, hnd⟩ := isDualFailure_iff.1 h
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · interval_cases m
      · simp at hnd
    · exact h2
  exact Nat.mul_le_mul_right p hm2

/-- **The smallest dual-failure field size is `729 = 3⁶`.** -/
theorem min_size {p k : ℕ} (h : IsDualFailure p k) : 729 ≤ p ^ k := by
  have h3 : 3 ≤ p := three_le_of_isDualFailure h
  have hk : 6 ≤ k := by have := two_mul_le_of_isDualFailure h; omega
  calc (729 : ℕ) = 3 ^ 6 := by norm_num
    _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    _ ≤ p ^ k := Nat.pow_le_pow_left h3 k

/-- `729 = 3⁶` really is a dual failure, so the bound `min_size` is attained. -/
theorem isDualFailure_three_six : IsDualFailure 3 6 := by decide

/-! ## Complete censuses below a bound -/

theorem exponent_lt {p k K M : ℕ} (h : IsDualFailure p k) (hM : p ^ k ≤ M) (hK : M < 3 ^ K) :
    k < K := by
  have h1 : (3 : ℕ) ^ k ≤ p ^ k := Nat.pow_le_pow_left (three_le_of_isDualFailure h) k
  have h2 : (3 : ℕ) ^ k < 3 ^ K := lt_of_le_of_lt (h1.trans hM) hK
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h2

theorem char_lt {p k K P M : ℕ} (h : IsDualFailure p k) (hM : p ^ k ≤ M) (hK : M < 3 ^ K)
    (hPK : K ≤ 2 * P) : p < P := by
  have h1 := exponent_lt h hM hK
  have h2 := two_mul_le_of_isDualFailure h
  omega

/-- **The census machine.**  If `M < 3^K` and `K ≤ 2P`, then a finite check over
`p < P`, `k < K` decides the dual failures of size at most `M`. -/
theorem census_of_check {M K P : ℕ} {L : List (ℕ × ℕ)} (hK : M < 3 ^ K) (hPK : K ≤ 2 * P)
    (hL : ∀ p ∈ List.range P, ∀ k ∈ List.range K,
      ((IsDualFailure p k ∧ p ^ k ≤ M) ↔ (p, k) ∈ L))
    (hsound : ∀ pk ∈ L, IsDualFailure pk.1 pk.2 ∧ pk.1 ^ pk.2 ≤ M) (p k : ℕ) :
    (IsDualFailure p k ∧ p ^ k ≤ M) ↔ (p, k) ∈ L := by
  constructor
  · rintro ⟨h, hM⟩
    exact (hL p (List.mem_range.2 (char_lt h hM hK hPK)) k
      (List.mem_range.2 (exponent_lt h hM hK))).1 ⟨h, hM⟩
  · intro hmem
    exact hsound (p, k) hmem

/-- **Every dual failure of size at most `10³`**: only `729 = 3⁶`. -/
theorem census_1e3 (p k : ℕ) :
    (IsDualFailure p k ∧ p ^ k ≤ 10 ^ 3) ↔ (p, k) ∈ [(3, 6)] :=
  census_of_check (K := 7) (P := 4) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) p k

/-- **Every dual failure of size at most `10⁶`**: `3⁶ = 729` and `3¹² = 531441`. -/
theorem census_1e6 (p k : ℕ) :
    (IsDualFailure p k ∧ p ^ k ≤ 10 ^ 6) ↔ (p, k) ∈ [(3, 6), (3, 12)] :=
  census_of_check (K := 13) (P := 7) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) p k

/-- **Every dual failure of size at most `10⁹`**: `3⁶, 3¹², 5¹⁰, 3¹⁸` — four of them. -/
theorem census_1e9 (p k : ℕ) :
    (IsDualFailure p k ∧ p ^ k ≤ 10 ^ 9) ↔ (p, k) ∈ [(3, 6), (3, 12), (3, 18), (5, 10)] :=
  census_of_check (K := 19) (P := 10) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) p k

/-- **Every dual failure of size at most `10¹²`**: `3⁶, 3¹², 3¹⁸, 3²⁴, 5¹⁰, 5¹⁵, 7¹⁴` — there
are **seven**, not six: `5¹⁵ = 30517578125` is a dual failure because `15 ≢ 1 (mod 4)`. -/
theorem census_1e12 (p k : ℕ) :
    (IsDualFailure p k ∧ p ^ k ≤ 10 ^ 12) ↔
      (p, k) ∈ [(3, 6), (3, 12), (3, 18), (3, 24), (5, 10), (5, 15), (7, 14)] :=
  census_of_check (K := 26) (P := 13) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) p k

/-- The dual-failure **sizes** below `10¹²`, in increasing order. -/
theorem census_sizes_1e12 (q : ℕ) :
    ((∃ p k, IsDualFailure p k ∧ p ^ k = q) ∧ q ≤ 10 ^ 12) ↔
      q ∈ [729, 531441, 9765625, 387420489, 30517578125, 282429536481, 678223072849] := by
  constructor
  · rintro ⟨⟨p, k, h, rfl⟩, hq⟩
    have := (census_1e12 p k).1 ⟨h, hq⟩
    fin_cases this <;> norm_num
  · intro hq
    fin_cases hq
    · exact ⟨⟨3, 6, isDualFailure_three_six, by norm_num⟩, by norm_num⟩
    · exact ⟨⟨3, 12, by decide, by norm_num⟩, by norm_num⟩
    · exact ⟨⟨5, 10, by decide, by norm_num⟩, by norm_num⟩
    · exact ⟨⟨3, 18, by decide, by norm_num⟩, by norm_num⟩
    · exact ⟨⟨5, 15, by decide, by norm_num⟩, by norm_num⟩
    · exact ⟨⟨3, 24, by decide, by norm_num⟩, by norm_num⟩
    · exact ⟨⟨7, 14, by decide, by norm_num⟩, by norm_num⟩

/-! ## The counting formula for a fixed odd characteristic -/
/-- Counting: among `m ∈ [1, N]`, exactly `(N-1)/d + 1` satisfy `m ≡ 1 (mod d)`. -/
theorem card_filter_dvd_sub_one (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N) :
    #{m ∈ Finset.Icc 1 N | d ∣ (m - 1)} = (N - 1) / d + 1 := by
  have hinj : Function.Injective (fun j : ℕ => 1 + j * d) := by
    intro a b hab
    simp only [add_right_inj] at hab
    exact Nat.eq_of_mul_eq_mul_right (by omega) hab
  have himg : {m ∈ Finset.Icc 1 N | d ∣ (m - 1)}
      = (Finset.range ((N - 1) / d + 1)).image (fun j => 1 + j * d) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨hm1, hmN⟩, j, hj⟩
      have hcomm : j * d = d * j := Nat.mul_comm j d
      have hjd : j * d ≤ N - 1 := by omega
      have hle : j ≤ (N - 1) / d := (Nat.le_div_iff_mul_le (by omega)).2 hjd
      exact ⟨j, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      have hjd : j * d ≤ N - 1 := by
        calc j * d ≤ ((N - 1) / d) * d := Nat.mul_le_mul_right d (Nat.lt_succ_iff.1 hj)
          _ ≤ N - 1 := Nat.div_mul_le_self _ _
      have hcomm : j * d = d * j := Nat.mul_comm j d
      exact ⟨⟨by omega, by omega⟩, ⟨j, by omega⟩⟩
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_range]

/-- Counting the complement: among `m ∈ [1, N]`, exactly `N - (N-1)/d - 1` satisfy
`m ≢ 1 (mod d)`. -/
theorem card_filter_not_dvd_sub_one (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N) :
    #{m ∈ Finset.Icc 1 N | ¬ d ∣ (m - 1)} = N - (N - 1) / d - 1 := by
  have htot : #{m ∈ Finset.Icc 1 N | d ∣ (m - 1)} + #{m ∈ Finset.Icc 1 N | ¬ d ∣ (m - 1)}
      = #(Finset.Icc 1 N) := Finset.card_filter_add_card_filter_not _
  rw [Nat.card_Icc] at htot
  rw [card_filter_dvd_sub_one d N hd hN] at htot
  omega

/-- `mmax p M` is the largest `m` with `p^(m·p) ≤ M`: the number of multiples of `p` available
as exponents below the bound. -/
def mmax (p M : ℕ) : ℕ := Nat.findGreatest (fun m => p ^ (m * p) ≤ M) M

theorem le_mmax_iff {p M m : ℕ} (hp : 2 ≤ p) (hM : 1 ≤ M) :
    p ^ (m * p) ≤ M ↔ m ≤ mmax p M := by
  have hbound : ∀ n : ℕ, p ^ (n * p) ≤ M → n ≤ M := by
    intro n hn
    calc n ≤ n * p := Nat.le_mul_of_pos_right n (by omega)
      _ ≤ p ^ (n * p) := Nat.le_of_lt (Nat.lt_pow_self hp)
      _ ≤ M := hn
  have hzero : p ^ (0 * p) ≤ M := by simpa using hM
  have hspec : p ^ (mmax p M * p) ≤ M := by
    have h := Nat.findGreatest_spec (P := fun m => p ^ (m * p) ≤ M) (m := 0) (Nat.zero_le M) hzero
    simpa [mmax] using h
  constructor
  · intro h
    have := Nat.le_findGreatest (P := fun m => p ^ (m * p) ≤ M) (hbound m h) h
    simpa [mmax] using this
  · intro h
    calc p ^ (m * p) ≤ p ^ (mmax p M * p) :=
          Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right p h)
      _ ≤ M := hspec

/-- **The counting formula.**  For an odd prime `p` and a bound `M`, the number of exponents `k`
for which `GF(p^k)` is a dual failure of size at most `M` is

`mmax - (mmax - 1)/(p - 1) - 1`,

where `mmax = mmax p M` is the largest `m` with `p^(m·p) ≤ M`.  (Equivalently: of the `mmax`
available multiples `k = m·p`, one discards those with `m ≡ 1 (mod p-1)`.) -/
theorem card_dualExponents {p M : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hM : 1 ≤ M) :
    #{k ∈ Finset.Icc 1 M | IsDualFailure p k ∧ p ^ k ≤ M}
      = mmax p M - (mmax p M - 1) / (p - 1) - 1 := by
  have hp2' : 2 ≤ p := hp.two_le
  have hpd : 1 ≤ p - 1 := by omega
  rcases Nat.eq_zero_or_pos (mmax p M) with h0 | hmm
  · have hempty : {k ∈ Finset.Icc 1 M | IsDualFailure p k ∧ p ^ k ≤ M} = ∅ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and]
      intro _ hdf
      obtain ⟨-, -, m, hm, rfl, -⟩ := isDualFailure_iff.1 hdf
      intro hk
      have := (le_mmax_iff (m := m) hp2' hM).1 hk
      omega
    rw [hempty]
    simp [h0]
  · have hbij : #{k ∈ Finset.Icc 1 M | IsDualFailure p k ∧ p ^ k ≤ M}
        = #{m ∈ Finset.Icc 1 (mmax p M) | ¬ (p - 1) ∣ (m - 1)} := by
      refine Finset.card_nbij' (fun k => k / p) (fun m => m * p) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
        obtain ⟨-, hdf, hkM⟩ := hk
        obtain ⟨-, -, m, hm, rfl, hnd⟩ := isDualFailure_iff.1 hdf
        have hdiv : m * p / p = m := Nat.mul_div_cancel _ (show 0 < p by omega)
        have hle := (le_mmax_iff (m := m) hp2' hM).1 hkM
        rw [hdiv]
        exact ⟨⟨hm, hle⟩, hnd⟩
      · intro m hm
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
        obtain ⟨⟨hm1, hmax⟩, hnd⟩ := hm
        have hpow : p ^ (m * p) ≤ M := (le_mmax_iff (m := m) hp2' hM).2 hmax
        have hmp : m * p ≤ M := le_trans (Nat.le_of_lt (Nat.lt_pow_self hp2')) hpow
        refine ⟨⟨?_, hmp⟩, isDualFailure_iff.2 ⟨hp, hp2, m, hm1, rfl, hnd⟩, hpow⟩
        have : 1 * 1 ≤ m * p := Nat.mul_le_mul hm1 (by omega)
        simpa using this
      · intro k hk
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hk
        obtain ⟨-, hdf, -⟩ := hk
        obtain ⟨-, -, m, hm, rfl, -⟩ := isDualFailure_iff.1 hdf
        show m * p / p * p = m * p
        rw [Nat.mul_div_cancel _ (show 0 < p by omega)]
      · intro m hm
        show m * p / p = m
        exact Nat.mul_div_cancel _ (show 0 < p by omega)
    rw [hbij, card_filter_not_dvd_sub_one (p - 1) (mmax p M) hpd hmm]

/-! ## The count at `10¹²`, prime by prime -/

theorem mmax_three_1e12 : mmax 3 (10 ^ 12) = 8 := by
  have h1 : 8 ≤ mmax 3 (10 ^ 12) :=
    (le_mmax_iff (p := 3) (m := 8) (by norm_num) (by norm_num)).1 (by norm_num)
  have h2 : ¬ 9 ≤ mmax 3 (10 ^ 12) := by
    intro h
    have := (le_mmax_iff (p := 3) (m := 9) (by norm_num) (by norm_num)).2 h
    norm_num at this
  omega

theorem mmax_five_1e12 : mmax 5 (10 ^ 12) = 3 := by
  have h1 : 3 ≤ mmax 5 (10 ^ 12) :=
    (le_mmax_iff (p := 5) (m := 3) (by norm_num) (by norm_num)).1 (by norm_num)
  have h2 : ¬ 4 ≤ mmax 5 (10 ^ 12) := by
    intro h
    have := (le_mmax_iff (p := 5) (m := 4) (by norm_num) (by norm_num)).2 h
    norm_num at this
  omega

theorem mmax_seven_1e12 : mmax 7 (10 ^ 12) = 2 := by
  have h1 : 2 ≤ mmax 7 (10 ^ 12) :=
    (le_mmax_iff (p := 7) (m := 2) (by norm_num) (by norm_num)).1 (by norm_num)
  have h2 : ¬ 3 ≤ mmax 7 (10 ^ 12) := by
    intro h
    have := (le_mmax_iff (p := 7) (m := 3) (by norm_num) (by norm_num)).2 h
    norm_num at this
  omega

/-- The formula, applied in characteristic `3` at `M = 10¹²`: `8 - 7/2 - 1 = 4` dual failures,
namely `3⁶, 3¹², 3¹⁸, 3²⁴`. -/
theorem card_dualExponents_three_1e12 :
    #{k ∈ Finset.Icc 1 (10 ^ 12) | IsDualFailure 3 k ∧ 3 ^ k ≤ 10 ^ 12} = 4 := by
  rw [card_dualExponents (by norm_num) (by norm_num) (by norm_num), mmax_three_1e12]

/-- Characteristic `5` at `M = 10¹²`: `3 - 2/4 - 1 = 2` dual failures, `5¹⁰` and `5¹⁵`. -/
theorem card_dualExponents_five_1e12 :
    #{k ∈ Finset.Icc 1 (10 ^ 12) | IsDualFailure 5 k ∧ 5 ^ k ≤ 10 ^ 12} = 2 := by
  rw [card_dualExponents (by norm_num) (by norm_num) (by norm_num), mmax_five_1e12]

/-- Characteristic `7` at `M = 10¹²`: `2 - 1/6 - 1 = 1` dual failure, `7¹⁴`. -/
theorem card_dualExponents_seven_1e12 :
    #{k ∈ Finset.Icc 1 (10 ^ 12) | IsDualFailure 7 k ∧ 7 ^ k ≤ 10 ^ 12} = 1 := by
  rw [card_dualExponents (by norm_num) (by norm_num) (by norm_num), mmax_seven_1e12]

/-- The three counts add up to the seven pairs listed in `census_1e12`. -/
theorem count_1e12_split :
    #{k ∈ Finset.Icc 1 (10 ^ 12) | IsDualFailure 3 k ∧ 3 ^ k ≤ 10 ^ 12}
      + #{k ∈ Finset.Icc 1 (10 ^ 12) | IsDualFailure 5 k ∧ 5 ^ k ≤ 10 ^ 12}
      + #{k ∈ Finset.Icc 1 (10 ^ 12) | IsDualFailure 7 k ∧ 7 ^ k ≤ 10 ^ 12}
      = [(3, 6), (3, 12), (3, 18), (3, 24), (5, 10), (5, 15), (7, 14)].length := by
  rw [card_dualExponents_three_1e12, card_dualExponents_five_1e12,
    card_dualExponents_seven_1e12]
  rfl

/-! ## Dual failure is not quite "no multiplicative repair at all"

A dual failure says the two *canonical* maps are both broken.  Whether some *other*
multiplicative map repairs the multiplicative side is the coprimality criterion
`FrobeniusPrimeSubfield.multiplicative_retraction_iff_coprime`, and the two conditions differ:
`729 = 3⁶` admits no multiplicative retraction whatsoever, while `5¹⁵` — a dual failure — does.
-/

/-- If a dual failure has even degree then no multiplicative retraction exists at all: `2`
divides both `k` and `p - 1`. -/
theorem gcd_ne_one_of_even {p k : ℕ} (h : IsDualFailure p k) (hk : Even k) :
    Nat.gcd k (p - 1) ≠ 1 := by
  have hp : p.Prime := h.1
  have h3 : 3 ≤ p := three_le_of_isDualFailure h
  have hpe : 2 ∣ (p - 1) := by
    have hodd : ¬ 2 ∣ p := by
      intro hd
      rcases hp.eq_one_or_self_of_dvd 2 hd with h1 | h1 <;> omega
    omega
  have h2 : 2 ∣ Nat.gcd k (p - 1) := Nat.dvd_gcd hk.two_dvd hpe
  omega

/-- **`GF(729)`: no multiplicative retraction at all** — `gcd (6, 3 - 1) = 2`. -/
theorem gf729_no_multiplicative_retraction {K : Type*} [Field K] [Fintype K] [CharP K 3]
    (hK : Nat.card K = 3 ^ 6) :
    ¬ ∃ f : K → K, (∀ x y, f (x * y) = f x * f y) ∧ (∀ x, (f x) ^ 3 = f x) ∧
        (∀ a : K, a ^ 3 = a → f a = a) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [FrobeniusPrimeSubfield.multiplicative_retraction_iff_coprime hK (by norm_num)]
  decide

/-- **`GF(5¹⁵)`: a dual failure that still has a multiplicative retraction** — the orbit product
itself is not one (`4 ∤ 14`), but `gcd (15, 5 - 1) = 1`, so some power of it is.  Dual failure
means both *canonical* dials are dead, not that every repair is. -/
theorem gf5pow15_multiplicative_retraction {K : Type*} [Field K] [Fintype K] [CharP K 5]
    (hK : Nat.card K = 5 ^ 15) :
    ∃ f : K → K, (∀ x y, f (x * y) = f x * f y) ∧ (∀ x, (f x) ^ 5 = f x) ∧
        (∀ a : K, a ^ 5 = a → f a = a) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact (FrobeniusPrimeSubfield.multiplicative_retraction_iff_coprime hK (by norm_num)).2
    (by decide)

/-! ## The total count: a sum over the odd primes -/

/-- All dual-failure pairs `(p, k)` of size at most `M`, as a finite set. -/
def dualPairs (M : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter fun pk => IsDualFailure pk.1 pk.2 ∧ pk.1 ^ pk.2 ≤ M

theorem char_mem_Icc {M p k : ℕ} (h : IsDualFailure p k) (hM : p ^ k ≤ M) :
    1 ≤ p ∧ p ≤ M := by
  have hk : k ≠ 0 := by have := h.2.1; omega
  exact ⟨h.1.pos, le_trans (Nat.le_self_pow hk p) hM⟩

theorem exponent_mem_Icc {M p k : ℕ} (h : IsDualFailure p k) (hM : p ^ k ≤ M) :
    1 ≤ k ∧ k ≤ M :=
  ⟨h.2.1, le_trans (Nat.le_of_lt (Nat.lt_pow_self h.1.one_lt)) hM⟩

theorem mem_dualPairs {M p k : ℕ} :
    (p, k) ∈ dualPairs M ↔ IsDualFailure p k ∧ p ^ k ≤ M := by
  simp only [dualPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  exact ⟨fun h => h.2, fun h => ⟨⟨char_mem_Icc h.1 h.2, exponent_mem_Icc h.1 h.2⟩, h⟩⟩

/-- **The total count is a sum over the primes** of the per-characteristic counts. -/
theorem card_dualPairs_eq_sum (M : ℕ) :
    (dualPairs M).card
      = ∑ p ∈ (Finset.Icc 1 M).filter Nat.Prime,
          #{k ∈ Finset.Icc 1 M | IsDualFailure p k ∧ p ^ k ≤ M} := by
  have hfib : Set.MapsTo Prod.fst (↑(dualPairs M) : Set (ℕ × ℕ))
      (↑((Finset.Icc 1 M).filter Nat.Prime) : Set ℕ) := by
    rintro ⟨a, k⟩ hx
    simp only [Finset.mem_coe] at hx
    rw [mem_dualPairs] at hx
    exact Finset.mem_coe.2
      (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 (char_mem_Icc hx.1 hx.2), hx.1.1⟩)
  rw [Finset.card_eq_sum_card_fiberwise hfib]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.card_nbij' Prod.snd (fun k => (p, k)) ?_ ?_ ?_ ?_
  · rintro ⟨a, k⟩ hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx
    obtain ⟨hmem, hfst⟩ := hx
    have ha : a = p := hfst
    subst ha
    rw [mem_dualPairs] at hmem
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨exponent_mem_Icc hmem.1 hmem.2, hmem⟩
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hk
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨mem_dualPairs.2 hk.2, ?_⟩)
    rfl
  · rintro ⟨a, k⟩ hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx
    have ha : a = p := hx.2
    subst ha
    rfl
  · intro k _
    rfl

/-- **The formula of the census, in full**: the number of dual failures of size at most `M` is
the sum over the odd primes `p ≤ M` of `mmax − (mmax − 1)/(p − 1) − 1`.  (Characteristic `2`
contributes nothing, and so does every `p` with `p^(2p) > M`, for which `mmax ≤ 1`.) -/
theorem card_dualPairs_eq_sum_formula (M : ℕ) (hM : 1 ≤ M) :
    (dualPairs M).card
      = ∑ p ∈ (Finset.Icc 1 M).filter (fun p => p.Prime ∧ p ≠ 2),
          (mmax p M - (mmax p M - 1) / (p - 1) - 1) := by
  rw [card_dualPairs_eq_sum, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hprime : p.Prime
  · rcases eq_or_ne p 2 with rfl | hne
    · rw [if_pos hprime, if_neg (by simp), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun k _ h => not_isDualFailure_two k h.1
    · rw [if_pos hprime, if_pos ⟨hprime, hne⟩, card_dualExponents hprime hne hM]
  · rw [if_neg hprime, if_neg (by tauto)]

/-- The dual-failure pairs below `10¹²`, as a finite set. -/
theorem dualPairs_1e12 :
    dualPairs (10 ^ 12) = {(3, 6), (3, 12), (3, 18), (3, 24), (5, 10), (5, 15), (7, 14)} := by
  ext ⟨p, k⟩
  rw [mem_dualPairs, census_1e12]
  simp

/-- **Seven dual failures below `10¹²`** — the total the counting formula predicts. -/
theorem card_dualPairs_1e12 : (dualPairs (10 ^ 12)).card = 7 := by
  rw [dualPairs_1e12]
  decide

end DualDial
