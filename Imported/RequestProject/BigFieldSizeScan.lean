import RequestProject.FieldSizeScan

/-!
# The expanded scan: every size `q = 2 … 1824`

`RequestProject/FieldSizeScan.lean` scans the candidate field sizes `q = 2 … 97`.  This file
runs the same scan over **`q = 2 … 1824`**, which needs a prime-power decomposition that the
kernel can evaluate 1823 times.

The decomposition used here is a *trial division bounded by the square root*:

* `leastFactorAux q` is the first `d ≥ 2` with `d ∣ q` **or** `q < d²`;
* `leastFactor q` is that `d` when it divides `q`, and `q` itself otherwise — the least prime
  factor of `q` (`leastFactor_prime`, `leastFactor_dvd`), reached in `O(√q)` kernel steps
  instead of the `O(q²)` of the small scan;
* `gfDataBig q = some (p, k)` iff `q = p ^ k` with `p` prime and `k ≥ 1`
  (`gfDataBig_eq_some_iff`, valid for `q < 4096`), i.e. iff a field of order `q` exists
  (`card_ne_of_gfDataBig_eq_none`).

The error attached to a field size is unchanged: `FieldSizeScan.frobDefect p k =
(p − 1) − gcd (p − 1) (k − 1)` counts the elements of `𝔽ₚ` moved by the Frobenius orbit
product of `GF(pᵏ)` (`FieldSizeScan.card_frobNorm_failures`), and vanishes exactly when that
orbit product is a retraction onto `𝔽ₚ` (`FieldSizeScan.retraction_iff_frobDefect_eq_zero`).

What the expanded scan finds, all by kernel computation:

* of the 1823 candidate sizes, **1513 are not field sizes at all**, 292 are field sizes whose
  orbit product is a genuine retraction, and **18 are field sizes with a nonzero error**
  (`bigScan_partition_counts`);
* the 18 failures are listed in `bigScan_failing_sizes`, the largest error being `39`, attained
  only at `q = 1681 = 41²` (`bigScan_max_error`);
* the proper prime powers (`k ≥ 2`) that *do* retract are
  `4, 8, 16, 27, 32, 64, 128, 243, 256, 512, 1024` (`bigScan_retractive_proper_prime_powers`):
  the powers of `2`, plus the two odd-characteristic ones `27 = 3³` and `243 = 3⁵`;
* the endpoint `1824 = 2⁵·3·19` is itself not a field size (`bigScan_endpoint`).

The data is drawn in three dimensions by `RequestProject/Heatmap3D.lean`.
-/

set_option maxRecDepth 4000000

namespace BigFieldSizeScan

open FieldSizeScan FrobeniusPrimeSubfield

/-! ### `find?` over an interval finds the least solution -/

/-- What `find?` over `List.range' s n` returns: a solution of `P`, inside the interval, with
no smaller solution in it. -/
theorem find?_range'_spec {P : ℕ → Bool} {s n a : ℕ}
    (h : (List.range' s n).find? P = some a) :
    P a ∧ s ≤ a ∧ a < s + n ∧ ∀ b, s ≤ b → b < a → P b = false := by
  induction n generalizing s with
  | zero => simp at h
  | succ n ih =>
    rw [List.range'_succ, List.find?_cons] at h
    by_cases hs : P s = true
    · rw [hs] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hs, le_refl _, by omega, fun b hb hlt => absurd hb (by omega)⟩
    · simp only [Bool.not_eq_true] at hs
      rw [hs] at h
      simp only at h
      obtain ⟨hPa, hle, hlt, hmin⟩ := ih h
      refine ⟨hPa, by omega, by omega, ?_⟩
      intro b hb hba
      rcases eq_or_lt_of_le hb with rfl | hb'
      · exact hs
      · exact hmin b (by omega) hba

/-- If some element of the interval solves `P`, then `find?` succeeds, and returns a solution
no larger than it. -/
theorem find?_range'_le_of_mem {P : ℕ → Bool} {s n b : ℕ} (hb : b ∈ List.range' s n)
    (hPb : P b) : ∃ a, (List.range' s n).find? P = some a ∧ a ≤ b := by
  rcases hfind : (List.range' s n).find? P with _ | a
  · rw [List.find?_eq_none] at hfind
    exact absurd hPb (hfind b hb)
  · obtain ⟨-, -, -, hmin⟩ := find?_range'_spec hfind
    refine ⟨a, rfl, ?_⟩
    by_contra hlt
    push_neg at hlt
    rw [List.mem_range'_1] at hb
    rw [hmin b hb.1 hlt] at hPb
    exact absurd hPb (by simp)

/-! ### The least prime factor, by trial division up to the square root -/

/-- The first `d ≥ 2` with `d ∣ q` or `q < d²`. -/
def leastFactorAux (q : ℕ) : ℕ :=
  ((List.range' 2 (q - 1)).find? (fun d => (q % d == 0) || decide (q < d * d))).getD q

/-- The least prime factor of `q`, computed by trial division bounded by `√q`. -/
def leastFactor (q : ℕ) : ℕ := if q % leastFactorAux q == 0 then leastFactorAux q else q

/-- What the bounded trial division produces. -/
theorem leastFactorAux_spec {q : ℕ} (hq : 2 ≤ q) :
    2 ≤ leastFactorAux q ∧ leastFactorAux q ≤ q ∧
      (q % leastFactorAux q = 0 ∨ q < leastFactorAux q * leastFactorAux q) ∧
      ∀ e, 2 ≤ e → e < leastFactorAux q → ¬ e ∣ q := by
  have hmem : q ∈ List.range' 2 (q - 1) := List.mem_range'_1.2 ⟨hq, by omega⟩
  have hPq : ((fun d => (q % d == 0) || decide (q < d * d)) q) = true := by
    simp [Nat.mod_self]
  obtain ⟨a, hfind, -⟩ :=
    find?_range'_le_of_mem (P := fun d => (q % d == 0) || decide (q < d * d)) hmem hPq
  obtain ⟨hPa, hlea, hlta, hmin⟩ := find?_range'_spec hfind
  have haux : leastFactorAux q = a := by
    unfold leastFactorAux
    rw [hfind]
    rfl
  rw [haux]
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hPa
  refine ⟨hlea, by omega, hPa, ?_⟩
  intro e he hea hdvd
  have hb := hmin e he hea
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not] at hb
  exact hb.1 (Nat.dvd_iff_mod_eq_zero.mp hdvd)

/-- The least prime factor divides. -/
theorem leastFactor_dvd (q : ℕ) : leastFactor q ∣ q := by
  unfold leastFactor
  by_cases h : q % leastFactorAux q = 0
  · simp only [h, beq_self_eq_true, if_true]
    exact Nat.dvd_of_mod_eq_zero h
  · simp only [beq_iff_eq, h, if_false]
    exact dvd_rfl

/-- The least prime factor is prime. -/
theorem leastFactor_prime {q : ℕ} (hq : 2 ≤ q) : (leastFactor q).Prime := by
  obtain ⟨h2, hle, hdisj, hmin⟩ := leastFactorAux_spec hq
  unfold leastFactor
  by_cases h : q % leastFactorAux q = 0
  · simp only [h, beq_self_eq_true, if_true]
    refine Nat.prime_def_lt'.2 ⟨h2, fun m hm hlt hdvd => ?_⟩
    exact hmin m hm hlt (hdvd.trans (Nat.dvd_of_mod_eq_zero h))
  · simp only [beq_iff_eq, h, if_false]
    by_contra hnp
    have hsq : q.minFac ^ 2 ≤ q := Nat.minFac_sq_le_self (by omega) hnp
    have hmp : q.minFac.Prime := Nat.minFac_prime (by omega)
    have hmd : q.minFac ∣ q := Nat.minFac_dvd q
    have hq2 : q < leastFactorAux q * leastFactorAux q := by
      rcases hdisj with h0 | h0
      · exact absurd h0 h
      · exact h0
    have hlt : q.minFac < leastFactorAux q := by
      by_contra hge
      push_neg at hge
      have : leastFactorAux q * leastFactorAux q ≤ q.minFac * q.minFac :=
        Nat.mul_le_mul hge hge
      have hsq' : q.minFac * q.minFac ≤ q := by
        rw [pow_two] at hsq; exact hsq
      omega
    exact hmin q.minFac hmp.two_le hlt hmd

/-- On a prime power the least prime factor is the base. -/
theorem leastFactor_eq_of_prime_pow {p k q : ℕ} (hp : p.Prime) (hk : 0 < k) (h : p ^ k = q) :
    leastFactor q = p := by
  have hq2 : 2 ≤ q := by
    calc 2 ≤ p := hp.two_le
      _ ≤ p ^ k := Nat.le_self_pow hk.ne' p
      _ = q := h
  have hfp := leastFactor_prime hq2
  have hfd : leastFactor q ∣ p ^ k := h ▸ leastFactor_dvd q
  exact (Nat.prime_dvd_prime_iff_eq hfp hp).1 (hfp.dvd_of_dvd_pow hfd)

/-! ### Reading a number as a field size -/

/-- The exponent `k ≤ 12` with `p ^ k = q`, if there is one. -/
def expOf (p q : ℕ) : Option ℕ := (List.range' 1 12).find? (fun k => p ^ k == q)

/-- The prime-power decomposition of a candidate field size `q < 4096`: `gfDataBig q =
some (p, k)` iff `q = p ^ k` with `p` prime and `k ≥ 1`. -/
def gfDataBig (q : ℕ) : Option (ℕ × ℕ) :=
  if 2 ≤ q then (expOf (leastFactor q) q).map (fun k => (leastFactor q, k)) else none

/-- **`gfDataBig` is correct** on the range of the scan. -/
theorem gfDataBig_eq_some_iff {q p k : ℕ} (hq : q < 4096) :
    gfDataBig q = some (p, k) ↔ (p.Prime ∧ 0 < k ∧ p ^ k = q) := by
  constructor
  · intro h
    unfold gfDataBig at h
    by_cases hq2 : 2 ≤ q
    · rw [if_pos hq2] at h
      rcases hexp : expOf (leastFactor q) q with _ | k'
      · rw [hexp] at h; simp at h
      · rw [hexp] at h
        obtain ⟨rfl, rfl⟩ : leastFactor q = p ∧ k' = k := by simpa [Prod.ext_iff] using h
        have hval := List.find?_some hexp
        simp only [beq_iff_eq] at hval
        have hmem := List.mem_of_find?_eq_some hexp
        rw [List.mem_range'_1] at hmem
        exact ⟨leastFactor_prime hq2, by omega, hval⟩
    · rw [if_neg hq2] at h; simp at h
  · rintro ⟨hp, hk, rfl⟩
    have hq2 : 2 ≤ p ^ k := by
      calc 2 ≤ p := hp.two_le
        _ ≤ p ^ k := Nat.le_self_pow hk.ne' p
    have hklt : k < 12 := by
      have h2k : (2 : ℕ) ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
      have h12 : (2 : ℕ) ^ k < 2 ^ 12 := by
        have : (2 : ℕ) ^ 12 = 4096 := by norm_num
        omega
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h12
    have hbase : leastFactor (p ^ k) = p := leastFactor_eq_of_prime_pow hp hk rfl
    have hexp : expOf p (p ^ k) = some k := by
      refine find?_eq_some_of_unique (List.range' 1 12) (fun j => p ^ j == p ^ k) k
        (List.mem_range'_1.2 ⟨hk, by omega⟩) (by simp) ?_
      intro x _ hx
      simp only [beq_iff_eq] at hx
      exact Nat.pow_right_injective hp.two_le hx
    unfold gfDataBig
    rw [if_pos hq2, hbase, hexp]
    rfl

/-- `q < 4096` is a possible field size exactly when `gfDataBig q` succeeds. -/
theorem gfDataBig_isSome_iff_isPrimePow {q : ℕ} (hq : q < 4096) :
    (gfDataBig q).isSome ↔ IsPrimePow q := by
  constructor
  · intro h
    obtain ⟨⟨p, k⟩, hpk⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨hp, hk, rfl⟩ := (gfDataBig_eq_some_iff hq).1 hpk
    exact ⟨p, k, hp.prime, hk, rfl⟩
  · intro h
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 h
    rw [(gfDataBig_eq_some_iff hq).2 ⟨hp, hk, rfl⟩]
    rfl

/-- **A hard error of the expanded scan**: if `gfDataBig q = none` for a `q < 4096`, then no
finite field has `q` elements. -/
theorem card_ne_of_gfDataBig_eq_none {q : ℕ} (hq : q < 4096) (hnone : gfDataBig q = none)
    (K : Type*) [Field K] [Fintype K] : Fintype.card K ≠ q := by
  intro hcard
  have hpp : IsPrimePow q := hcard ▸ Fintype.isPrimePow_card_of_field (α := K)
  rw [← gfDataBig_isSome_iff_isPrimePow hq] at hpp
  rw [hnone] at hpp
  exact absurd hpp (by simp)

/-! ### The scan `q = 2 … 1824` -/

/-- One row of the expanded scan: the candidate size `q`, together with `some (p, k, error)`
when `q = p ^ k` is a field size, and `none` when it is not. -/
def bigScanRow (q : ℕ) : ℕ × Option (ℕ × ℕ × ℕ) :=
  (q, (gfDataBig q).map fun pk => (pk.1, pk.2, frobDefect pk.1 pk.2))

/-- The scan of all candidate sizes `q = 2, 3, …, 1824`. -/
def bigScan : List (ℕ × Option (ℕ × ℕ × ℕ)) := (List.range' 2 1823).map bigScanRow

/-- Every candidate size in `2 … 1824` falls into exactly one of three classes: not a field
size (1513 values), a field size whose orbit product is a genuine retraction (292 values), or a
field size with a nonzero error (18 values). -/
theorem bigScan_partition_counts :
    bigScan.length = 1823 ∧
    (bigScan.filter fun r => r.2.isNone).length = 1513 ∧
    (bigScan.filter fun r =>
        match r.2 with | some (_, _, d) => d == 0 | none => false).length = 292 ∧
    (bigScan.filter fun r =>
        match r.2 with | some (_, _, d) => d != 0 | none => false).length = 18 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **The 18 failures below 1825**, as `(q, p, k, error)`.  Every one of them has degree
`k = 2, 3, 4` or `6` over a prime field of odd characteristic. -/
theorem bigScan_failing_sizes :
    (bigScan.filterMap fun r =>
        match r.2 with
        | some (p, k, d) => if d ≠ 0 then some (r.1, p, k, d) else none
        | none => none) =
      [(9, 3, 2, 1), (25, 5, 2, 3), (49, 7, 2, 5), (81, 3, 4, 1), (121, 11, 2, 9),
       (125, 5, 3, 2), (169, 13, 2, 11), (289, 17, 2, 15), (343, 7, 3, 4), (361, 19, 2, 17),
       (529, 23, 2, 21), (625, 5, 4, 3), (729, 3, 6, 1), (841, 29, 2, 27), (961, 31, 2, 29),
       (1331, 11, 3, 8), (1369, 37, 2, 35), (1681, 41, 2, 39)] := by
  decide +kernel

/-- The proper prime powers `q = p ^ k ≤ 1824` (`k ≥ 2`) whose Frobenius orbit product **is** a
retraction onto the prime subfield: the powers of `2` (where the retraction is degenerate,
`WhyTwentySeven.frobNorm_eq_one_of_char_two`), together with `27 = 3³` and `243 = 3⁵`. -/
theorem bigScan_retractive_proper_prime_powers :
    (bigScan.filterMap fun r =>
        match r.2 with
        | some (_, k, d) => if d = 0 ∧ 2 ≤ k then some r.1 else none
        | none => none) = [4, 8, 16, 27, 32, 64, 128, 243, 256, 512, 1024] := by
  decide +kernel

/-- **The worst error below 1825 is 39**, attained only at `q = 1681 = 41²`. -/
theorem bigScan_max_error :
    (bigScan.filterMap fun r =>
        match r.2 with
        | some (_, _, d) => if 39 ≤ d then some r.1 else none
        | none => none) = [1681] ∧
    bigScan.all (fun r =>
      match r.2 with | some (_, _, d) => d ≤ 39 | none => true) = true := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- The endpoint of the scan is itself not a field size: `1824 = 2⁵·3·19`, so by
`card_ne_of_gfDataBig_eq_none` no field has 1824 elements. -/
theorem bigScan_endpoint : gfDataBig 1824 = none ∧ 1824 = 2 ^ 5 * 3 * 19 := by
  refine ⟨by decide +kernel, by norm_num⟩

/-- No field has `1824` elements. -/
theorem card_ne_1824 (K : Type*) [Field K] [Fintype K] : Fintype.card K ≠ 1824 :=
  card_ne_of_gfDataBig_eq_none (by norm_num) bigScan_endpoint.1 K

/-! ### The three new field sizes on Mathlib's `GaloisField` -/

section GaloisFields

local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩

/-- `GF(243) = GF(3⁵)`: error `0`, a genuine retraction — the second odd-characteristic
example, after `GF(27)`. -/
theorem gf243_retractive :
    ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 3 5) 3), frobNorm 3 5 a = a :=
  (galoisField_retraction_iff_frobDefect 3 5 (by norm_num)).2 (by decide)

/-- `GF(1024) = GF(2¹⁰)`: error `0`, a retraction (characteristic `2`). -/
theorem gf1024_retractive :
    ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 2 10) 2), frobNorm 2 10 a = a :=
  (galoisField_retraction_iff_frobDefect 2 10 (by norm_num)).2 (by decide)

/-- `GF(1681) = GF(41²)`: error `39` — the orbit product moves 39 of the 40 units of `𝔽₄₁`,
the worst failure below `1825`. -/
theorem gf1681_error_39 :
    ¬ (∀ a ∈ Set.range (primeSubfieldHom (GaloisField 41 2) 41), frobNorm 41 2 a = a) ∧
      frobDefect 41 2 = 39 := by
  refine ⟨fun h => ?_, by decide⟩
  have hd := (galoisField_retraction_iff_frobDefect 41 2 (by norm_num)).1 h
  simp [frobDefect] at hd

end GaloisFields

end BigFieldSizeScan
