import RequestProject.WhyTwentySeven

/-!
# Scanning every size `q = 2 … 97` as a potential `GF(q)`, with its error count

`RequestProject/WhyTwentySeven.lean` shows that for a field of characteristic `p` with `p ^ k`
elements the Frobenius orbit product

  `N(x) = x · x^p · … · x^(p^(k-1))`

is a retraction onto the prime subfield `𝔽ₚ` **iff `p - 1 ∣ k - 1`**.  This file turns that
yes/no criterion into a *quantitative* one and runs it over every candidate size
`q = 2, 3, …, 97`.

Two things are measured for each `q`.

* **Is `q` a field size at all?**  `gfData q` returns `some (p, k)` exactly when `q = p ^ k` for
  a prime `p` and `k ≥ 1` (`gfData_eq_some_iff`), and `none` exactly when no field of order `q`
  exists (`gfData_isSome_iff_isPrimePow`, `card_ne_of_gfData_eq_none`).  These `none` values are
  the *hard errors* of the scan: `6, 10, 12, 14, 15, …` are not field sizes at all.

* **How badly does the retraction fail?**  For `q = p ^ k` put

    `frobDefect p k = (p - 1) - gcd (p - 1) (k - 1)`.

  This is exactly the number of elements of the prime field that the orbit product moves:
  on `𝔽ₚ` the orbit product is `a ↦ a ^ k`, and `card_frobNorm_failures` proves

    `#{a ∈ 𝔽ₚ | a ^ k ≠ a} = frobDefect p k`.

  So `frobDefect` is the error bar of the picture: `0` means "genuine retraction"
  (`retraction_iff_frobDefect_eq_zero`), and the largest possible value is `p - 1`, i.e. every
  unit of the prime field is moved.

The scan itself is `fieldSizeScan`, and the classification theorems `scan_no_field_sizes`,
`scan_retractive_sizes`, `scan_failing_sizes`, `scan_partition_counts` are checked by kernel
computation.  Each of the ten proper prime powers `q = p ^ k ≤ 97` is then also tested on
Mathlib's actual field `GaloisField p k` (`gf4_retractive` … `gf81_error_one`).  The data is
plotted by `RequestProject/ScanVisualization.lean` into `svg/field-size-scan.svg`.
-/

set_option maxRecDepth 100000

open Finset FrobeniusPrimeSubfield

namespace FieldSizeScan

/-! ### Reading a number as a potential field size

`Nat.minFac` and `Nat.primeFactorsList` are defined by well-founded recursion and therefore do
not reduce in the kernel, so the prime-power decomposition is computed here by two bounded
searches, which do.  `gfData_eq_some_iff` proves that the search is correct. -/

/-- A `find?` over a list whose predicate is satisfied by at most one element returns that
element. -/
theorem find?_eq_some_of_unique {α : Type*} (l : List α) (P : α → Bool) (a : α) (ha : a ∈ l)
    (hP : P a) (huniq : ∀ x ∈ l, P x → x = a) : l.find? P = some a := by
  induction l with
  | nil => simp at ha
  | cons b t ih =>
    rw [List.find?_cons]
    by_cases hb : P b
    · have hba := huniq b (by simp) hb
      subst hba
      simp [hb]
    · simp only [hb]
      refine ih ?_ (fun x hx hPx => huniq x (by simp [hx]) hPx)
      rcases List.mem_cons.1 ha with rfl | h
      · exact absurd hP hb
      · exact h

/-- The characteristic of a potential field of order `q`: the unique prime `p` such that `q` is
a positive power of `p`, if there is one. -/
def gfChar (q : ℕ) : Option ℕ :=
  (List.range' 2 q).find?
    (fun p => decide (Nat.Prime p) && (List.range' 1 q).any (fun k => p ^ k == q))

/-- The prime-power decomposition of a candidate field size: `gfData q = some (p, k)` iff
`q = p ^ k` with `p` prime and `k ≥ 1`, i.e. iff a field with `q` elements exists — in which
case `p` is its characteristic and `k` its degree over the prime field.  Otherwise `none`. -/
def gfData (q : ℕ) : Option (ℕ × ℕ) :=
  (gfChar q).bind fun p => ((List.range' 1 q).find? (fun k => p ^ k == q)).map fun k => (p, k)

/-- Two prime powers with the same value have the same base. -/
theorem prime_pow_base_unique {p p' k k' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (hk' : 0 < k') (h : p' ^ k' = p ^ k) : p' = p := by
  have hd : p' ∣ p ^ k := h ▸ dvd_pow_self p' hk'.ne'
  exact (Nat.prime_dvd_prime_iff_eq hp' hp).1 (hp'.dvd_of_dvd_pow hd)

/-- **`gfData` is correct**: it returns the prime-power decomposition of `q` when there is one. -/
theorem gfData_eq_some_iff {q p k : ℕ} :
    gfData q = some (p, k) ↔ (p.Prime ∧ 0 < k ∧ p ^ k = q) := by
  constructor
  · intro h
    unfold gfData at h
    rcases hfp : gfChar q with _ | p'
    · rw [hfp] at h; simp at h
    · rw [hfp] at h
      replace h : ((List.range' 1 q).find? (fun j => p' ^ j == q)).map (fun j => (p', j))
          = some (p, k) := h
      have hp' : Nat.Prime p' := by
        have hs := List.find?_some hfp
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
        exact hs.1
      rcases hfk : (List.range' 1 q).find? (fun j => p' ^ j == q) with _ | k'
      · rw [hfk] at h; simp at h
      · rw [hfk] at h
        obtain ⟨rfl, rfl⟩ : p' = p ∧ k' = k := by simpa [Prod.ext_iff] using h
        have hpred := List.find?_some hfk
        simp only [beq_iff_eq] at hpred
        have hmem := List.mem_of_find?_eq_some hfk
        rw [List.mem_range'_1] at hmem
        exact ⟨hp', by omega, hpred⟩
  · rintro ⟨hp, hk, rfl⟩
    have hk2 : k < 1 + p ^ k := by
      have h1 : k < 2 ^ k := Nat.lt_two_pow_self
      have h2 : (2 : ℕ) ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
      omega
    have hp2 : p < 2 + p ^ k := by
      have h1 : p ^ 1 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
      simp only [pow_one] at h1
      omega
    have hstage1 : gfChar (p ^ k) = some p := by
      refine find?_eq_some_of_unique _ _ _ (List.mem_range'_1.2 ⟨hp.two_le, hp2⟩) ?_ ?_
      · simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
        exact ⟨hp, k, List.mem_range'_1.2 ⟨hk, hk2⟩, by simp⟩
      · intro x _ hPx
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hPx
        obtain ⟨hxp, j, hj, hjq⟩ := hPx
        rw [List.mem_range'_1] at hj
        exact prime_pow_base_unique hp hxp (by omega) hjq
    have hstage2 : (List.range' 1 (p ^ k)).find? (fun j => p ^ j == p ^ k) = some k := by
      refine find?_eq_some_of_unique _ _ _ (List.mem_range'_1.2 ⟨hk, hk2⟩) (by simp) ?_
      intro x _ hPx
      simp only [beq_iff_eq] at hPx
      exact Nat.pow_right_injective hp.two_le hPx
    unfold gfData
    rw [hstage1]
    show (((List.range' 1 (p ^ k)).find? fun j => p ^ j == p ^ k).map fun j => (p, j))
        = some (p, k)
    rw [hstage2, Option.map_some]

/-- `q` is a possible field size exactly when `gfData q` succeeds. -/
theorem gfData_isSome_iff_isPrimePow (q : ℕ) : (gfData q).isSome ↔ IsPrimePow q := by
  constructor
  · intro h
    obtain ⟨⟨p, k⟩, hpk⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨hp, hk, rfl⟩ := gfData_eq_some_iff.1 hpk
    exact ⟨p, k, hp.prime, hk, rfl⟩
  · intro h
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 h
    rw [gfData_eq_some_iff.2 ⟨hp, hk, rfl⟩]
    rfl

/-- **A hard error of the scan.**  If `gfData q = none` then there is no field with `q`
elements at all. -/
theorem card_ne_of_gfData_eq_none {q : ℕ} (hq : gfData q = none) (K : Type*) [Field K]
    [Fintype K] : Fintype.card K ≠ q := by
  intro hcard
  have hpp : IsPrimePow q := hcard ▸ Fintype.isPrimePow_card_of_field (α := K)
  rw [← gfData_isSome_iff_isPrimePow] at hpp
  rw [hq] at hpp
  exact absurd hpp (by simp)

/-! ### The error attached to a field size -/

/-- **The error of `GF(p ^ k)`**: the number of elements of the prime field `𝔽ₚ` that the
Frobenius orbit product fails to fix, `(p - 1) - gcd (p - 1) (k - 1)`.  It is `0` exactly when
the orbit product is a retraction onto `𝔽ₚ`, and at most `p - 1`. -/
def frobDefect (p k : ℕ) : ℕ := (p - 1) - Nat.gcd (p - 1) (k - 1)

theorem frobDefect_le (p k : ℕ) : frobDefect p k ≤ p - 1 := Nat.sub_le _ _

/-- The error vanishes exactly on the divisibility criterion `p - 1 ∣ k - 1`. -/
theorem frobDefect_eq_zero_iff {p k : ℕ} (hp : p.Prime) :
    frobDefect p k = 0 ↔ p - 1 ∣ k - 1 := by
  have h2 := hp.two_le
  constructor
  · intro h
    have hle : p - 1 ≤ Nat.gcd (p - 1) (k - 1) := by
      unfold frobDefect at h; omega
    have hge : Nat.gcd (p - 1) (k - 1) ≤ p - 1 :=
      Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
    have hgcd : Nat.gcd (p - 1) (k - 1) = p - 1 := by omega
    exact hgcd ▸ Nat.gcd_dvd_right (p - 1) (k - 1)
  · intro h
    have hgcd : Nat.gcd (p - 1) (k - 1) = p - 1 := Nat.gcd_eq_left h
    unfold frobDefect
    omega

/-- In the cyclic group `(ZMod p)ˣ` of order `p - 1`, the number of solutions of `u ^ k = 1` is
`gcd (p - 1) k`. -/
theorem card_units_pow_eq_one (p k : ℕ) [Fact p.Prime] :
    #({u : (ZMod p)ˣ | u ^ k = 1} : Finset _) = Nat.gcd (p - 1) k := by
  have h := IsCyclic.card_powMonoidHom_ker (G := (ZMod p)ˣ) k
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card_units p] at h
  rw [← h, Fintype.card_subtype]
  congr 1
  ext u
  simp [MonoidHom.mem_ker, powMonoidHom]

/-- The fixed points of `a ↦ a ^ k` on `𝔽ₚ`: zero, together with the `(k-1)`-st roots of
unity. -/
theorem frobNorm_fixed_eq (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) :
    ({a : ZMod p | a ^ k = a} : Finset (ZMod p)) =
      insert 0 (({u : (ZMod p)ˣ | u ^ (k - 1) = 1} : Finset _).image Units.val) := by
  ext a
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_image]
  constructor
  · intro h
    rcases eq_or_ne a 0 with rfl | ha
    · exact Or.inl rfl
    · refine Or.inr ⟨Units.mk0 a ha, ?_, rfl⟩
      have h2 : a ^ (k - 1) * a = a := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk)]
        exact h
      have h3 := mul_right_cancel₀ ha (h2.trans (one_mul a).symm)
      have h4 : (Units.mk0 a ha) ^ (k - 1) = 1 := by ext; simpa using h3
      simpa using h4
  · rintro (rfl | ⟨u, hu, rfl⟩)
    · simp [zero_pow hk]
    · replace hu : u ^ (k - 1) = 1 := by simpa using hu
      have h1 : ((u ^ (k - 1) : (ZMod p)ˣ) : ZMod p) = 1 := by rw [hu]; simp
      push_cast at h1
      calc ((u : ZMod p)) ^ k = (u : ZMod p) ^ (k - 1) * u := by
            rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk)]
        _ = u := by rw [h1, one_mul]

/-- **The error is a genuine count.**  On the prime field `𝔽ₚ` the Frobenius orbit product of a
field with `p ^ k` elements is `a ↦ a ^ k`, and the number of elements it moves is exactly
`frobDefect p k`. -/
theorem card_frobNorm_failures (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) :
    #({a : ZMod p | a ^ k ≠ a} : Finset (ZMod p)) = frobDefect p k := by
  have hp2 := (Fact.out : p.Prime).two_le
  have hfix : #({a : ZMod p | a ^ k = a} : Finset (ZMod p)) = 1 + Nat.gcd (p - 1) (k - 1) := by
    have h0 : (0 : ZMod p) ∉ ({u : (ZMod p)ˣ | u ^ (k - 1) = 1} : Finset _).image Units.val := by
      intro hmem
      obtain ⟨u, -, hu⟩ := mem_image.1 hmem
      exact u.ne_zero hu
    rw [frobNorm_fixed_eq p k hk, Finset.card_insert_of_notMem h0,
      Finset.card_image_of_injective _ Units.val_injective, card_units_pow_eq_one]
    omega
  have htot : #({a : ZMod p | a ^ k = a} : Finset (ZMod p)) +
      #({a : ZMod p | a ^ k ≠ a} : Finset (ZMod p)) = p := by
    have h : #({a : ZMod p | a ^ k = a} : Finset (ZMod p)) +
        #({a : ZMod p | a ^ k ≠ a} : Finset (ZMod p)) = #(Finset.univ : Finset (ZMod p)) :=
      Finset.card_filter_add_card_filter_not _
    rw [h, Finset.card_univ, ZMod.card p]
  have hg : Nat.gcd (p - 1) (k - 1) ≤ p - 1 :=
    Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  unfold frobDefect
  omega

/-- **The retraction criterion, in terms of the error count.**  In any field of characteristic
`p`, the Frobenius orbit product of degree `k` fixes the prime subfield pointwise — i.e. it is a
retraction onto `𝔽ₚ` — iff its error count `frobDefect p k` is zero. -/
theorem retraction_iff_frobDefect_eq_zero {K : Type*} [Field K] {p k : ℕ} [hp : Fact p.Prime]
    [CharP K p] (hk : k ≠ 0) :
    (∀ a ∈ Set.range (primeSubfieldHom K p), frobNorm p k a = a) ↔ frobDefect p k = 0 :=
  (WhyTwentySeven.frobNorm_eq_self_on_primeSubfield_iff hk).trans
    (frobDefect_eq_zero_iff hp.out).symm

/-! ### The scan `q = 2 … 97` -/

/-- One row of the scan: the candidate size `q`, together with `some (p, k, error)` when
`q = p ^ k` is a field size, and `none` when it is not. -/
def scanRow (q : ℕ) : ℕ × Option (ℕ × ℕ × ℕ) :=
  (q, (gfData q).map fun pk => (pk.1, pk.2, frobDefect pk.1 pk.2))

/-- The scan of all candidate sizes `q = 2, 3, …, 97`. -/
def fieldSizeScan : List (ℕ × Option (ℕ × ℕ × ℕ)) := (List.range' 2 96).map scanRow

/-- The sizes in `2 … 97` that are **not** field sizes (`gfData = none`): the hard errors of the
scan.  By `card_ne_of_gfData_eq_none` no finite field has any of these cardinalities. -/
theorem scan_no_field_sizes :
    (fieldSizeScan.filter fun r => r.2.isNone).map Prod.fst =
      [6, 10, 12, 14, 15, 18, 20, 21, 22, 24, 26, 28, 30, 33, 34, 35, 36, 38, 39, 40, 42, 44, 45,
       46, 48, 50, 51, 52, 54, 55, 56, 57, 58, 60, 62, 63, 65, 66, 68, 69, 70, 72, 74, 75, 76, 77,
       78, 80, 82, 84, 85, 86, 87, 88, 90, 91, 92, 93, 94, 95, 96] := by
  decide +kernel

/-- The field sizes `q = p ^ k ≤ 97` with error `0`, i.e. those for which the Frobenius orbit
product really is a retraction onto `𝔽ₚ`, listed as `(q, p, k)`: every prime (where the orbit
product is the identity map, `k = 1`), every power of `2`, and — the only other one below
`100` — `27`. -/
theorem scan_retractive_sizes :
    (fieldSizeScan.filterMap fun r =>
        match r.2 with
        | some (p, k, d) => if d = 0 then some (r.1, p, k) else none
        | none => none) =
      [(2, 2, 1), (3, 3, 1), (4, 2, 2), (5, 5, 1), (7, 7, 1), (8, 2, 3), (11, 11, 1), (13, 13, 1),
       (16, 2, 4), (17, 17, 1), (19, 19, 1), (23, 23, 1), (27, 3, 3), (29, 29, 1), (31, 31, 1),
       (32, 2, 5), (37, 37, 1), (41, 41, 1), (43, 43, 1), (47, 47, 1), (53, 53, 1), (59, 59, 1),
       (61, 61, 1), (64, 2, 6), (67, 67, 1), (71, 71, 1), (73, 73, 1), (79, 79, 1), (83, 83, 1),
       (89, 89, 1), (97, 97, 1)] := by
  decide +kernel

/-- The proper prime powers `q = p ^ k ≤ 97` (`k ≥ 2`) with error `0`: `4, 8, 16, 32, 64` in
characteristic `2` — where the retraction is degenerate, see
`WhyTwentySeven.frobNorm_eq_one_of_char_two` — and `27`. -/
theorem scan_retractive_proper_prime_powers :
    (fieldSizeScan.filterMap fun r =>
        match r.2 with
        | some (_, k, d) => if d = 0 ∧ 2 ≤ k then some r.1 else none
        | none => none) = [4, 8, 16, 27, 32, 64] := by
  decide +kernel

/-- The field sizes `q ≤ 97` with a **nonzero** error, listed as `(q, p, k, error)`: the orbit
product of `GF(9)` moves `1` of the `2` units of `𝔽₃`, that of `GF(25)` moves `3` of the `4`
units of `𝔽₅`, that of `GF(49)` moves `5` of the `6` units of `𝔽₇`, and that of `GF(81)` moves
`1` of the `2` units of `𝔽₃`. -/
theorem scan_failing_sizes :
    (fieldSizeScan.filterMap fun r =>
        match r.2 with
        | some (p, k, d) => if d ≠ 0 then some (r.1, p, k, d) else none
        | none => none) = [(9, 3, 2, 1), (25, 5, 2, 3), (49, 7, 2, 5), (81, 3, 4, 1)] := by
  decide +kernel

/-- Every candidate size in `2 … 97` falls into exactly one of three classes: not a field size
(61 values), a field size with a working retraction (31 values), or a field size with a nonzero
error (4 values). -/
theorem scan_partition_counts :
    (fieldSizeScan.filter fun r => r.2.isNone).length = 61 ∧
    (fieldSizeScan.filter fun r =>
        match r.2 with | some (_, _, d) => d == 0 | none => false).length = 31 ∧
    (fieldSizeScan.filter fun r =>
        match r.2 with | some (_, _, d) => d != 0 | none => false).length = 4 ∧
    fieldSizeScan.length = 96 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ### The companion scan: fixed characteristic, degrees `n = 2 … 97`

The scan above reads `2 … 97` as *sizes*.  Reading them instead as *degrees* over a fixed prime
field gives the periodic picture drawn in the lower panel of `svg/field-size-scan-degrees.svg`:
the error of `GF(p ^ n)` depends on `n` only through `n mod (p - 1)`, and vanishes exactly on
`n ≡ 1 mod (p - 1)`. -/

/-- The errors of `GF(p ^ n)` for the degrees `n = 2, …, 97` at a fixed characteristic `p`. -/
def degreeScan (p : ℕ) : List (ℕ × ℕ) := (List.range' 2 96).map fun k => (k, frobDefect p k)

/-- The error vanishes exactly on the congruence `n ≡ 1 mod (p - 1)`. -/
theorem frobDefect_eq_zero_iff_modEq {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    frobDefect p k = 0 ↔ k ≡ 1 [MOD p - 1] := by
  rw [frobDefect_eq_zero_iff hp, Nat.ModEq.comm, Nat.modEq_iff_dvd' hk]

/-- Characteristic `2`: the error is `0` in every degree — but degenerately, since `𝔽₂` has a
trivial unit group (`WhyTwentySeven.frobNorm_eq_one_of_char_two`). -/
theorem degreeScan_char_two : (degreeScan 2).all (fun r => r.2 == 0) = true := by decide +kernel

/-- Characteristic `3`: the error is `0` exactly in the odd degrees, and `1` otherwise. -/
theorem degreeScan_char_three :
    ((degreeScan 3).filter fun r => r.2 == 0).map Prod.fst =
      [3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47, 49,
       51, 53, 55, 57, 59, 61, 63, 65, 67, 69, 71, 73, 75, 77, 79, 81, 83, 85, 87, 89, 91, 93, 95,
       97] ∧
    (degreeScan 3).all (fun r => r.2 ≤ 1) = true := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- Characteristic `5`: the error is `0` exactly for `n ≡ 1 mod 4`, and is `2` or `3` otherwise. -/
theorem degreeScan_char_five :
    ((degreeScan 5).filter fun r => r.2 == 0).map Prod.fst =
      [5, 9, 13, 17, 21, 25, 29, 33, 37, 41, 45, 49, 53, 57, 61, 65, 69, 73, 77, 81, 85, 89, 93,
       97] ∧
    (degreeScan 5).all (fun r => r.2 ≤ 3) = true := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- Characteristic `7`: the error is `0` exactly for `n ≡ 1 mod 6`, and is `3`, `4` or `5`
otherwise. -/
theorem degreeScan_char_seven :
    ((degreeScan 7).filter fun r => r.2 == 0).map Prod.fst =
      [7, 13, 19, 25, 31, 37, 43, 49, 55, 61, 67, 73, 79, 85, 91, 97] ∧
    (degreeScan 7).all (fun r => r.2 ≤ 5) = true := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-! ### Testing the actual fields `GF(q)` for every proper prime power `q ≤ 97` -/

section GaloisFields

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The criterion, read on Mathlib's `GaloisField p k` (the field with `p ^ k` elements), in
terms of the error count. -/
theorem galoisField_retraction_iff_frobDefect (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) :
    (∀ a ∈ Set.range (primeSubfieldHom (GaloisField p k) p), frobNorm p k a = a) ↔
      frobDefect p k = 0 :=
  retraction_iff_frobDefect_eq_zero hk

/-- `GF(4)`: error `0`, a retraction (characteristic `2`). -/
theorem gf4_retractive :
    ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 2 2) 2), frobNorm 2 2 a = a :=
  (galoisField_retraction_iff_frobDefect 2 2 (by norm_num)).2 (by decide)

/-- `GF(8)`: error `0`, a retraction (characteristic `2`). -/
theorem gf8_retractive :
    ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 2 3) 2), frobNorm 2 3 a = a :=
  (galoisField_retraction_iff_frobDefect 2 3 (by norm_num)).2 (by decide)

/-- `GF(16)`: error `0`, a retraction (characteristic `2`). -/
theorem gf16_retractive :
    ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 2 4) 2), frobNorm 2 4 a = a :=
  (galoisField_retraction_iff_frobDefect 2 4 (by norm_num)).2 (by decide)

/-- `GF(32)`: error `0`, a retraction (characteristic `2`). -/
theorem gf32_retractive :
    ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 2 5) 2), frobNorm 2 5 a = a :=
  (galoisField_retraction_iff_frobDefect 2 5 (by norm_num)).2 (by decide)

/-- `GF(64)`: error `0`, a retraction (characteristic `2`). -/
theorem gf64_retractive :
    ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 2 6) 2), frobNorm 2 6 a = a :=
  (galoisField_retraction_iff_frobDefect 2 6 (by norm_num)).2 (by decide)

/-- `GF(27)`: error `0` — the only retraction in odd characteristic below `100`. -/
theorem gf27_retractive_scan :
    ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 3 3) 3), frobNorm 3 3 a = a :=
  (galoisField_retraction_iff_frobDefect 3 3 (by norm_num)).2 (by decide)

/-- `GF(9)`: error `1`, so no retraction. -/
theorem gf9_error_one :
    ¬ (∀ a ∈ Set.range (primeSubfieldHom (GaloisField 3 2) 3), frobNorm 3 2 a = a) ∧
      frobDefect 3 2 = 1 := by
  refine ⟨fun h => ?_, by decide⟩
  have hd := (galoisField_retraction_iff_frobDefect 3 2 (by norm_num)).1 h
  simp [frobDefect] at hd

/-- `GF(25)`: error `3` — the orbit product moves three of the four units of `𝔽₅`. -/
theorem gf25_error_three :
    ¬ (∀ a ∈ Set.range (primeSubfieldHom (GaloisField 5 2) 5), frobNorm 5 2 a = a) ∧
      frobDefect 5 2 = 3 := by
  refine ⟨fun h => ?_, by decide⟩
  have hd := (galoisField_retraction_iff_frobDefect 5 2 (by norm_num)).1 h
  simp [frobDefect] at hd

/-- `GF(49)`: error `5` — the worst failure below `100`. -/
theorem gf49_error_five :
    ¬ (∀ a ∈ Set.range (primeSubfieldHom (GaloisField 7 2) 7), frobNorm 7 2 a = a) ∧
      frobDefect 7 2 = 5 := by
  refine ⟨fun h => ?_, by decide⟩
  have hd := (galoisField_retraction_iff_frobDefect 7 2 (by norm_num)).1 h
  simp [frobDefect] at hd

/-- `GF(81)`: error `1`, so no retraction (odd degree of the wrong residue: `2 ∤ 3`). -/
theorem gf81_error_one :
    ¬ (∀ a ∈ Set.range (primeSubfieldHom (GaloisField 3 4) 3), frobNorm 3 4 a = a) ∧
      frobDefect 3 4 = 1 := by
  refine ⟨fun h => ?_, by decide⟩
  have hd := (galoisField_retraction_iff_frobDefect 3 4 (by norm_num)).1 h
  simp [frobDefect] at hd

end GaloisFields

end FieldSizeScan
