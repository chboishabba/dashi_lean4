import RequestProject.Frobenius

/-!
# Why `27`?  Which field sizes admit the Frobenius-norm retraction

The concrete field used elsewhere in this project is `GF(27) = 𝔽₃[t]/(t³ - t - 1)`, on which
the Frobenius orbit product

  `N(x) = x · x³ · x⁹ = x¹³`

is a retraction of `GF(27)` onto its prime subfield `𝔽₃`.  This file answers the question
*why that size, and what happens for other sizes*.

Two of the three phenomena are **size independent**:

* the fixed points of `x ↦ x ^ p` are the prime subfield `𝔽_p`, in *any* field of
  characteristic `p` (`FrobeniusPrimeSubfield.fixedPoints_frobenius_eq_range_zmod`);
* the orbit product `N` always lands in `𝔽_p` and is always *onto* `𝔽_p`
  (`FrobeniusPrimeSubfield.frobNorm_mem_primeSubfield`,
  `FrobeniusOrbitStructure.frobNorm_surjective_onto_primeSubfield`).

The third one — that `N` **fixes `𝔽_p` pointwise**, i.e. that `N` is a *retraction* and not
merely a surjection — is *not* size independent.  On `𝔽_p` the orbit product is the `n`-th
power map, so for `#K = pⁿ`:

* `frobNorm_eq_self_on_primeSubfield_iff` : `N` restricts to the identity on `𝔽_p`
  **iff `p - 1 ∣ n - 1`**.

Consequences (all proved below):

* characteristic `2`: the condition is vacuous, so `GF(4)`, `GF(8)`, `GF(16)`, … all work —
  but degenerately: there `N(x) = 1` for every `x ≠ 0` (`frobNorm_eq_one_of_char_two`),
  because the target `𝔽₂ = {0, 1}` has a trivial unit group.
* `GF(9)`, `GF(81)`, `GF(25)`, `GF(49)`, … fail: whenever `p` is odd and `n` is even,
  `N(-1) = 1 ≠ -1` (`frobNorm_neg_one_of_even`).
* `GF(125)` fails too (`5 - 1 = 4 ∤ 2 = 3 - 1`), even though `n = 3` is odd.
* `GF(27)` works (`3 - 1 = 2 ∣ 2 = 3 - 1`), and it is the **smallest** field of odd
  characteristic and degree `n ≥ 2` that does (`lt_27_not_retractive`,
  `twentySeven_is_least_odd_retractive`).  The next ones are `GF(3⁵) = GF(243)`,
  `GF(5⁵)`, `GF(7⁷)`, …

So `27` is not magic, but it is not arbitrary either: it is the smallest size for which the
Frobenius orbit product is a retraction onto a prime field with more than one unit.
-/

open Finset FrobeniusPrimeSubfield

namespace WhyTwentySeven

section General

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- **Necessity of the congruence `n ≡ 1 mod (p - 1)`.**
If the Frobenius orbit product `N(x) = ∏ k < n, x ^ (p ^ k)` fixes the prime subfield
pointwise, then `p - 1 ∣ n - 1`.  Indeed on `𝔽_p` the orbit product is `a ↦ aⁿ`, and a
generator of the cyclic group `𝔽_pˣ` (of order `p - 1`) is fixed only if `p - 1 ∣ n - 1`. -/
theorem dvd_of_frobNorm_eq_self_on_primeSubfield {n : ℕ} (hn : n ≠ 0)
    (h : ∀ a ∈ Set.range (primeSubfieldHom K p), frobNorm p n a = a) : p - 1 ∣ n - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  set f : ZMod p →+* K := primeSubfieldHom K p with hf
  have hinj : Function.Injective f := f.injective
  set a : K := f ((g : (ZMod p)ˣ) : ZMod p) with ha
  have hchar : a ^ p = a := (pow_char_eq_self_iff_mem_range_zmod a).2 ⟨_, rfl⟩
  have hself : a ^ n = a := by
    rw [← frobNorm_of_pow_char_eq_self (n := n) hchar]
    exact h a ⟨_, rfl⟩
  have ha0 : a ≠ 0 := by
    rw [ha]
    intro h0
    have : ((g : (ZMod p)ˣ) : ZMod p) = 0 := hinj (by simp [h0])
    exact (Units.ne_zero g) this
  have hpow : a ^ (n - 1) = 1 := by
    have : a ^ (n - 1) * a = 1 * a := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn), hself]
    exact mul_right_cancel₀ ha0 this
  have hzmod : ((g : (ZMod p)ˣ) : ZMod p) ^ (n - 1) = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact hpow
  have horder : orderOf ((g : (ZMod p)ˣ) : ZMod p) ∣ n - 1 := orderOf_dvd_of_pow_eq_one hzmod
  rw [orderOf_units] at horder
  rwa [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
    ZMod.card_units p] at horder

/-- **The exact condition on the field size.**  For a field `K` of characteristic `p` with
`p ^ n` elements (`n ≠ 0`), the Frobenius orbit product `N(x) = ∏ k < n, x ^ (p ^ k)`
restricts to the identity on the prime subfield `𝔽_p` — i.e. it is a *retraction* of `K`
onto `𝔽_p` — if and only if `p - 1 ∣ n - 1`.

Note that only the characteristic and the degree enter; the hypothesis `#K = p ^ n` is not
even needed for the equivalence. -/
theorem frobNorm_eq_self_on_primeSubfield_iff {n : ℕ} (hn : n ≠ 0) :
    (∀ a ∈ Set.range (primeSubfieldHom K p), frobNorm p n a = a) ↔ p - 1 ∣ n - 1 :=
  ⟨dvd_of_frobNorm_eq_self_on_primeSubfield hn, fun hdvd a hmem =>
    frobNorm_eq_self_of_pow_char_eq_self hn hdvd
      ((pow_char_eq_self_iff_mem_range_zmod a).2 hmem)⟩

/-- **Explicit failure witness for odd `p` and even `n`** (e.g. `GF(9)`, `GF(25)`, `GF(49)`,
`GF(81)`): the orbit product sends `-1` to `1`, so it does not fix the prime subfield. -/
theorem frobNorm_neg_one_of_even {n : ℕ} (hp2 : p ≠ 2) (hn : Even n) :
    frobNorm p n (-1 : K) = 1 ∧ frobNorm p n (-1 : K) ≠ (-1 : K) := by
  have hchar : (-1 : K) ^ p = -1 := by
    have hodd : Odd p := hp.out.odd_of_ne_two hp2
    exact hodd.neg_one_pow
  have hval : frobNorm p n (-1 : K) = 1 := by
    rw [frobNorm_of_pow_char_eq_self hchar, hn.neg_one_pow]
  refine ⟨hval, ?_⟩
  rw [hval]
  haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)⟩
  exact fun h => CharP.neg_one_ne_one K p h.symm

/-- **Characteristic `2` is degenerate.**  In a field with `2 ^ n` elements the orbit product
of every nonzero element is `1`: the retraction is onto `𝔽₂ = {0, 1}`, whose unit group is
trivial.  So `GF(4)`, `GF(8)`, `GF(16)`, … do satisfy the retraction condition, but nothing
interesting happens there. -/
theorem frobNorm_eq_one_of_char_two {K : Type*} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) {x : K} (hx : x ≠ 0) : frobNorm 2 n x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfix : (frobNorm 2 n x) ^ 2 = frobNorm 2 n x := frobNorm_pow_char hK x
  have h0 : frobNorm 2 n x ≠ 0 := frobNorm_ne_zero hx
  have : frobNorm 2 n x * (frobNorm 2 n x - 1) = 0 := by ring_nf; linear_combination hfix
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h h0
  · exact sub_eq_zero.1 h

end General

/-! ### Concrete field sizes

We instantiate the criterion on Mathlib's `GaloisField p n`, the field with `p ^ n` elements. -/

section Examples

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The criterion, read on the standard field `GF(p ^ n)`. -/
theorem galoisField_retraction_iff (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    (∀ a ∈ Set.range (primeSubfieldHom (GaloisField p n) p), frobNorm p n a = a) ↔
      p - 1 ∣ n - 1 :=
  frobNorm_eq_self_on_primeSubfield_iff hn

/-- **`GF(27)` works**: `N(x) = x · x³ · x⁹ = x¹³` fixes `𝔽₃` pointwise. -/
theorem gf27_retractive :
    ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 3 3) 3), frobNorm 3 3 a = a :=
  (galoisField_retraction_iff 3 3 (by norm_num)).2 (by norm_num)

/-- **`GF(9)` fails**: `N(x) = x · x³ = x⁴` does not fix `𝔽₃` pointwise. -/
theorem gf9_not_retractive :
    ¬ ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 3 2) 3), frobNorm 3 2 a = a := by
  rw [galoisField_retraction_iff 3 2 (by norm_num)]
  decide

/-- The explicit witness for the failure over `GF(9)`: `N(-1) = (-1)⁴ = 1 ≠ -1`. -/
theorem gf9_norm_neg_one :
    frobNorm 3 2 (-1 : GaloisField 3 2) = 1 ∧
      frobNorm 3 2 (-1 : GaloisField 3 2) ≠ (-1 : GaloisField 3 2) :=
  frobNorm_neg_one_of_even (by norm_num) (by norm_num)

/-- **`GF(81)` fails** (`p = 3`, `n = 4`: `2 ∤ 3`). -/
theorem gf81_not_retractive :
    ¬ ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 3 4) 3), frobNorm 3 4 a = a := by
  rw [galoisField_retraction_iff 3 4 (by norm_num)]
  decide

/-- **`GF(243) = GF(3⁵)` works**: after `27`, the next field of characteristic `3` on which the
orbit product is a retraction. -/
theorem gf243_retractive :
    ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 3 5) 3), frobNorm 3 5 a = a :=
  (galoisField_retraction_iff 3 5 (by norm_num)).2 (by norm_num)

/-- **`GF(25)` fails** (`p = 5`, `n = 2`: `4 ∤ 1`). -/
theorem gf25_not_retractive :
    ¬ ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 5 2) 5), frobNorm 5 2 a = a := by
  rw [galoisField_retraction_iff 5 2 (by norm_num)]
  decide

/-- **`GF(125)` fails** (`p = 5`, `n = 3`: `4 ∤ 2`) — odd degree is not enough. -/
theorem gf125_not_retractive :
    ¬ ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 5 3) 5), frobNorm 5 3 a = a := by
  rw [galoisField_retraction_iff 5 3 (by norm_num)]
  decide

/-- **`GF(5⁵) = GF(3125)` works** (`4 ∣ 4`). -/
theorem gf3125_retractive :
    ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 5 5) 5), frobNorm 5 5 a = a :=
  (galoisField_retraction_iff 5 5 (by norm_num)).2 (by norm_num)

/-- **`GF(49)` fails** (`p = 7`, `n = 2`: `6 ∤ 1`). -/
theorem gf49_not_retractive :
    ¬ ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 7 2) 7), frobNorm 7 2 a = a := by
  rw [galoisField_retraction_iff 7 2 (by norm_num)]
  decide

/-- **`GF(8)` works**, as does every field of characteristic `2` — but see
`frobNorm_eq_one_of_char_two` for why this is degenerate. -/
theorem gf8_retractive :
    ∀ a ∈ Set.range (primeSubfieldHom (GaloisField 2 3) 2), frobNorm 2 3 a = a :=
  (galoisField_retraction_iff 2 3 (by norm_num)).2 (by norm_num)

/-- **Every field of characteristic `2` works**: the condition `p - 1 ∣ n - 1` reads `1 ∣ n - 1`. -/
theorem char_two_always_retractive {K : Type*} [Field K] [CharP K 2] (n : ℕ) (hn : n ≠ 0) :
    ∀ a ∈ Set.range (primeSubfieldHom K 2), frobNorm 2 n a = a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (frobNorm_eq_self_on_primeSubfield_iff hn).2 (by simp)

end Examples

/-! ### `27` is the smallest odd size that works -/

section Minimality

/-- No field of odd characteristic with fewer than `27` elements and degree `n ≥ 2` satisfies the
retraction condition: the only candidates are `GF(9)` and `GF(25)`, and both fail. -/
theorem lt_27_not_retractive {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 ≤ n)
    (hlt : p ^ n < 27) : ¬ (p - 1 ∣ n - 1) := by
  intro hdvd
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  have h3 : 3 ^ n ≤ p ^ n := Nat.pow_le_pow_left hp3 n
  have hn2 : n = 2 := by
    by_contra hne
    have h3n : 3 ≤ n := by omega
    have h27 : 3 ^ 3 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h3n
    norm_num at h27
    omega
  subst hn2
  have hle : p - 1 ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- **Why `27`.**  `GF(27)` satisfies the retraction condition (`p - 1 = 2` divides `n - 1 = 2`),
and no smaller field of odd characteristic and degree `≥ 2` does.  Fields of characteristic `2`
satisfy it for trivial reasons (`frobNorm_eq_one_of_char_two`), so `27` is the smallest size for
which the Frobenius orbit product is a retraction onto a prime field with a nontrivial unit
group. -/
theorem twentySeven_is_least_odd_retractive :
    (3 : ℕ) ^ 3 = 27 ∧ (3 - 1 : ℕ) ∣ (3 - 1 : ℕ) ∧
      ∀ p n : ℕ, p.Prime → p ≠ 2 → 2 ≤ n → p ^ n < 27 → ¬ (p - 1 ∣ n - 1) :=
  ⟨by norm_num, dvd_refl _, fun _ _ hp hp2 hn hlt => lt_27_not_retractive hp hp2 hn hlt⟩

/-- The prime powers `p ^ n ≤ 256` with `n ≥ 2` on which the Frobenius orbit product is a
retraction onto the prime subfield: `4, 8, 16, 32, 64, 128, 256` in characteristic `2`, and
only `27` and `243` in odd characteristic.  (Primes `p ≥ 17` are excluded because already
`p ^ 2 > 256`.) -/
theorem retractive_sizes_upto_256 :
    ((([2, 3, 5, 7, 11, 13] : List ℕ).flatMap
        (fun p => (List.range 9).map (fun n => (p, n)))).filter
      (fun pn => 2 ≤ pn.2 && pn.1 ^ pn.2 ≤ 256 && decide (pn.1 - 1 ∣ pn.2 - 1))).map
      (fun pn => pn.1 ^ pn.2) = [4, 8, 16, 32, 64, 128, 256, 27, 243] := by
  decide

end Minimality

end WhyTwentySeven
