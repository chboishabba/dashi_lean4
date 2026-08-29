import RequestProject.OtherFieldSizes
import RequestProject.FrobeniusTrace
import RequestProject.BigFieldSizeScan

/-!
# The smallest error, and how to repair it: `GF(9)`

Elsewhere in this project the Frobenius orbit product

`N(x) = x · x^p · ⋯ · x^(p^(k-1))`

of a field `GF(p^k)` is shown to land in the prime subfield `𝔽ₚ` and to be onto it, but to
fix `𝔽ₚ` pointwise — i.e. to be a genuine *retraction* — only when `p - 1 ∣ k - 1`.  The
number of points of `𝔽ₚ` that it moves is the error
`frobDefect p k = (p - 1) - gcd (p - 1) (k - 1)`.

This file takes the **smallest nonzero error** and works it out completely.

* `bigScan_min_error` : over the whole scanned range `q = 2 … 1824` the smallest nonzero
  error is `1`, attained exactly at `q = 9, 81, 729`; the smallest failing field size is
  therefore `q = 9 = 3²`, which is the case studied here.
* `GF9.error_card`, `GF9.error_point` : in `GF(9)` the orbit product `N(x) = x · x³ = x⁴`
  moves exactly one point of `𝔽₃`, namely `2`, with `N(2) = 1`.

**The multiplicative error cannot be repaired.**  The obstruction is not the particular
choice of `N`: it is that `-1 = 2` is a square in `GF(9)` (namely `(1+t)² = 2`) but not a
square in `𝔽₃`.

* `FrobeniusRepair.multiplicative_map_ne_of_sq` : *no* multiplicative map `K → K` taking
  values in the prime subfield can fix an element of the prime subfield which is a square in
  `K` but not a square in the prime subfield.
* `GF9.no_multiplicative_repair` : hence no multiplicative map `GF(9) → GF(9)` with values in
  `𝔽₃` is a retraction — in particular no adjusted power `x ↦ x^m` is
  (`GF9.no_power_repair`), and the failure of `N` at `2` is recovered abstractly
  (`GF9.norm_ne_two`).
* The obstruction is general: for `#K = p^k` with `p` odd and `k` even, every element of the
  prime subfield is a square in `K` (`FrobeniusRepair.isSquare_of_pow_char_eq_self`), while
  `𝔽ₚ` itself has a non-square, so no multiplicative map into `𝔽ₚ` fixes `𝔽ₚ` pointwise
  (`FrobeniusRepair.no_multiplicative_retraction_of_even_degree`).

**The additive error can be repaired.**  The additive orbit sum (the trace)
`T(x) = x + x³` also fails to fix `𝔽₃` — it is `a ↦ 2a` there, moving *two* points, a worse
error than `N`'s — but this failure is a single scalar, and dividing it out repairs the map:

* `GF9.repair x = 2 * (x + x³)` (note `2 = 2⁻¹` in `𝔽₃`) is additive
  (`GF9.repair_add`), `𝔽₃`-linear (`GF9.repair_smul`), takes values in `𝔽₃`
  (`GF9.repair_mem_primeSubfield`), is onto `𝔽₃` (`GF9.repair_surjective`), fixes `𝔽₃`
  pointwise (`GF9.repair_id_on_primeSubfield`) and is idempotent (`GF9.repair_idempotent`):
  **a genuine retraction of `GF(9)` onto `𝔽₃`** (`GF9.repair_isRetraction`).
* `GF9.repair_eq_normalized_frobTrace` identifies it with the general normalized orbit sum
  `x ↦ (k : K)⁻¹ * ∑_{i<k} x^(p^i)` of `RequestProject/FrobeniusTrace.lean`, and
  `GF9.repair_retraction_abstract` is the corresponding abstract statement.
* `GF9.repair_not_multiplicative` : it is not multiplicative — as it cannot be, by the
  obstruction above.  Repairing the error costs exactly the multiplicative structure.

Both halves together are `FrobeniusRepair.repair_dichotomy`: for `#K = p^k` with `p` odd,
`k` even and `p ∤ k`, the multiplicative error can never be repaired while the additive one
always can.  `GF(9)` is the smallest instance, and the two statements are checked on
Mathlib's own field of order `9` as well (`GaloisFieldNine.no_multiplicative_repair`,
`GaloisFieldNine.trace_repair`).

The picture `svg/gf9-error-repair.svg`, drawn by `RequestProject/RepairVisualization.lean`,
shows the broken map and the repaired one side by side.
-/

set_option maxHeartbeats 1000000

open Finset

/-! ## The smallest error in the scanned range -/

namespace BigFieldSizeScan

/-- Over the scanned range `q = 2 … 1824` the smallest nonzero error is `1`, and it occurs
exactly at `q = 9, 81, 729` (all of characteristic `3`).  So `q = 9` is the smallest field
size whose Frobenius orbit product is not a retraction, and its error is the smallest one
that occurs at all. -/
theorem bigScan_min_error :
    (bigScan.filterMap fun r =>
        match r.2 with
        | some (_, _, d) => if 1 ≤ d ∧ d ≤ 1 then some r.1 else none
        | none => none) = [9, 81, 729] ∧
    (bigScan.filterMap fun r =>
        match r.2 with
        | some (_, _, d) => if 1 ≤ d then some r.1 else none
        | none => none).head? = some 9 := by
  refine ⟨by decide +kernel, by decide +kernel⟩

end BigFieldSizeScan

/-! ## The obstruction: a multiplicative repair is impossible -/

namespace FrobeniusRepair

/-- **No multiplicative map with values in the prime subfield can fix a "hidden square".**

If `a` is a square in `K`, say `a = b * b`, but is not the square of any Frobenius-fixed
element (i.e. not a square inside the prime subfield), then every multiplicative
`f : K → K` whose values are Frobenius-fixed moves `a`.  Indeed `f a = f b * f b` is then a
square of a Frobenius-fixed element, so it cannot equal `a`. -/
theorem multiplicative_map_ne_of_sq {K : Type*} [Field K] {p : ℕ} {f : K → K}
    (hmul : ∀ x y, f (x * y) = f x * f y) (hfix : ∀ x, (f x) ^ p = f x)
    {a b : K} (hb : b * b = a) (hns : ∀ c : K, c ^ p = c → c * c ≠ a) :
    f a ≠ a := by
  intro h
  exact hns (f b) (hfix b) (by rw [← hmul, hb, h])

/-! ### The obstruction in general: odd characteristic and even degree -/

open FrobeniusPrimeSubfield

section General

variable {K : Type*} [Field K] [Finite K] {p k : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- For `p` odd and `k` even, **every** element of the prime subfield of `GF(p^k)` is a square
in `GF(p^k)`: an element of `𝔽ₚˣ` is killed by `p - 1`, and `2 (p - 1)` divides `p^k - 1`. -/
theorem isSquare_of_pow_char_eq_self (hK : Nat.card K = p ^ k) (hodd : p ≠ 2) (heven : Even k)
    {a : K} (ha : a ^ p = a) (ha0 : a ≠ 0) : IsSquare a := by
  obtain ⟨m, hm⟩ := heven
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = p ^ k := by rwa [← Nat.card_eq_fintype_card]
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hodd
  have hpodd : Odd p := hp.out.odd_of_ne_two hodd
  -- `a ^ (p - 1) = 1`
  have hpow : a ^ (p - 1) = 1 := by
    obtain ⟨u, rfl⟩ := (pow_char_eq_self_iff_mem_range_zmod a).1 ha
    have hu : u ≠ 0 := fun h => ha0 (by rw [h, map_zero])
    rw [← map_pow, ZMod.pow_card_sub_one_eq_one hu, map_one]
  -- `2 * (p - 1)` divides `p ^ k - 1`
  have hpm : 1 ≤ p ^ m := Nat.one_le_pow _ _ hp.out.pos
  have hsq : ∀ n : ℕ, 1 ≤ n → n * n - 1 = (n - 1) * (n + 1) := by
    intro n hn1
    obtain ⟨c, rfl⟩ : ∃ c, n = c + 1 := ⟨n - 1, by omega⟩
    have h1 : (c + 1) * (c + 1) = c * (c + 2) + 1 := by ring
    simp [h1]
  have hfact : p ^ k - 1 = (p ^ m - 1) * (p ^ m + 1) := by
    have hk2 : p ^ k = p ^ m * p ^ m := by rw [hm, ← pow_add]
    rw [hk2, hsq (p ^ m) hpm]
  have hd1 : (p - 1) ∣ p ^ m - 1 := Nat.sub_one_dvd_pow_sub_one p m
  have hd2 : 2 ∣ p ^ m + 1 := by
    obtain ⟨j, hj⟩ := hpodd.pow (n := m)
    omega
  have hdvd : 2 * (p - 1) ∣ p ^ k - 1 := by
    rw [hfact, mul_comm 2 (p - 1)]
    exact mul_dvd_mul hd1 hd2
  -- hence `a ^ (#K / 2) = 1`, which is Euler's criterion
  have hpk1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.out.pos
  obtain ⟨t, ht⟩ := hdvd
  rw [mul_assoc] at ht
  have hhalf : Fintype.card K / 2 = (p - 1) * t := by
    rw [hcard]; omega
  rw [FiniteField.isSquare_iff hchar ha0, hhalf, pow_mul, hpow, one_pow]

/-- **No multiplicative repair in odd characteristic and even degree.**  If `#K = p ^ k` with
`p` odd and `k` even, then every multiplicative map `f : K → K` whose values lie in the prime
subfield moves some point of the prime subfield: there is no multiplicative retraction of `K`
onto `𝔽ₚ`, no matter how the orbit product is adjusted.

The reason is `isSquare_of_pow_char_eq_self`: in this situation every element of `𝔽ₚˣ` is a
square in `K`, while `𝔽ₚˣ` itself, being cyclic of even order `p - 1`, contains a
non-square. -/
theorem no_multiplicative_retraction_of_even_degree (hK : Nat.card K = p ^ k) (hodd : p ≠ 2)
    (heven : Even k) {f : K → K} (hmul : ∀ x y, f (x * y) = f x * f y)
    (hfix : ∀ x, (f x) ^ p = f x) :
    ∃ a : K, a ^ p = a ∧ f a ≠ a := by
  have hchar3 : ringChar (ZMod p) ≠ 2 := by
    rw [ringChar.eq (ZMod p) p]
    exact hodd
  obtain ⟨u, hu⟩ := FiniteField.exists_nonsquare (F := ZMod p) hchar3
  set a : K := primeSubfieldHom K p u with hadef
  have ha : a ^ p = a := (pow_char_eq_self_iff_mem_range_zmod a).2 ⟨u, rfl⟩
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hu ⟨0, by simp⟩
  have ha0 : a ≠ 0 := fun h => hu0 (by
    have := (map_eq_zero_iff (primeSubfieldHom K p) (primeSubfieldHom K p).injective).1 h
    exact this)
  -- `a` is a square in `K`, but not a square inside the prime subfield
  obtain ⟨b, hb⟩ := isSquare_of_pow_char_eq_self hK hodd heven ha ha0
  have hns : ∀ c : K, c ^ p = c → c * c ≠ a := by
    intro c hc hca
    obtain ⟨y, rfl⟩ := (pow_char_eq_self_iff_mem_range_zmod c).1 hc
    rw [hadef, ← map_mul] at hca
    exact hu ⟨y, ((primeSubfieldHom K p).injective hca).symm⟩
  exact ⟨a, ha, multiplicative_map_ne_of_sq hmul hfix hb.symm hns⟩

/-- **The dichotomy.**  For `#K = p ^ k` with `p` odd, `k` even and `p ∤ k`:
the *multiplicative* error can never be repaired, while the *additive* one always can — the
normalized orbit sum `x ↦ (k : K)⁻¹ * ∑_{i<k} x^(p^i)` is an additive retraction onto `𝔽ₚ`.
`GF(9)` is the smallest instance. -/
theorem repair_dichotomy (hK : Nat.card K = p ^ k) (hodd : p ≠ 2) (heven : Even k)
    (hpk : ¬ p ∣ k) :
    (∀ f : K → K, (∀ x y, f (x * y) = f x * f y) → (∀ x, (f x) ^ p = f x) →
        ∃ a : K, a ^ p = a ∧ f a ≠ a) ∧
      ((∀ x y : K, (k : K)⁻¹ * frobTrace p k (x + y)
          = (k : K)⁻¹ * frobTrace p k x + (k : K)⁻¹ * frobTrace p k y) ∧
        (∀ x : K, (k : K)⁻¹ * frobTrace p k x ∈ Set.range (primeSubfieldHom K p)) ∧
        (∀ a ∈ Set.range (primeSubfieldHom K p), (k : K)⁻¹ * frobTrace p k a = a) ∧
        (∀ a ∈ Set.range (primeSubfieldHom K p), ∃ x : K, (k : K)⁻¹ * frobTrace p k x = a)) :=
  haveI : Fintype K := Fintype.ofFinite K
  ⟨fun _ hmul hfix => no_multiplicative_retraction_of_even_degree hK hodd heven hmul hfix,
    frobTrace_retraction_onto_primeSubfield hK hpk⟩

end General

end FrobeniusRepair

namespace GF9

/-! ## The error of the orbit product on `GF(9)` -/

/-- The orbit product of `GF(9)`: `N(x) = x · x³ = x⁴`. -/
def norm4 (x : GF9) : GF9 := x ^ 4

/-- The elements of the prime subfield `𝔽₃ ⊆ GF(9)` are those with vanishing `t`-coordinate;
`primeSubfieldFinset` lists them. -/
def primeSubfieldFinset : Finset GF9 := univ.filter (fun x => x.c1 = 0)

theorem primeSubfieldFinset_card : primeSubfieldFinset.card = 3 := by decide

/-- **The error of `GF(9)`: the orbit product moves exactly one point of `𝔽₃`.** -/
theorem error_card :
    (primeSubfieldFinset.filter (fun x => norm4 x ≠ x)).card = 1 := by decide

/-- The single moved point is `2`, and it is sent to `1`. -/
theorem error_point :
    primeSubfieldFinset.filter (fun x => norm4 x ≠ x) = {(⟨2, 0⟩ : GF9)} ∧
      norm4 (⟨2, 0⟩ : GF9) = 1 := by
  refine ⟨by decide, by decide⟩

/-- The error count matches the general formula `frobDefect p k = (p-1) - gcd(p-1, k-1)`
at `p = 3`, `k = 2`. -/
theorem error_eq_frobDefect :
    (primeSubfieldFinset.filter (fun x => norm4 x ≠ x)).card = FieldSizeScan.frobDefect 3 2 := by
  decide

/-! ### Why the error cannot be repaired multiplicatively -/

/-- `2 = -1` is a square in `GF(9)`: `(1 + t)² = 2`. -/
theorem sq_one_add_t : (⟨1, 1⟩ : GF9) * ⟨1, 1⟩ = 2 := by decide

/-- …but `2` is not a square in the prime subfield `𝔽₃`. -/
theorem not_sq_in_primeSubfield : ∀ c : GF9, c ^ 3 = c → c * c ≠ 2 := by decide

/-- **No multiplicative repair exists.**  Every multiplicative map `f : GF(9) → GF(9)` whose
values lie in the prime subfield `𝔽₃` moves the point `2`; so no such map is a retraction of
`GF(9)` onto `𝔽₃`.  The obstruction is that `2 = -1` is a square in `GF(9)` but not in `𝔽₃`
(`sq_one_add_t`, `not_sq_in_primeSubfield`): the multiplicative group `GF(9)ˣ ≅ ℤ/8` is
cyclic, and its subgroup `𝔽₃ˣ ≅ ℤ/2` sits inside the squares, so it is not a retract. -/
theorem no_multiplicative_repair {f : GF9 → GF9} (hmul : ∀ x y, f (x * y) = f x * f y)
    (hfix : ∀ x, (f x) ^ 3 = f x) : f 2 ≠ 2 :=
  FrobeniusRepair.multiplicative_map_ne_of_sq hmul hfix sq_one_add_t not_sq_in_primeSubfield

/-- In particular no adjusted power `x ↦ x^m` repairs the error: if it lands in `𝔽₃` it
still moves `2`. -/
theorem no_power_repair (m : ℕ) (hfix : ∀ x : GF9, (x ^ m) ^ 3 = x ^ m) :
    (2 : GF9) ^ m ≠ 2 :=
  no_multiplicative_repair (f := fun x => x ^ m) (fun x y => mul_pow x y m) hfix

/-- The failure of the orbit product itself, recovered from the obstruction rather than by
enumeration: `N(2) ≠ 2`. -/
theorem norm_ne_two : norm4 2 ≠ 2 :=
  no_power_repair 4 (by decide)

/-! ## The repair: the normalized additive orbit sum -/

/-- The additive orbit sum (trace) of `GF(9)`: `T(x) = x + x³`. -/
def trace2 (x : GF9) : GF9 := x + x ^ 3

/-- On the prime subfield the raw orbit sum is `a ↦ 2a`, so it moves **two** points of `𝔽₃` —
a bigger error than the orbit product's.  But it is a single scalar factor, and that is what
makes it repairable. -/
theorem trace2_on_primeSubfield : ∀ x : GF9, x.c1 = 0 → trace2 x = 2 * x := by decide

theorem trace2_error_card :
    (primeSubfieldFinset.filter (fun x => trace2 x ≠ x)).card = 2 := by decide

/-- **The repaired map**: `x ↦ 2⁻¹ · (x + x³) = 2 · (x + x³)`, since `2⁻¹ = 2` in `𝔽₃`. -/
def repair (x : GF9) : GF9 := 2 * (x + x ^ 3)

theorem two_inv_eq_two : (2 : GF9)⁻¹ = 2 := by decide

theorem repair_eq_trace2 (x : GF9) : repair x = (2 : GF9)⁻¹ * trace2 x := by
  rw [two_inv_eq_two]; rfl

/-- The repaired map takes values in the prime subfield `𝔽₃`. -/
theorem repair_mem_primeSubfield (x : GF9) : (repair x).c1 = 0 := by revert x; decide

/-- **It fixes `𝔽₃` pointwise — the retraction property that `N` failed.** -/
theorem repair_id_on_primeSubfield (x : GF9) (hx : x.c1 = 0) : repair x = x := by
  revert x; decide

/-- It is onto `𝔽₃`. -/
theorem repair_surjective (a : GF9) (ha : a.c1 = 0) : ∃ x : GF9, repair x = a :=
  ⟨a, repair_id_on_primeSubfield a ha⟩

/-- It is idempotent, so it really is a retraction onto its image. -/
theorem repair_idempotent (x : GF9) : repair (repair x) = repair x := by revert x; decide

/-- It is additive. -/
theorem repair_add (x y : GF9) : repair (x + y) = repair x + repair y := by
  revert x y; decide

/-- It is `𝔽₃`-linear. -/
theorem repair_smul (a x : GF9) (ha : a.c1 = 0) : repair (a * x) = a * repair x := by
  revert a x; decide

/-- **The repaired map is a retraction of `GF(9)` onto `𝔽₃`**: additive, `𝔽₃`-linear, with
image exactly `𝔽₃`, and the identity there.  The error `1` of the orbit product has been
corrected. -/
theorem repair_isRetraction :
    (∀ x y : GF9, repair (x + y) = repair x + repair y) ∧
    (∀ a x : GF9, a.c1 = 0 → repair (a * x) = a * repair x) ∧
    (∀ x : GF9, (repair x).c1 = 0) ∧
    (∀ a : GF9, a.c1 = 0 → ∃ x : GF9, repair x = a) ∧
    (∀ a : GF9, a.c1 = 0 → repair a = a) ∧
    (primeSubfieldFinset.filter (fun x => repair x ≠ x)).card = 0 :=
  ⟨repair_add, fun a x ha => repair_smul a x ha, repair_mem_primeSubfield,
    fun a ha => repair_surjective a ha, fun a ha => repair_id_on_primeSubfield a ha, by decide⟩

/-- The price of the repair: the corrected map is no longer multiplicative.  By
`no_multiplicative_repair` no repair could have been. -/
theorem repair_not_multiplicative : ¬ ∀ x y : GF9, repair (x * y) = repair x * repair y := by
  decide

/-! ### Identification with the general normalized orbit sum -/

open FrobeniusPrimeSubfield

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

theorem frobTrace_eq_trace2 (x : GF9) : frobTrace 3 2 x = trace2 x := by
  simp [frobTrace, Finset.sum_range_succ, trace2]

/-- The repaired map is exactly the normalized Frobenius orbit sum
`x ↦ (k : K)⁻¹ * ∑_{i<k} x^(p^i)` of `RequestProject/FrobeniusTrace.lean`, for `p = 3`,
`k = 2`. -/
theorem repair_eq_normalized_frobTrace (x : GF9) :
    repair x = ((2 : ℕ) : GF9)⁻¹ * frobTrace 3 2 x := by
  rw [frobTrace_eq_trace2, repair_eq_trace2]
  norm_num

/-- The abstract form of the repair, obtained from the general theorem: since `3 ∤ 2`, the
normalized orbit sum is an additive retraction of `GF(9)` onto the prime subfield. -/
theorem repair_retraction_abstract :
    (∀ x y : GF9, ((2 : ℕ) : GF9)⁻¹ * frobTrace 3 2 (x + y)
        = ((2 : ℕ) : GF9)⁻¹ * frobTrace 3 2 x + ((2 : ℕ) : GF9)⁻¹ * frobTrace 3 2 y) ∧
      (∀ x : GF9, ((2 : ℕ) : GF9)⁻¹ * frobTrace 3 2 x ∈ Set.range (primeSubfieldHom GF9 3)) ∧
      (∀ a ∈ Set.range (primeSubfieldHom GF9 3),
        ((2 : ℕ) : GF9)⁻¹ * frobTrace 3 2 a = a) ∧
      (∀ a ∈ Set.range (primeSubfieldHom GF9 3),
        ∃ x : GF9, ((2 : ℕ) : GF9)⁻¹ * frobTrace 3 2 x = a) :=
  frobTrace_retraction_onto_primeSubfield card_eq (by decide)

end GF9

/-! ## The same, on Mathlib's own field of order `9` -/

namespace GaloisFieldNine

open FrobeniusPrimeSubfield FrobeniusRepair

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

theorem card : Nat.card (GaloisField 3 2) = 3 ^ 2 := GaloisField.card 3 2 (by norm_num)

noncomputable local instance : Fintype (GaloisField 3 2) := Fintype.ofFinite _

/-- On `GaloisField 3 2` too, no multiplicative map into the prime subfield is a retraction:
some point of `𝔽₃` is always moved. -/
theorem no_multiplicative_repair {f : GaloisField 3 2 → GaloisField 3 2}
    (hmul : ∀ x y, f (x * y) = f x * f y) (hfix : ∀ x, (f x) ^ 3 = f x) :
    ∃ a : GaloisField 3 2, a ^ 3 = a ∧ f a ≠ a :=
  no_multiplicative_retraction_of_even_degree card (by norm_num) ⟨1, rfl⟩ hmul hfix

/-- …while the normalized additive orbit sum `x ↦ 2⁻¹ (x + x³)` is a retraction onto `𝔽₃`. -/
theorem trace_repair :
    (∀ x y : GaloisField 3 2, ((2 : ℕ) : GaloisField 3 2)⁻¹ * frobTrace 3 2 (x + y)
        = ((2 : ℕ) : GaloisField 3 2)⁻¹ * frobTrace 3 2 x
          + ((2 : ℕ) : GaloisField 3 2)⁻¹ * frobTrace 3 2 y) ∧
      (∀ x : GaloisField 3 2, ((2 : ℕ) : GaloisField 3 2)⁻¹ * frobTrace 3 2 x
        ∈ Set.range (primeSubfieldHom (GaloisField 3 2) 3)) ∧
      (∀ a ∈ Set.range (primeSubfieldHom (GaloisField 3 2) 3),
        ((2 : ℕ) : GaloisField 3 2)⁻¹ * frobTrace 3 2 a = a) ∧
      (∀ a ∈ Set.range (primeSubfieldHom (GaloisField 3 2) 3),
        ∃ x : GaloisField 3 2, ((2 : ℕ) : GaloisField 3 2)⁻¹ * frobTrace 3 2 x = a) :=
  frobTrace_retraction_onto_primeSubfield card (by decide)

end GaloisFieldNine
