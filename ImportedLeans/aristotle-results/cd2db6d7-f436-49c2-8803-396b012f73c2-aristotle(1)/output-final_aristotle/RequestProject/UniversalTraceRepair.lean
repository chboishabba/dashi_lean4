import RequestProject.FrobeniusTrace

/-!
# Every error can be repaired additively: the twisted trace

`RequestProject/GF9Repair.lean` repaired the smallest error of the scan by *normalizing* the
Frobenius orbit sum: `x ↦ (k : K)⁻¹ · Tr(x)`, where `Tr(x) = ∑_{i<k} x^(p^i)`.  That trick
needs `p ∤ k`, because on the prime subfield the raw orbit sum is the scalar `a ↦ k·a`, and
when `p ∣ k` that scalar is `0`: the orbit sum annihilates `𝔽ₚ` and *no* rescaling can bring
it back (`frobTrace_eq_zero_of_dvd`, `no_scalar_repair_of_dvd`).  The smallest field size in
the scan where this happens is `q = 729 = 3⁶`.

The repair that always works twists the *argument* instead of the value:

`R_c(x) = Tr(c · x)`  for any `c` with `Tr(c) = 1`.

Such a `c` exists for every finite field, because the orbit sum is onto the prime subfield
(`exists_trace_eq_one`).  The resulting map is additive, `𝔽ₚ`-linear, takes values in `𝔽ₚ`,
is onto `𝔽ₚ` and fixes it pointwise: a genuine retraction
(`twistedTrace_isRetraction`), for **every** prime power `p^k`, with no side condition at
all.  When `p ∤ k` one may take `c = (k : K)⁻¹` and recovers the normalized orbit sum
(`twistedTrace_inv_natCast_eq_normalized`), so the earlier repair is the special case
`c = k⁻¹` of this one.

So on the additive side the error is *always* correctable, and the picture is complete: the
18 failing sizes of the scan `q = 2 … 1824` — including `729`, which the normalization cannot
reach — all admit an additive retraction onto their prime subfield.  On the multiplicative
side the situation is different and is settled in
`RequestProject/MultiplicativeRepairIff.lean`.
-/

namespace FrobeniusPrimeSubfield

open Finset

variable {K : Type*} [Field K] {p n : ℕ} [hp : Fact p.Prime] [CharP K p]

/-! ## When `p ∣ n` the orbit sum kills the prime subfield -/

omit hp in
/-- If `p ∣ n` then the Frobenius orbit sum vanishes on the prime subfield: there it is the
scalar `a ↦ n·a = 0`. -/
theorem frobTrace_eq_zero_of_dvd (hpn : p ∣ n) {a : K} (ha : a ^ p = a) :
    frobTrace p n a = 0 := by
  rw [frobTrace_of_pow_char_eq_self ha]
  have : (n : K) = 0 := (CharP.cast_eq_zero_iff K p n).2 hpn
  rw [this, zero_mul]

omit hp in
/-- **When `p ∣ n`, no rescaling of the orbit sum repairs the error.**  For every scalar `c`
the map `x ↦ c · Tr(x)` sends the whole prime subfield to `0`, so it does not fix `1`. -/
theorem no_scalar_repair_of_dvd (hpn : p ∣ n) (c : K) :
    c * frobTrace p n (1 : K) ≠ 1 := by
  rw [frobTrace_eq_zero_of_dvd hpn (one_pow p), mul_zero]
  exact zero_ne_one

/-! ## The twisted trace -/

/-- The trace twisted by a scalar: `R_c(x) = Tr(c · x)`.  For a suitable `c` this is the
universal additive repair of the Frobenius orbit sum. -/
def twistedTrace (p n : ℕ) (c x : K) : K := frobTrace p n (c * x)

/-- When `p ∤ n` one may take `c = (n : K)⁻¹`, and then the twisted trace is exactly the
normalized orbit sum of `RequestProject/FrobeniusTrace.lean`: the earlier repair is the
special case `c = n⁻¹` of the universal one. -/
theorem twistedTrace_inv_natCast_eq_normalized (hpn : ¬ p ∣ n) (x : K) :
    twistedTrace p n ((n : K)⁻¹) x = (n : K)⁻¹ * frobTrace p n x := by
  have hn0 : (n : K) ≠ 0 := fun h => hpn ((CharP.cast_eq_zero_iff K p n).1 h)
  have hnF : (n : K) ∈ fixedSubfield K p 1 := by
    rw [mem_fixedSubfield, pow_one, ← map_natCast (primeSubfieldHom K p) n, ← map_pow,
      ZMod.pow_card]
  have hninv : ((n : K)⁻¹) ^ p = (n : K)⁻¹ := by
    have h := inv_mem hnF
    rw [mem_fixedSubfield, pow_one] at h
    exact h
  exact frobTrace_smul_of_pow_char_eq_self hninv x

/-- And in that case `Tr((n : K)⁻¹) = 1`, so `c = n⁻¹` really is a legitimate twist. -/
theorem frobTrace_inv_natCast (hpn : ¬ p ∣ n) : frobTrace p n ((n : K)⁻¹) = 1 := by
  have hn0 : (n : K) ≠ 0 := fun h => hpn ((CharP.cast_eq_zero_iff K p n).1 h)
  have h := twistedTrace_inv_natCast_eq_normalized (K := K) hpn 1
  rw [twistedTrace, mul_one] at h
  rw [h, frobTrace_of_pow_char_eq_self (one_pow p), mul_one, inv_mul_cancel₀ hn0]

variable [Fintype K]

/-- **A twisting scalar always exists**: since the orbit sum is onto the prime subfield, some
`c ∈ K` has `Tr(c) = 1`. -/
theorem exists_trace_eq_one (hK : Nat.card K = p ^ n) (hn : n ≠ 0) :
    ∃ c : K, frobTrace p n c = 1 := by
  have h1 : (1 : K) ∈ Set.range (primeSubfieldHom K p) := ⟨1, map_one _⟩
  rw [← frobTrace_range_eq_primeSubfield hK hn] at h1
  exact h1

/-- **The twisted trace is an additive retraction onto the prime subfield** — always, with no
hypothesis on `p` and `n` beyond `n ≠ 0`.  It is additive, `𝔽ₚ`-linear, has values in `𝔽ₚ`,
fixes `𝔽ₚ` pointwise, and is onto `𝔽ₚ`. -/
theorem twistedTrace_isRetraction (hK : Nat.card K = p ^ n) {c : K}
    (hc : frobTrace p n c = 1) :
    (∀ x y : K, twistedTrace p n c (x + y)
        = twistedTrace p n c x + twistedTrace p n c y) ∧
      (∀ a x : K, a ^ p = a → twistedTrace p n c (a * x) = a * twistedTrace p n c x) ∧
      (∀ x : K, twistedTrace p n c x ∈ Set.range (primeSubfieldHom K p)) ∧
      (∀ a ∈ Set.range (primeSubfieldHom K p), twistedTrace p n c a = a) ∧
      (∀ a ∈ Set.range (primeSubfieldHom K p), ∃ x : K, twistedTrace p n c x = a) := by
  have hlin : ∀ a x : K, a ^ p = a → twistedTrace p n c (a * x) = a * twistedTrace p n c x := by
    intro a x ha
    show frobTrace p n (c * (a * x)) = a * frobTrace p n (c * x)
    rw [show c * (a * x) = a * (c * x) by ring, frobTrace_smul_of_pow_char_eq_self ha]
  have hid : ∀ a ∈ Set.range (primeSubfieldHom K p), twistedTrace p n c a = a := by
    rintro a ha
    have hpa : a ^ p = a := (pow_char_eq_self_iff_mem_range_zmod a).2 ha
    show frobTrace p n (c * a) = a
    rw [mul_comm, frobTrace_smul_of_pow_char_eq_self hpa, hc, mul_one]
  refine ⟨fun x y => ?_, hlin, fun x => frobTrace_mem_primeSubfield hK _, hid,
    fun a ha => ⟨a, hid a ha⟩⟩
  show frobTrace p n (c * (x + y)) = frobTrace p n (c * x) + frobTrace p n (c * y)
  rw [mul_add, frobTrace_add]

/-- The twisted trace is idempotent: it is a retraction onto its image `𝔽ₚ`. -/
theorem twistedTrace_idempotent (hK : Nat.card K = p ^ n) {c : K}
    (hc : frobTrace p n c = 1) (x : K) :
    twistedTrace p n c (twistedTrace p n c x) = twistedTrace p n c x := by
  obtain ⟨-, -, hmem, hid, -⟩ := twistedTrace_isRetraction hK hc
  exact hid _ (hmem x)

/-- **The universal additive repair.**  Every finite field `K` with `p^n` elements (`n ≠ 0`)
carries an additive retraction onto its prime subfield of the shape `x ↦ Tr(c·x)`, built from
the Frobenius orbit sum alone. -/
theorem exists_additive_retraction (hK : Nat.card K = p ^ n) (hn : n ≠ 0) :
    ∃ c : K, frobTrace p n c = 1 ∧
      (∀ x y : K, twistedTrace p n c (x + y)
          = twistedTrace p n c x + twistedTrace p n c y) ∧
      (∀ a x : K, a ^ p = a → twistedTrace p n c (a * x) = a * twistedTrace p n c x) ∧
      (∀ x : K, twistedTrace p n c x ∈ Set.range (primeSubfieldHom K p)) ∧
      (∀ a ∈ Set.range (primeSubfieldHom K p), twistedTrace p n c a = a) ∧
      (∀ a ∈ Set.range (primeSubfieldHom K p), ∃ x : K, twistedTrace p n c x = a) := by
  obtain ⟨c, hc⟩ := exists_trace_eq_one hK hn
  obtain ⟨h1, h2, h3, h4, h5⟩ := twistedTrace_isRetraction hK hc
  exact ⟨c, hc, h1, h2, h3, h4, h5⟩

end FrobeniusPrimeSubfield
