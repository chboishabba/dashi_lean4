import RequestProject.FrobeniusOrbit

/-!
# Exactly which multiplicative errors can be repaired: `gcd (k, p − 1) = 1`

The Frobenius orbit product of `GF(p^k)`,

`N(x) = x · x^p · ⋯ · x^(p^(k−1)) = x^s`,  `s = 1 + p + ⋯ + p^(k−1)`,

lands in the prime subfield `𝔽ₚ` and is onto it, but on `𝔽ₚ` itself it is `a ↦ a^s = a^k`
(exponents on `𝔽ₚˣ` only matter mod `p − 1`, and `s ≡ k`).  So the multiplicative error is a
single exponent, `k`, just as the additive error is the single scalar `k`
(`RequestProject/UniversalTraceRepair.lean`).  Repairing it means undoing that exponent:

* **If `gcd (k, p − 1) = 1`** the exponent `k` is invertible mod `p − 1`, and
  `R(x) = N(x)^t = x^(s·t)` with `k·t ≡ 1 (mod p − 1)` is a genuine multiplicative retraction
  of `K` onto `𝔽ₚ` (`exists_pow_multiplicative_retraction`, with the explicit exponent
  `t = k^(φ(p−1)−1)`).
* **If `gcd (k, p − 1) ≠ 1`** no multiplicative map into `𝔽ₚ` fixes `𝔽ₚ` pointwise at all
  (`no_multiplicative_retraction_of_not_coprime`), whatever its shape: pick a prime `ℓ`
  dividing both `k` and `p − 1`; then every element of `𝔽ₚˣ` is an `ℓ`-th power in `K`
  (`isPow_of_prime_dvd_geomSum`) while `𝔽ₚˣ`, cyclic of order divisible by `ℓ`, contains a
  non-`ℓ`-th-power (`exists_not_pow_zmod`).

Together: `multiplicative_retraction_iff_coprime` — a multiplicative retraction of `GF(p^k)`
onto `𝔽ₚ` exists **iff** `gcd (k, p − 1) = 1`.  This is the sharp form of the even-degree
obstruction `FrobeniusRepair.no_multiplicative_retraction_of_even_degree` proved for `GF(9)`
in `RequestProject/GF9Repair.lean` (`ℓ = 2` there), and it tells exactly which of the failing
sizes of the scan can be repaired multiplicatively: see
`RequestProject/RepairScan.lean`, where the answer turns out to be `q = 125` and `q = 1331`
only.
-/

namespace FrobeniusPrimeSubfield

open Finset

/-! ## Arithmetic of the exponent `s = 1 + p + ⋯ + p^(k−1)` -/

/-- The orbit-product exponent is congruent to the degree modulo `p − 1`: each `p^i ≡ 1`. -/
theorem geomSum_modEq_degree (p k : ℕ) (hp : 1 ≤ p) :
    (∑ i ∈ range k, p ^ i) ≡ k [MOD p - 1] := by
  induction k with
  | zero => simp [Nat.ModEq.refl]
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have h1 : p ^ k ≡ 1 [MOD p - 1] := by
        have hd : p - 1 ∣ p ^ k - 1 := Nat.sub_one_dvd_pow_sub_one p k
        have h1k : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
        exact ((Nat.modEq_iff_dvd' h1k).2 hd).symm
      simpa [Nat.add_comm] using ih.add h1

/-- If a prime `ℓ` divides the degree `k` and also `p − 1`, then it divides the
orbit-product exponent `s = 1 + p + ⋯ + p^(k−1)`. -/
theorem dvd_geomSum_of_dvd {p k l : ℕ} (hp : 1 ≤ p) (hlk : l ∣ k) (hlp : l ∣ p - 1) :
    l ∣ ∑ i ∈ range k, p ^ i := by
  have h := (geomSum_modEq_degree p k hp).of_dvd hlp
  have hk : k ≡ 0 [MOD l] := (Nat.modEq_zero_iff_dvd).2 hlk
  have := h.trans hk
  exact (Nat.modEq_zero_iff_dvd).1 this

/-! ## The positive half: an explicit multiplicative repair when `gcd (k, p − 1) = 1` -/

variable {K : Type*} [Field K] [Fintype K] {p k : ℕ} [hp : Fact p.Prime] [CharP K p]

omit [CharP K p] in
/-- **The multiplicative repair.**  If `gcd (k, p − 1) = 1` then the power map
`x ↦ x^m` with `m = s · t`, `s = 1 + p + ⋯ + p^(k−1)` the orbit-product exponent and
`t = k^(φ(p−1)−1)` an inverse of `k` mod `p − 1`, is a multiplicative retraction of `K` onto
its prime subfield: it is multiplicative (being a power map), takes values in `𝔽ₚ`, and fixes
`𝔽ₚ` pointwise.  Moreover it is a power of the Frobenius orbit product itself,
`x ↦ N(x)^t`. -/
theorem exists_pow_multiplicative_retraction (hK : Nat.card K = p ^ k) (hk : k ≠ 0)
    (hcop : Nat.gcd k (p - 1) = 1) :
    ∃ m : ℕ, 0 < m ∧
      (∀ x y : K, (x * y) ^ m = x ^ m * y ^ m) ∧
      (∀ x : K, (x ^ m) ^ p = x ^ m) ∧
      (∀ a : K, a ^ p = a → a ^ m = a) ∧
      (∀ x : K, x ^ m = (frobNorm p k x) ^ (k ^ (Nat.totient (p - 1) - 1))) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  set s : ℕ := ∑ i ∈ range k, p ^ i with hs
  set t : ℕ := k ^ (Nat.totient (p - 1) - 1) with ht
  have hs1 : 1 ≤ s := by
    have : (0 : ℕ) ∈ range k := Finset.mem_range.2 (Nat.pos_of_ne_zero hk)
    calc 1 = p ^ 0 := by simp
    _ ≤ s := Finset.single_le_sum (f := fun i => p ^ i) (fun i _ => Nat.zero_le _) this
  have ht1 : 1 ≤ t := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hk)
  refine ⟨s * t, by positivity, fun x y => mul_pow x y _, ?_, ?_, ?_⟩
  · -- values lie in the prime subfield: `x^(m(p−1)) = 1`
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · rw [zero_pow (Nat.mul_ne_zero (by omega) (by omega)), zero_pow hp.out.pos.ne']
    · have hcard : Fintype.card K = p ^ k := by rwa [← Nat.card_eq_fintype_card]
      have hpow : x ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one x hx
      have hsm : s * (p - 1) = p ^ k - 1 := geom_sum_mul_pred p k (by omega)
      have key : (x ^ (s * t)) ^ (p - 1) = 1 := by
        have : (x ^ (s * t)) ^ (p - 1) = (x ^ (p ^ k - 1)) ^ t := by
          rw [← pow_mul, ← pow_mul, ← hsm]; ring_nf
        rw [this, ← hcard, hpow, one_pow]
      calc (x ^ (s * t)) ^ p = (x ^ (s * t)) ^ ((p - 1) + 1) := by
            congr 1; omega
      _ = x ^ (s * t) := by rw [pow_succ, key, one_mul]
  · -- the prime subfield is fixed pointwise: `m ≡ 1 (mod p−1)`
    intro a ha
    rcases eq_or_ne a 0 with rfl | ha0
    · exact zero_pow (Nat.mul_ne_zero (by omega) (by omega))
    · have hared : a ^ (p - 1) = 1 := pow_sub_one_eq_one_of_pow_char_eq_self ha ha0
      -- `s·t ≡ k·t = k^φ(p−1) ≡ 1 (mod p−1)`
      have hsk : s ≡ k [MOD p - 1] := geomSum_modEq_degree p k (by omega)
      have hkt : k * t = k ^ Nat.totient (p - 1) := by
        rw [ht, ← pow_succ']
        congr 1
        have : 0 < Nat.totient (p - 1) := Nat.totient_pos.2 (by omega)
        omega
      have heuler : k ^ Nat.totient (p - 1) ≡ 1 [MOD p - 1] :=
        Nat.ModEq.pow_totient hcop
      have hmod : s * t ≡ 1 [MOD p - 1] := by
        calc s * t ≡ k * t [MOD p - 1] := hsk.mul_right t
        _ = k ^ Nat.totient (p - 1) := hkt
        _ ≡ 1 [MOD p - 1] := heuler
      have hle : 1 ≤ s * t := Nat.one_le_iff_ne_zero.2 (by positivity)
      obtain ⟨v, hv⟩ : (p - 1) ∣ s * t - 1 := (Nat.modEq_iff_dvd' hle).1 hmod.symm
      have hmv : s * t = 1 + (p - 1) * v := by omega
      rw [hmv, pow_add, pow_one, pow_mul, hared, one_pow, mul_one]
  · intro x
    rw [frobNorm_eq_pow, ← pow_mul]

/-! ## The negative half: the obstruction when `gcd (k, p − 1) ≠ 1` -/

/-- In `𝔽ₚ` there is a non-`ℓ`-th power whenever the prime `ℓ` divides `p − 1`: a generator of
the cyclic group `𝔽ₚˣ` is one. -/
theorem exists_not_pow_zmod {p l : ℕ} (hp : p.Prime) (hl : 1 < l) (hlp : l ∣ p - 1) :
    ∃ u : ZMod p, u ≠ 0 ∧ ∀ y : ZMod p, y ^ l ≠ u := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hp]
  obtain ⟨c, hc⟩ := hlp
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · have := hp.two_le; omega
    · exact h
  refine ⟨(g : ZMod p), g.ne_zero, ?_⟩
  rintro y hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact g.ne_zero (by rw [← hy, zero_pow (by omega)])
  set w : (ZMod p)ˣ := Units.mk0 y hy0 with hw
  have hwl : w ^ l = g := by
    ext
    push_cast
    simpa [hw] using hy
  have hw1 : w ^ (p - 1) = 1 := by
    ext
    push_cast
    simpa [hw] using ZMod.pow_card_sub_one_eq_one hy0
  have hgc : g ^ c = 1 := by
    calc g ^ c = (w ^ l) ^ c := by rw [hwl]
    _ = w ^ (p - 1) := by rw [← pow_mul, ← hc]
    _ = 1 := hw1
  have hdvd : orderOf g ∣ c := orderOf_dvd_of_pow_eq_one hgc
  rw [hord, hc] at hdvd
  have hle := Nat.le_of_dvd hc0 hdvd
  nlinarith

omit [CharP K p] in
/-- If a prime `ℓ` divides the orbit-product exponent `s`, then **every** nonzero element of
the prime subfield is an `ℓ`-th power in `K`: it is `N(x) = x^s` for some `x`, hence
`(x^(s/ℓ))^ℓ`. -/
theorem isPow_of_prime_dvd_geomSum (hK : Nat.card K = p ^ k) {l : ℕ}
    (hl : l ∣ ∑ i ∈ range k, p ^ i) {a : K} (ha : a ^ p = a) (ha0 : a ≠ 0) :
    ∃ b : K, b ^ l = a := by
  obtain ⟨x, -, hx⟩ := frobNorm_surjective_onto_primeSubfield hK ha ha0
  obtain ⟨c, hc⟩ := hl
  refine ⟨x ^ c, ?_⟩
  rw [← pow_mul, mul_comm c l, ← hc, ← frobNorm_eq_pow, hx]

/-- A multiplicative map sends `ℓ`-th powers to `ℓ`-th powers. -/
theorem map_pow_of_mul {K : Type*} [Field K] {f : K → K}
    (hmul : ∀ x y, f (x * y) = f x * f y) (b : K) : ∀ l : ℕ, 0 < l → f (b ^ l) = (f b) ^ l := by
  intro l hl
  induction l with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [pow_succ, hmul, ih hn, pow_succ]

/-- **The obstruction, in sharp form.**  If `gcd (k, p − 1) ≠ 1` then *no* multiplicative map
`f : K → K` with values in the prime subfield fixes `𝔽ₚ` pointwise: some Frobenius-fixed point
is always moved.  In particular no adjusted power of the orbit product repairs the error. -/
theorem no_multiplicative_retraction_of_not_coprime (hK : Nat.card K = p ^ k)
    (hcop : Nat.gcd k (p - 1) ≠ 1) {f : K → K} (hmul : ∀ x y, f (x * y) = f x * f y)
    (hfix : ∀ x, (f x) ^ p = f x) :
    ∃ a : K, a ^ p = a ∧ f a ≠ a := by
  have hp2 : 2 ≤ p := hp.out.two_le
  set d : ℕ := Nat.gcd k (p - 1) with hd
  have hd0 : d ≠ 0 := by
    intro h
    rw [hd, Nat.gcd_eq_zero_iff] at h
    omega
  have hdne1 : d ≠ 1 := hcop
  have hd1 : 2 ≤ d := by omega
  obtain ⟨l, hlp, hld⟩ := Nat.exists_prime_and_dvd (n := d) (by omega)
  have hlk : l ∣ k := hld.trans (Nat.gcd_dvd_left _ _)
  have hlpm : l ∣ p - 1 := hld.trans (Nat.gcd_dvd_right _ _)
  have hl1 : 1 < l := hlp.one_lt
  -- a non-`ℓ`-th power in `𝔽ₚ`
  obtain ⟨u, hu0, hu⟩ := exists_not_pow_zmod hp.out hl1 hlpm
  set a : K := primeSubfieldHom K p u with hadef
  have ha : a ^ p = a := (pow_char_eq_self_iff_mem_range_zmod a).2 ⟨u, rfl⟩
  have ha0 : a ≠ 0 := fun h =>
    hu0 ((map_eq_zero_iff (primeSubfieldHom K p) (primeSubfieldHom K p).injective).1 h)
  -- but `a` is an `ℓ`-th power in `K`
  obtain ⟨b, hb⟩ :=
    isPow_of_prime_dvd_geomSum hK (dvd_geomSum_of_dvd (by omega) hlk hlpm) ha ha0
  refine ⟨a, ha, fun hfa => ?_⟩
  have hfb : f b ∈ Set.range (primeSubfieldHom K p) :=
    (pow_char_eq_self_iff_mem_range_zmod (f b)).1 (hfix b)
  obtain ⟨y, hy⟩ := hfb
  have : a = (f b) ^ l := by
    rw [← map_pow_of_mul hmul b l (by omega), hb, hfa]
  rw [← hy, ← map_pow, hadef] at this
  exact hu y ((primeSubfieldHom K p).injective this).symm

/-- **The multiplicative dichotomy.**  For a finite field `K` with `p^k` elements (`k ≠ 0`),
a multiplicative retraction of `K` onto its prime subfield `𝔽ₚ` — a multiplicative map with
values in `𝔽ₚ` fixing `𝔽ₚ` pointwise — exists **if and only if** `gcd (k, p − 1) = 1`, and
when it exists it can be taken to be a power `x ↦ N(x)^t` of the Frobenius orbit product. -/
theorem multiplicative_retraction_iff_coprime (hK : Nat.card K = p ^ k) (hk : k ≠ 0) :
    (∃ f : K → K, (∀ x y, f (x * y) = f x * f y) ∧ (∀ x, (f x) ^ p = f x) ∧
        (∀ a : K, a ^ p = a → f a = a))
      ↔ Nat.gcd k (p - 1) = 1 := by
  constructor
  · rintro ⟨f, hmul, hfix, hid⟩
    by_contra hcop
    obtain ⟨a, ha, hne⟩ := no_multiplicative_retraction_of_not_coprime hK hcop hmul hfix
    exact hne (hid a ha)
  · intro hcop
    obtain ⟨m, -, hmulm, hval, hid, -⟩ := exists_pow_multiplicative_retraction hK hk hcop
    exact ⟨fun x => x ^ m, fun x y => hmulm x y, hval, hid⟩

end FrobeniusPrimeSubfield
