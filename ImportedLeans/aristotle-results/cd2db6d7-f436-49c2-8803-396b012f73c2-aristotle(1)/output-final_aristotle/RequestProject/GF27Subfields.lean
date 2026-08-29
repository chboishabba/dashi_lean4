import RequestProject.FrobeniusOrbit
import RequestProject.FrobeniusGalois
import RequestProject.FrobeniusTrace
import RequestProject.KernelReflection
import RequestProject.SubfieldLattice

/-!
# The subfields and Frobenius orbits of the concrete field `GF27`

The general results of `RequestProject.FrobeniusOrbit`, instantiated at the kernel-computable
field `GF27 = 𝔽₃[t]/(t³ - t - 1)` of `RequestProject.GF27`.

* `GF27.card_fixedSubfield_eq` : the fixed points of the `k`-th Frobenius iterate form a
  subfield with `3 ^ gcd(k, 3)` elements, so there are only two of them: the prime subfield
  `𝔽₃` (for `3 ∤ k`) and the whole of `GF27` (for `3 ∣ k`) — `GF27.fixedSubfield_dichotomy`.
* `GF27.subfield_dichotomy` : and in fact *every* subfield of `GF27` is one of these two,
  since `n = 3` is prime.
* `GF27.frobPeriod_one_or_three` : every element has Frobenius period `1` or `3`; the period
  is `1` exactly on `{0, 1, 2} = 𝔽₃`, and every other element has an orbit of `3` elements.
* `GF27.frobNorm_range_eq` : the image of the orbit product `x ↦ x ¹³` is exactly `𝔽₃`, so the
  retraction onto the prime subfield is surjective.
* `GF27.frobTrace_range_eq` : the additive counterpart — the image of the orbit sum
  `x ↦ x + x³ + x⁹` is again exactly `𝔽₃`; but here `p = 3` divides `n = 3`, and indeed the
  orbit sum *kills* the prime subfield (`GF27.frobTrace_eq_zero_of_mem_primeSubfield`), so no
  rescaling of it is a retraction (`GF27.no_scaled_frobTrace_retraction`).  This shows the
  hypothesis `p ∤ n` in `frobTrace_retraction_onto_primeSubfield` is genuinely needed.
-/

open FrobeniusPrimeSubfield

namespace GF27

/-- The `k`-th fixed subfield of `GF27` has `3 ^ gcd(k, 3)` elements. -/
theorem card_fixedSubfield_eq (k : ℕ) :
    Nat.card (fixedSubfield GF27 3 k) = 3 ^ Nat.gcd k 3 :=
  card_fixedSubfield (K := GF27) (p := 3) (n := 3) card_eq (by norm_num) k

/-- Only two subfields arise as fixed subfields of a Frobenius iterate of `GF27`: the prime
subfield `𝔽₃` (three elements) and `GF27` itself (`27` elements). -/
theorem fixedSubfield_dichotomy (k : ℕ) :
    (¬ (3 ∣ k) ∧ Nat.card (fixedSubfield GF27 3 k) = 3) ∨
      (3 ∣ k ∧ Nat.card (fixedSubfield GF27 3 k) = 27) := by
  rcases Nat.eq_zero_or_pos (k % 3) with h | h
  · have hdvd : 3 ∣ k := Nat.dvd_of_mod_eq_zero h
    refine Or.inr ⟨hdvd, ?_⟩
    rw [card_fixedSubfield_eq, Nat.gcd_eq_right hdvd]
    norm_num
  · have hnd : ¬ (3 ∣ k) := by omega
    refine Or.inl ⟨hnd, ?_⟩
    have hg : Nat.gcd k 3 = 1 := by
      rcases (Nat.prime_three).eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right k 3) with h1 | h3
      · exact h1
      · exact absurd (h3 ▸ Nat.gcd_dvd_left k 3) hnd
    rw [card_fixedSubfield_eq, hg, pow_one]

/-- **`GF27` has exactly two subfields**: the prime subfield `{0, 1, 2} = 𝔽₃` and the whole
field. -/
theorem subfield_dichotomy (F : Subfield GF27) :
    (F : Set GF27) = ({0, 1, 2} : Set GF27) ∨ F = ⊤ := by
  rcases subfield_eq_of_prime (K := GF27) (p := 3) (n := 3) card_eq (by norm_num) F with h | h
  · exact Or.inl (h.trans range_primeSubfieldHom)
  · exact Or.inr h

/-- Every element of `GF27` has Frobenius period `1` or `3`, and period `1` characterizes the
prime subfield `{0, 1, 2}`. -/
theorem frobPeriod_one_or_three (x : GF27) :
    (x ^ 3 = x ∧ x ∈ ({0, 1, 2} : Set GF27)) ∨
      (x ^ 3 ≠ x ∧ (frobOrbit 3 x).ncard = 3) := by
  rcases eq_or_ne (x ^ 3) x with h | h
  · exact Or.inl ⟨h, (pow_three_eq_self_iff x).1 h⟩
  · refine Or.inr ⟨h, ?_⟩
    have h27 : x ^ 3 ^ 3 = x := pow_card_pow_eq_self (K := GF27) (p := 3) (n := 3) card_eq x
    refine ncard_frobOrbit (p := 3) (by norm_num) h27 ?_
    intro k hk hkfix
    -- the period divides `3`, and it is not `1`
    by_contra hnd
    have hg : Nat.gcd k 3 = 1 := by
      rcases (Nat.prime_three).eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right k 3) with h1 | h3
      · exact h1
      · exact absurd (h3 ▸ Nat.gcd_dvd_left k 3) hnd
    have : x ^ 3 ^ Nat.gcd k 3 = x := pow_pow_char_of_gcd hkfix h27
    rw [hg, pow_one] at this
    exact h this

/-- The image of the Frobenius orbit product `x ↦ x ¹³` on `GF27` is exactly the prime
subfield `{0, 1, 2} = 𝔽₃`: the retraction onto the prime subfield is surjective. -/
theorem frobNorm_range_eq : Set.range (frobNorm 3 3 : GF27 → GF27) = ({0, 1, 2} : Set GF27) := by
  rw [frobNorm_range_eq_primeSubfield (K := GF27) (p := 3) (n := 3) card_eq (by norm_num)]
  exact range_primeSubfieldHom

/-- The image of the Frobenius orbit *sum* `x ↦ x + x³ + x⁹` on `GF27` is also exactly the
prime subfield `{0, 1, 2} = 𝔽₃`. -/
theorem frobTrace_range_eq : Set.range (frobTrace 3 3 : GF27 → GF27) = ({0, 1, 2} : Set GF27) := by
  rw [frobTrace_range_eq_primeSubfield (K := GF27) (p := 3) (n := 3) card_eq (by norm_num)]
  exact range_primeSubfieldHom

/-- On `GF27` the orbit sum vanishes on the prime subfield, because `p = 3` divides `n = 3`. -/
theorem frobTrace_eq_zero_of_mem_primeSubfield (a : GF27) (ha : a ∈ ({0, 1, 2} : Set GF27)) :
    frobTrace 3 3 a = 0 := by
  have ha3 : a ^ 3 = a := (pow_three_eq_self_iff a).2 ha
  rw [frobTrace_of_pow_char_eq_self (p := 3) ha3]
  have : ((3 : ℕ) : GF27) = 0 := by
    exact_mod_cast (CharP.cast_eq_zero_iff GF27 3 3).2 dvd_rfl
  rw [this, zero_mul]

/-- No rescaling of the orbit sum is a retraction of `GF27` onto its prime subfield: the orbit
sum kills `𝔽₃`, so it cannot fix `1`. -/
theorem no_scaled_frobTrace_retraction :
    ¬ ∃ c : GF27, ∀ a ∈ ({0, 1, 2} : Set GF27), c * frobTrace 3 3 a = a := by
  rintro ⟨c, hc⟩
  have h1 : c * frobTrace 3 3 (1 : GF27) = 1 := hc 1 (by simp)
  rw [frobTrace_eq_zero_of_mem_primeSubfield 1 (by simp), mul_zero] at h1
  exact zero_ne_one h1

/-- The Frobenius automorphism `x ↦ x³` of `GF27` has order exactly `3`. -/
theorem orderOf_frobeniusEquiv_eq_three : orderOf (frobeniusEquiv GF27 3) = 3 :=
  orderOf_frobeniusEquiv (K := GF27) (p := 3) (n := 3) card_eq (by norm_num)

end GF27
