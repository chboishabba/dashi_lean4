import RequestProject.FrobeniusOrbit

/-!
# The subfield lattice of a finite field, via the Frobenius

This file completes the description of the Frobenius fixed subfields started in
`RequestProject.FrobeniusOrbit`. Let `K` be a field with `p ^ n` elements (`p` prime, `n ≠ 0`).

* `fixedSubfield_le_fixedSubfield_iff` : for `d, e` positive divisors of `n`,
  `fixedSubfield K p d ≤ fixedSubfield K p e ↔ d ∣ e`; in particular
  `fixedSubfield_injOn` : distinct divisors give distinct subfields.
* `exists_card_subfield` : every subfield of `K` has `p ^ d` elements for a (unique) positive
  divisor `d` of `n`;
* `exists_eq_fixedSubfield` : and it *is* the fixed subfield of the `d`-th Frobenius iterate.
* `bijOn_fixedSubfield` : consequently `d ↦ fixedSubfield K p d` is a bijection from the
  divisors of `n` onto the set of all subfields of `K` — the subfield lattice of `𝔽_{p^n}`
  is the divisor lattice of `n`.
* Two extreme cases: `fixedSubfield_self` (`d = n` gives all of `K`) and `fixedSubfield_one`
  (`d = 1` gives the prime subfield `𝔽_p`); when `n` is prime, `subfield_eq_of_prime` says
  these are the only subfields.
-/

namespace FrobeniusPrimeSubfield

variable {K : Type*} [Field K] {p n : ℕ} [hp : Fact p.Prime] [CharP K p] [Fintype K]

/-! ### The inclusion order on fixed subfields is divisibility -/

/-- For positive divisors `d`, `e` of `n`, the `d`-th fixed subfield is contained in the `e`-th
one exactly when `d ∣ e`. -/
theorem fixedSubfield_le_fixedSubfield_iff (hK : Nat.card K = p ^ n) (hn : n ≠ 0)
    {d e : ℕ} (hd : d ∣ n) (he : e ∣ n) :
    fixedSubfield K p d ≤ fixedSubfield K p e ↔ d ∣ e := by
  constructor
  · intro hle
    have hinf : fixedSubfield K p (Nat.gcd d e) = fixedSubfield K p d := by
      rw [← fixedSubfield_inf]
      exact inf_eq_left.2 hle
    have hcards : p ^ Nat.gcd (Nat.gcd d e) n = p ^ Nat.gcd d n := by
      rw [← card_fixedSubfield hK hn (Nat.gcd d e), ← card_fixedSubfield hK hn d, hinf]
    have hgd : Nat.gcd d n = d := Nat.gcd_eq_left hd
    have hgde : Nat.gcd (Nat.gcd d e) n = Nat.gcd d e :=
      Nat.gcd_eq_left ((Nat.gcd_dvd_left d e).trans hd)
    rw [hgd, hgde] at hcards
    have : Nat.gcd d e = d := Nat.pow_right_injective hp.out.two_le hcards
    exact this ▸ Nat.gcd_dvd_right d e
  · rintro ⟨c, rfl⟩
    intro x hx
    exact pow_pow_char_of_mul hx c

/-- Distinct positive divisors of `n` give distinct fixed subfields. -/
theorem fixedSubfield_injOn (hK : Nat.card K = p ^ n) (hn : n ≠ 0) :
    Set.InjOn (fun d => fixedSubfield K p d) {d | d ∈ n.divisors} := by
  intro d hd e he hde
  simp only [Set.mem_setOf_eq, Nat.mem_divisors] at hd he
  have h1 : d ∣ e :=
    (fixedSubfield_le_fixedSubfield_iff hK hn hd.1 he.1).1 (le_of_eq hde)
  have h2 : e ∣ d :=
    (fixedSubfield_le_fixedSubfield_iff hK hn he.1 hd.1).1 (le_of_eq hde.symm)
  exact Nat.dvd_antisymm h1 h2

/-! ### Every subfield is a fixed subfield -/

/-- Every subfield of a field with `p ^ n` elements has `p ^ d` elements for some positive
divisor `d` of `n`. -/
theorem exists_card_subfield (hK : Nat.card K = p ^ n) (F : Subfield K) :
    ∃ d, 0 < d ∧ d ∣ n ∧ Nat.card F = p ^ d := by
  classical
  have hFfin : Fintype F := Fintype.ofFinite _
  obtain ⟨d, -, hd⟩ := FiniteField.card F p
  refine ⟨d, ?_, ?_, ?_⟩
  · exact d.2
  · have hrank : Nat.card K = Nat.card F ^ Module.finrank F K :=
      Module.natCard_eq_pow_finrank
    have hFcard : Nat.card F = p ^ (d : ℕ) := by
      rw [Nat.card_eq_fintype_card]; exact hd
    rw [hK, hFcard, ← pow_mul] at hrank
    have : n = (d : ℕ) * Module.finrank F K := Nat.pow_right_injective hp.out.two_le hrank
    exact ⟨_, this⟩
  · rw [Nat.card_eq_fintype_card]; exact hd

/-- **Every subfield of a finite field is the fixed subfield of a Frobenius iterate.** -/
theorem exists_eq_fixedSubfield (hK : Nat.card K = p ^ n) (hn : n ≠ 0) (F : Subfield K) :
    ∃ d, 0 < d ∧ d ∣ n ∧ F = fixedSubfield K p d := by
  classical
  obtain ⟨d, hd0, hdn, hcard⟩ := exists_card_subfield hK F
  refine ⟨d, hd0, hdn, ?_⟩
  have hFfin : Fintype F := Fintype.ofFinite _
  have hle : F ≤ fixedSubfield K p d := by
    intro x hx
    have hcard' : Fintype.card F = p ^ d := by rw [← Nat.card_eq_fintype_card]; exact hcard
    have : (⟨x, hx⟩ : F) ^ Fintype.card F = ⟨x, hx⟩ := FiniteField.pow_card _
    rw [hcard'] at this
    have := congrArg (Subfield.subtype F) this
    simpa using this
  have hcards : Nat.card (fixedSubfield K p d) = Nat.card F := by
    rw [card_fixedSubfield hK hn d, Nat.gcd_eq_left hdn, hcard]
  refine SetLike.coe_injective ?_
  refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)
  simpa [← Nat.card_coe_set_eq] using hcards.le

/-- **The subfield lattice of `𝔽_{p^n}` is the divisor lattice of `n`:** `d ↦ fixedSubfield d`
is a bijection from the divisors of `n` onto the subfields of `K`. -/
theorem bijOn_fixedSubfield (hK : Nat.card K = p ^ n) (hn : n ≠ 0) :
    Set.BijOn (fun d => fixedSubfield K p d) {d | d ∈ n.divisors} (Set.univ : Set (Subfield K)) := by
  refine ⟨fun d _ => Set.mem_univ _, fixedSubfield_injOn hK hn, ?_⟩
  intro F _
  obtain ⟨d, hd0, hdn, rfl⟩ := exists_eq_fixedSubfield hK hn F
  exact ⟨d, by simp [Nat.mem_divisors, hdn, hn], rfl⟩

/-! ### The two extreme subfields -/

/-- The `n`-th fixed subfield of a field with `p ^ n` elements is the whole field. -/
theorem fixedSubfield_self (hK : Nat.card K = p ^ n) : fixedSubfield K p n = ⊤ := by
  ext x
  simpa using pow_card_pow_eq_self hK x

/-- **When `n` is prime, `𝔽_{p^n}` has exactly two subfields:** the prime subfield and the
whole field. -/
theorem subfield_eq_of_prime (hK : Nat.card K = p ^ n) (hn : n.Prime) (F : Subfield K) :
    (F : Set K) = Set.range (primeSubfieldHom K p) ∨ F = ⊤ := by
  obtain ⟨d, hd0, hdn, rfl⟩ := exists_eq_fixedSubfield hK hn.ne_zero F
  rcases (Nat.Prime.eq_one_or_self_of_dvd hn d hdn) with rfl | rfl
  · exact Or.inl fixedSubfield_one
  · exact Or.inr (fixedSubfield_self hK)

end FrobeniusPrimeSubfield
