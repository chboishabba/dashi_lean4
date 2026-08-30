import RequestProject.Frobenius

/-!
# Frobenius orbits, fixed subfields, and surjectivity of the orbit product

This file continues `RequestProject.Frobenius`. Throughout, `K` is a field of prime
characteristic `p` and `φ : x ↦ x ^ p` is its Frobenius endomorphism.

## Fixed subfields of the iterates

* `fixedSubfield K p k` : the fixed points of the `k`-th Frobenius iterate `x ↦ x ^ (p ^ k)`
  form a subfield of `K`, containing the prime subfield `𝔽_p = fixedSubfield K p 1`.
* `pow_pow_char_of_gcd` : the set of `k` with `x ^ (p ^ k) = x` is closed under `gcd`; so the
  fixed subfields intersect along gcds (`fixedSubfield_inf`).
* `card_fixedSubfield` : in a field with `p ^ n` elements the `k`-th fixed subfield has
  exactly `p ^ gcd(k, n)` elements.

## The Frobenius orbit of an element

For a finite field with `p ^ n` elements the orbit `x, x ^ p, x ^ (p ^ 2), …` of `x` under the
Frobenius is periodic, and

* `exists_frobPeriod` : the least period `d` of `x` divides `n` and divides every period;
* `frobPeriod_eq_one_iff` : the period is `1` exactly for the elements of the prime subfield;
* `ncard_frobOrbit` : the orbit of `x` has exactly `d` elements.

## The orbit product is onto the prime subfield

* `frobNorm_range_eq_primeSubfield` : the image of the Frobenius orbit product
  `x ↦ ∏ k < n, x ^ (p ^ k)` is *exactly* the prime subfield `𝔽_p`; equivalently
  (`frobNorm_surjective_onto_primeSubfield`) every nonzero element of `𝔽_p` is the orbit
  product of some nonzero element of `K`. Together with the retraction property proved in
  `RequestProject.Frobenius` this says that the retraction `Kˣ → 𝔽_pˣ` is surjective.
-/

open Finset

namespace FrobeniusPrimeSubfield

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-! ### Iterates of the Frobenius -/

variable (K p) in
/-- The `k`-th Frobenius iterate `x ↦ x ^ (p ^ k)` is injective. -/
theorem pow_pow_char_inj (k : ℕ) : Function.Injective (fun x : K => x ^ p ^ k) := by
  intro x y h
  simp only at h
  have hk : p ^ k ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have h0 : (x - y) ^ p ^ k = 0 := by rw [sub_pow_char_pow, h, sub_self]
  exact sub_eq_zero.1 ((pow_eq_zero_iff hk).1 h0)

omit hp [CharP K p] in
/-- If `x` is fixed by the `a`-th Frobenius iterate, it is fixed by the `a * m`-th one. -/
theorem pow_pow_char_of_mul {x : K} {a : ℕ} (ha : x ^ p ^ a = x) (m : ℕ) :
    x ^ p ^ (a * m) = x := by
  induction m with
  | zero => simp
  | succ m ih =>
      have : a * (m + 1) = a * m + a := by ring
      rw [this, pow_add, pow_mul, ih, ha]

/-- The exponents fixing `x` are closed under subtraction. -/
theorem pow_pow_char_of_sub {x : K} {a b : ℕ} (ha : x ^ p ^ a = x) (hb : x ^ p ^ b = x) :
    x ^ p ^ (b - a) = x := by
  rcases le_or_gt b a with h | h
  · simp [Nat.sub_eq_zero_of_le h]
  · have hab : a ≤ b := h.le
    refine pow_pow_char_inj K p a ?_
    show (x ^ p ^ (b - a)) ^ p ^ a = x ^ p ^ a
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hab, hb, ha]

/-- The exponents fixing `x` are closed under `gcd`. -/
theorem pow_pow_char_of_gcd {x : K} {a b : ℕ} (ha : x ^ p ^ a = x) (hb : x ^ p ^ b = x) :
    x ^ p ^ Nat.gcd a b = x := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
      rcases Nat.eq_zero_or_pos a with rfl | hapos
      · simpa using hb
      · rw [Nat.gcd_rec]
        have hmod : x ^ p ^ (b % a) = x := by
          have hmul : x ^ p ^ (a * (b / a)) = x := pow_pow_char_of_mul ha (b / a)
          have hsub := pow_pow_char_of_sub hmul hb
          have hbm : b - a * (b / a) = b % a := by
            have := Nat.div_add_mod b a
            omega
          rwa [hbm] at hsub
        exact ih (b % a) (Nat.mod_lt _ hapos) hmod ha

/-! ### The fixed subfield of an iterate -/

variable (K p) in
/-- The fixed points of the `k`-th Frobenius iterate form a subfield of `K`. -/
def fixedSubfield (k : ℕ) : Subfield K where
  carrier := {x : K | x ^ p ^ k = x}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    rw [mul_pow, hx, hy]
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    rw [add_pow_char_pow, hx, hy]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    exact zero_pow (pow_ne_zero _ hp.out.ne_zero)
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    have : ((0 : K) - x) ^ p ^ k = (0 : K) ^ p ^ k - x ^ p ^ k := sub_pow_char_pow _ _ _
    rw [zero_sub, zero_pow (pow_ne_zero _ hp.out.ne_zero), zero_sub, hx] at this
    exact this
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    rw [inv_pow, hx]

@[simp]
theorem mem_fixedSubfield {k : ℕ} {x : K} : x ∈ fixedSubfield K p k ↔ x ^ p ^ k = x := Iff.rfl

/-- The first fixed subfield is the prime subfield. -/
theorem fixedSubfield_one : (fixedSubfield K p 1 : Set K) = Set.range (primeSubfieldHom K p) := by
  ext x
  simp only [SetLike.mem_coe, mem_fixedSubfield, pow_one]
  exact pow_char_eq_self_iff_mem_range_zmod x

/-- Every fixed subfield contains the prime subfield. -/
theorem primeSubfield_le_fixedSubfield (k : ℕ) :
    Set.range (primeSubfieldHom K p) ⊆ (fixedSubfield K p k : Set K) := by
  intro x hx
  exact pow_pow_char_eq_self ((pow_char_eq_self_iff_mem_range_zmod x).2 hx) k

/-- The fixed subfields of two iterates meet in the fixed subfield of the gcd. -/
theorem fixedSubfield_inf (a b : ℕ) :
    fixedSubfield K p a ⊓ fixedSubfield K p b = fixedSubfield K p (Nat.gcd a b) := by
  ext x
  constructor
  · rintro ⟨ha, hb⟩
    exact pow_pow_char_of_gcd ha hb
  · intro h
    obtain ⟨u, hu⟩ := Nat.gcd_dvd_left a b
    obtain ⟨v, hv⟩ := Nat.gcd_dvd_right a b
    exact ⟨by rw [show a = Nat.gcd a b * u from hu]; exact pow_pow_char_of_mul h u,
      by rw [show b = Nat.gcd a b * v from hv]; exact pow_pow_char_of_mul h v⟩

/-! ### The Frobenius period of an element of a finite field -/

section Finite

variable [Fintype K] {n : ℕ}

/-- **The Frobenius period.** In a field with `p ^ n` elements every `x` has a least positive
`d` with `x ^ (p ^ d) = x`; it divides `n` and divides every other period. -/
theorem exists_frobPeriod (hK : Nat.card K = p ^ n) (hn : n ≠ 0) (x : K) :
    ∃ d, 0 < d ∧ d ∣ n ∧ x ^ p ^ d = x ∧ ∀ k, 0 < k → x ^ p ^ k = x → d ∣ k := by
  classical
  have hex : ∃ k, 0 < k ∧ x ^ p ^ k = x := ⟨n, Nat.pos_of_ne_zero hn, pow_card_pow_eq_self hK x⟩
  set d := Nat.find hex with hd
  obtain ⟨hdpos, hdfix⟩ := Nat.find_spec hex
  have key : ∀ k, 0 < k → x ^ p ^ k = x → d ∣ k := by
    intro k hk hkfix
    have hg : x ^ p ^ Nat.gcd d k = x := pow_pow_char_of_gcd hdfix hkfix
    have hgpos : 0 < Nat.gcd d k := Nat.gcd_pos_of_pos_left _ hdpos
    have hle : d ≤ Nat.gcd d k := Nat.find_le ⟨hgpos, hg⟩
    have : Nat.gcd d k = d := le_antisymm (Nat.gcd_le_left _ hdpos) hle
    exact this ▸ Nat.gcd_dvd_right d k
  exact ⟨d, hdpos, key n (Nat.pos_of_ne_zero hn) (pow_card_pow_eq_self hK x), hdfix, key⟩

omit [Fintype K] in
/-- The elements of Frobenius period `1` are exactly the elements of the prime subfield. -/
theorem frobPeriod_eq_one_iff {x : K} :
    x ^ p ^ 1 = x ↔ x ∈ Set.range (primeSubfieldHom K p) := by
  rw [pow_one]
  exact pow_char_eq_self_iff_mem_range_zmod x

/-- The Frobenius orbit of `x`: the set of all `x ^ (p ^ k)`. -/
def frobOrbit (p : ℕ) (x : K) : Set K := Set.range fun k : ℕ => x ^ p ^ k

omit [Fintype K] in
/-- The Frobenius orbit of `x` has exactly `d` elements, where `d` is the period of `x`. -/
theorem ncard_frobOrbit {x : K} {d : ℕ} (hdpos : 0 < d) (hdfix : x ^ p ^ d = x)
    (hmin : ∀ k, 0 < k → x ^ p ^ k = x → d ∣ k) :
    (frobOrbit p x).ncard = d := by
  classical
  have hmod : ∀ k, x ^ p ^ (k % d) = x ^ p ^ k := by
    intro k
    conv_rhs => rw [← Nat.div_add_mod k d, pow_add, pow_mul, pow_pow_char_of_mul hdfix (k / d)]
  have key : ∀ i j, i ≤ j → j < d → x ^ p ^ i = x ^ p ^ j → i = j := by
    intro i j hij hjd h
    by_contra hne
    have hfix : x ^ p ^ (j - i) = x := by
      refine pow_pow_char_inj K p i ?_
      show (x ^ p ^ (j - i)) ^ p ^ i = x ^ p ^ i
      rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hij, ← h]
    have hdvd := hmin (j - i) (by omega) hfix
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have himg : frobOrbit p x = ↑((Finset.range d).image fun k : ℕ => x ^ p ^ k) := by
    ext y
    simp only [frobOrbit, Set.mem_range, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_range]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k % d, Nat.mod_lt _ hdpos, hmod k⟩
    · rintro ⟨k, -, rfl⟩
      exact ⟨k, rfl⟩
  rw [himg, Set.ncard_coe_finset, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases le_total i j with h | h
  · exact key i j h hj hij
  · exact (key j i h hi hij.symm).symm

end Finite

/-! ### The orbit product is onto the prime subfield -/

/-- `(∑ k < n, p ^ k) * (p - 1) = p ^ n - 1`. -/
theorem geom_sum_mul_pred (p n : ℕ) (hp : 1 ≤ p) :
    (∑ k ∈ range n, p ^ k) * (p - 1) = p ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
      have h1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ (by omega)
      have h2 : p ^ n * (p - 1) = p ^ n * p - p ^ n := by
        rw [Nat.mul_sub, mul_one]
      have h3 : p ^ n ≤ p ^ n * p := Nat.le_mul_of_pos_right _ (by omega)
      omega

omit [CharP K p] in
/-- A nonzero Frobenius-fixed element satisfies `a ^ (p - 1) = 1`. -/
theorem pow_sub_one_eq_one_of_pow_char_eq_self {a : K} (ha : a ^ p = a) (h0 : a ≠ 0) :
    a ^ (p - 1) = 1 := by
  have h : a ^ (p - 1) * a = a := by
    rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, ha]
  exact mul_right_cancel₀ h0 (by rw [h, one_mul])

section Surjective

variable [Fintype K] {n : ℕ}

omit [CharP K p] in
/-- **The orbit product is onto the prime subfield.** Every nonzero element of `𝔽_p` is the
Frobenius orbit product of a nonzero element of `K`. -/
theorem frobNorm_surjective_onto_primeSubfield (hK : Nat.card K = p ^ n)
    {a : K} (ha : a ^ p = a) (h0 : a ≠ 0) : ∃ x : K, x ≠ 0 ∧ frobNorm p n x = a := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  set u : Kˣ := Units.mk0 a h0 with hu
  obtain ⟨i, hi⟩ : ∃ i : ℕ, g ^ i = u := by
    have := hg u
    rwa [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at this
  have hord : orderOf g = p ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units,
      ← Nat.card_eq_fintype_card, hK]
  set N := ∑ k ∈ range n, p ^ k with hN
  have hp2 : 2 ≤ p := hp.out.two_le
  have hNmul : N * (p - 1) = p ^ n - 1 := geom_sum_mul_pred p n (by omega)
  have hu1 : u ^ (p - 1) = 1 := by
    ext
    push_cast
    simpa [hu] using pow_sub_one_eq_one_of_pow_char_eq_self ha h0
  have hdvd : orderOf g ∣ i * (p - 1) := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_mul, hi, hu1]
  rw [hord, ← hNmul] at hdvd
  have hNi : N ∣ i := (Nat.mul_dvd_mul_iff_right (by omega : 0 < p - 1)).1 hdvd
  refine ⟨((g ^ (i / N) : Kˣ) : K), Units.ne_zero _, ?_⟩
  have hgu : (g ^ (i / N)) ^ N = u := by rw [← pow_mul, Nat.div_mul_cancel hNi, hi]
  rw [frobNorm_eq_pow, ← hN, ← Units.val_pow_eq_pow_val, hgu]
  rfl

/-- The image of the Frobenius orbit product is *exactly* the prime subfield `𝔽_p`. -/
theorem frobNorm_range_eq_primeSubfield (hK : Nat.card K = p ^ n) (hn : n ≠ 0) :
    Set.range (frobNorm p n) = Set.range (primeSubfieldHom K p) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    exact frobNorm_mem_primeSubfield hK x
  · rintro y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · refine ⟨0, ?_⟩
      show ∏ k ∈ range n, (0 : K) ^ p ^ k = 0
      refine Finset.prod_eq_zero (Finset.mem_range.2 (Nat.pos_of_ne_zero hn)) ?_
      simp
    · obtain ⟨x, -, hx⟩ := frobNorm_surjective_onto_primeSubfield hK
        ((pow_char_eq_self_iff_mem_range_zmod y).2 hy) hy0
      exact ⟨x, hx⟩

end Surjective

/-! ### The size of the fixed subfields -/

section Counting

/-- In a finite cyclic group of order `m`, the equation `x ^ e = 1` has exactly `e` solutions
when `e ∣ m`. -/
theorem card_ker_pow_of_dvd (G : Type*) [CommGroup G] [Finite G] [IsCyclic G] {e : ℕ}
    (he : e ∣ Nat.card G) (he0 : 0 < e) : Nat.card ((powMonoidHom e : G →* G).ker) = e := by
  classical
  have _ : Fintype G := Fintype.ofFinite G
  set m := Nat.card G with hm
  have hm0 : 0 < m := Nat.card_pos
  obtain ⟨c, hc⟩ := he
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · simp [hc] at hm0
    · exact h
  have hcdvd : (m / e) ∣ m := ⟨e, by rw [hc, Nat.mul_div_cancel_left _ he0, mul_comm]⟩
  have hme : m / e = c := by rw [hc, Nat.mul_div_cancel_left _ he0]
  have hrange : Nat.card ((powMonoidHom (m / e) : G →* G).range) = e := by
    rw [IsCyclic.card_powMonoidHom_range, ← hm, Nat.gcd_eq_right hcdvd, hme, hc,
      Nat.mul_div_cancel _ hc0]
  have hle : (powMonoidHom (m / e) : G →* G).range ≤ (powMonoidHom e : G →* G).ker := by
    rintro x ⟨y, rfl⟩
    simp only [MonoidHom.mem_ker, powMonoidHom_apply] at *
    rw [← pow_mul, hme, show c * e = Nat.card G by rw [← hm, hc]; ring]
    exact pow_card_eq_one'
  have h1 := Subgroup.card_le_of_le hle
  rw [hrange] at h1
  have h2 : Nat.card ((powMonoidHom e : G →* G).ker) ≤ e := by
    have hle2 := IsCyclic.card_pow_eq_one_le (α := G) (n := e) he0
    have hsub : Fintype.card {a : G // a ^ e = 1} ≤ e := by
      rw [Fintype.card_subtype]; exact hle2
    have hcongr : Nat.card ((powMonoidHom e : G →* G).ker)
        = Fintype.card {a : G // a ^ e = 1} := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => by simp [MonoidHom.mem_ker])
    omega
  omega

variable [Fintype K] {n : ℕ}

omit [CharP K p] in
/-- **The fixed subfield of an iterate has `p ^ d` elements** when `d ∣ n`: in a field with
`p ^ n` elements, exactly `p ^ d` elements satisfy `x ^ (p ^ d) = x`. -/
theorem card_fixedSubfield_of_dvd {d : ℕ} (hK : Nat.card K = p ^ n) (hd : d ∣ n) (hd0 : 0 < d) :
    Nat.card {x : K // x ^ p ^ d = x} = p ^ d := by
  classical
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpd : 2 ≤ p ^ d := by
    have h1 : p ^ 1 ≤ p ^ d := Nat.pow_le_pow_right (by omega) hd0
    simp only [pow_one] at h1
    omega
  set e := p ^ d - 1 with he
  have he0 : 0 < e := by omega
  have hunits : Nat.card Kˣ = p ^ n - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have hdvd : e ∣ Nat.card Kˣ := by
    obtain ⟨c, rfl⟩ := hd
    rw [hunits, pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one (p ^ d) c
  have hker := card_ker_pow_of_dvd Kˣ hdvd he0
  have hkerfin : (Finset.univ.filter fun u : Kˣ => u ^ e = 1).card = e := by
    have h2 : Fintype.card {u : Kˣ // u ^ e = 1}
        = Nat.card ((powMonoidHom e : Kˣ →* Kˣ).ker) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => by simp [MonoidHom.mem_ker])
    rw [← Fintype.card_subtype, h2, hker]
  have hA : (Finset.univ.filter fun x : K => x ^ p ^ d = x) =
      insert 0 ((Finset.univ.filter fun u : Kˣ => u ^ e = 1).image Units.val) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro hx
      rcases eq_or_ne x 0 with rfl | hx0
      · exact Or.inl rfl
      · have hxx : x ^ (p ^ d - 1) * x = x := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega), hx]
        have hx1 : x ^ e = 1 := by
          refine mul_right_cancel₀ hx0 ?_
          rw [one_mul]
          exact hxx
        refine Or.inr ⟨Units.mk0 x hx0, ?_, rfl⟩
        apply Units.ext
        simpa using hx1
    · rintro (rfl | ⟨u, hu, rfl⟩)
      · exact zero_pow (pow_ne_zero _ hp.out.ne_zero)
      · have hu1 : (u : K) ^ e = 1 := by
          rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
        calc (u : K) ^ p ^ d = (u : K) ^ (e + 1) := by rw [he]; congr 1; omega
          _ = (u : K) ^ e * u := by rw [pow_succ]
          _ = u := by rw [hu1, one_mul]
  have hcard : (Finset.univ.filter fun x : K => x ^ p ^ d = x).card = p ^ d := by
    rw [hA, Finset.card_insert_of_notMem,
      Finset.card_image_of_injective _ Units.val_injective, hkerfin]
    · omega
    · simp only [Finset.mem_image, Finset.mem_filter, not_exists]
      rintro u ⟨-, hu⟩
      exact (Units.ne_zero u) hu
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact hcard

/-- **The fixed subfields of a finite field.** In a field with `p ^ n` elements the fixed
points of the `k`-th Frobenius iterate form a subfield with `p ^ gcd(k, n)` elements; so the
fixed subfields of the iterates are exactly the subfields `𝔽_{p^d}` for `d ∣ n`. -/
theorem card_fixedSubfield (hK : Nat.card K = p ^ n) (hn : n ≠ 0) (k : ℕ) :
    Nat.card (fixedSubfield K p k) = p ^ Nat.gcd k n := by
  have hgcd0 : 0 < Nat.gcd k n := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hn)
  have hiff : ∀ x : K, x ^ p ^ k = x ↔ x ^ p ^ Nat.gcd k n = x := by
    intro x
    constructor
    · intro hx
      exact pow_pow_char_of_gcd hx (pow_card_pow_eq_self hK x)
    · intro hx
      obtain ⟨u, hu⟩ := Nat.gcd_dvd_left k n
      rw [show k = Nat.gcd k n * u from hu]
      exact pow_pow_char_of_mul hx u
  have hcongr : Nat.card (fixedSubfield K p k) = Nat.card {x : K // x ^ p ^ Nat.gcd k n = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (hiff x).trans Iff.rfl)
  rw [hcongr]
  exact card_fixedSubfield_of_dvd hK (Nat.gcd_dvd_right k n) hgcd0

end Counting

end FrobeniusPrimeSubfield
