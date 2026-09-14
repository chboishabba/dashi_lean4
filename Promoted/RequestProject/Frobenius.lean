import Mathlib

/-!
# The Frobenius endomorphism of a field of characteristic `p`

Let `K` be a field of characteristic a prime `p`, and let `φ : x ↦ x ^ p` be its Frobenius
endomorphism.

* `pow_char_eq_self_iff_mem_range_zmod` / `fixedPoints_frobenius_eq_range_zmod` :
  the fixed points of the Frobenius are exactly the prime subfield, i.e. the image of the
  canonical ring homomorphism `ZMod p → K` (`𝔽_p ⊆ K`).
* `card_fixedPoints_frobenius` : there are exactly `p` such fixed points.
* `forall_pow_pow_char_eq_self_iff` : the elements with a one-point Frobenius orbit are exactly
  the elements of the prime subfield.

For a *finite* field `K` with `#K = p ^ n`, the Frobenius orbit of `x` is
`x, x ^ p, x ^ (p ^ 2), …, x ^ (p ^ (n-1))` (it closes up since `x ^ (p ^ n) = x`).
While a single `x ^ (p ^ k)` need not lie in `𝔽_p`, the *product over the whole orbit*
— the norm map — always does:

* `frobNorm` : `x ↦ ∏ k < n, x ^ (p ^ k)`, equivalently `x ^ ((p ^ n - 1)/(p - 1))`.
* `frobNorm_pow_char` / `frobNorm_mem_primeSubfield` : the orbit product is Frobenius-fixed,
  i.e. lands in the prime subfield `𝔽_p`.
* `frobNorm_ne_zero` : the orbit product of a nonzero element is a nonzero element of `𝔽_p`.
* `frobNorm_mul` : the orbit product is multiplicative, so it is a group homomorphism
  `K ˣ → 𝔽_p ˣ`.
* `frobNorm_of_pow_char_eq_self` : on the prime subfield it is `a ↦ a ^ n`; hence
  (`frobNorm_eq_self_of_pow_char_eq_self`) when `p - 1 ∣ n - 1` it restricts to the identity
  on `𝔽_p`, i.e. it is a *retraction* of `K ˣ` onto the (central) subgroup `𝔽_p ˣ`.
-/

open Finset

namespace FrobeniusPrimeSubfield

variable (K : Type*) [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

/-! ### Fixed points of the Frobenius endomorphism -/

/-- The canonical embedding of the prime field `𝔽_p = ZMod p` into a field of
characteristic `p`. -/
abbrev primeSubfieldHom : ZMod p →+* K := ZMod.castHom (dvd_refl p) K

variable {K p}

/-- **Fixed points of Frobenius = the prime subfield.**
An element of a field of characteristic `p` satisfies `x ^ p = x` if and only if it lies in
the image of `ZMod p → K`. -/
theorem pow_char_eq_self_iff_mem_range_zmod (x : K) :
    x ^ p = x ↔ x ∈ Set.range (primeSubfieldHom K p) := by
  constructor
  · intro h
    letI := ZMod.algebra K p
    have hb : (⊥ : Subfield K) = (algebraMap (ZMod p) K).fieldRange :=
      Subfield.bot_eq_of_zMod_algebra p
    have hx : x ∈ (⊥ : Subfield K) := (Subfield.mem_bot_iff_pow_eq_self K p).2 h
    rw [hb] at hx
    obtain ⟨y, rfl⟩ := hx
    refine ⟨y, ?_⟩
    rfl
  · rintro ⟨y, rfl⟩
    rw [← map_pow, ZMod.pow_card]

/-- The fixed point set of the Frobenius endomorphism is precisely the prime subfield. -/
theorem fixedPoints_frobenius_eq_range_zmod (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] : {x : K | x ^ p = x} = Set.range (primeSubfieldHom K p) :=
  Set.ext fun _ => pow_char_eq_self_iff_mem_range_zmod _

/-- The fixed point set of the Frobenius endomorphism, described through `frobenius`. -/
theorem fixedPoints_frobenius_eq_range_zmod' (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] [ExpChar K p] :
    {x : K | frobenius K p x = x} = Set.range (primeSubfieldHom K p) := by
  simpa [frobenius_def] using fixedPoints_frobenius_eq_range_zmod K p

/-- The Frobenius endomorphism of a field of characteristic `p` has exactly `p` fixed points. -/
theorem card_fixedPoints_frobenius (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    Nat.card {x : K // x ^ p = x} = p := by
  have hinj : Function.Injective (primeSubfieldHom K p) := (primeSubfieldHom K p).injective
  have : Nat.card {x : K // x ^ p = x} = Nat.card (Set.range (primeSubfieldHom K p)) := by
    congr 1
    exact congrArg _ (fixedPoints_frobenius_eq_range_zmod K p)
  rw [this, Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card, ZMod.card]

omit hp [CharP K p] in
/-- A Frobenius-fixed element is fixed by every iterate of the Frobenius. -/
theorem pow_pow_char_eq_self {x : K} (hx : x ^ p = x) : ∀ k : ℕ, x ^ p ^ k = x := by
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, hx]

/-- The elements whose Frobenius orbit is a single point are exactly the elements of the
prime subfield. -/
theorem forall_pow_pow_char_eq_self_iff (x : K) :
    (∀ k : ℕ, x ^ p ^ k = x) ↔ x ∈ Set.range (primeSubfieldHom K p) := by
  refine ⟨fun h => (pow_char_eq_self_iff_mem_range_zmod x).1 (by simpa using h 1), fun h =>
    pow_pow_char_eq_self ((pow_char_eq_self_iff_mem_range_zmod x).2 h)⟩

/-! ### The Frobenius orbit product (norm) of a finite field -/

variable (p)

/-- The product over the Frobenius orbit of `x`, i.e. `x ⬝ x ^ p ⬝ … ⬝ x ^ (p ^ (n-1))`.
For `#K = p ^ n` this is the norm of `x` down to the prime subfield. -/
def frobNorm (n : ℕ) (x : K) : K := ∏ k ∈ range n, x ^ p ^ k

variable {p}

omit hp [CharP K p] in
theorem frobNorm_eq_pow (n : ℕ) (x : K) : frobNorm p n x = x ^ (∑ k ∈ range n, p ^ k) := by
  rw [frobNorm, Finset.prod_pow_eq_pow_sum]

omit hp [CharP K p] in
/-- The orbit product is multiplicative. -/
theorem frobNorm_mul (n : ℕ) (x y : K) :
    frobNorm p n (x * y) = frobNorm p n x * frobNorm p n y := by
  simp [frobNorm, mul_pow, prod_mul_distrib]

omit hp [CharP K p] in
theorem frobNorm_one (n : ℕ) : frobNorm p n (1 : K) = 1 := by simp [frobNorm]

omit hp [CharP K p] in
theorem frobNorm_ne_zero {n : ℕ} {x : K} (hx : x ≠ 0) : frobNorm p n x ≠ 0 :=
  prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ hx

section Finite

variable [Fintype K] {n : ℕ} (hK : Nat.card K = p ^ n)
include hK

omit hp [CharP K p] in
theorem pow_card_pow_eq_self (x : K) : x ^ p ^ n = x := by
  rw [← hK, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

omit [CharP K p] in
/-- **The Frobenius orbit product lands in the prime subfield**: it is fixed by Frobenius. -/
theorem frobNorm_pow_char (x : K) : (frobNorm p n x) ^ p = frobNorm p n x := by
  set f : ℕ → K := fun k => x ^ p ^ k with hf
  have hpow : (frobNorm p n x) ^ p = ∏ k ∈ range n, f (k + 1) := by
    rw [frobNorm, ← prod_pow]
    refine prod_congr rfl fun k _ => ?_
    simp only [hf]
    rw [← pow_mul, ← pow_succ]
  have hshift : (∏ k ∈ range n, f (k + 1)) * f 0 = (∏ k ∈ range n, f k) * f n := by
    rw [← prod_range_succ' f n, prod_range_succ f n]
  have h0 : f 0 = x := by simp [hf]
  have hn : f n = x := by rw [hf]; exact pow_card_pow_eq_self hK x
  rw [h0, hn] at hshift
  rcases eq_or_ne x 0 with rfl | hx
  · rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [frobNorm]
    · have hs : ∑ k ∈ range n, p ^ k ≠ 0 := by
        have h1 : p ^ 0 ≤ ∑ k ∈ range n, p ^ k :=
          Finset.single_le_sum (f := fun k => p ^ k) (fun i _ => Nat.zero_le _)
            (mem_range.2 hn0)
        simp only [pow_zero] at h1
        omega
      rw [frobNorm_eq_pow, zero_pow hs, zero_pow hp.out.ne_zero]
  · rw [hpow]
    exact mul_right_cancel₀ hx hshift

/-- The Frobenius orbit product of `x` lies in the prime subfield `𝔽_p ⊆ K`. -/
theorem frobNorm_mem_primeSubfield (x : K) :
    frobNorm p n x ∈ Set.range (primeSubfieldHom K p) :=
  (pow_char_eq_self_iff_mem_range_zmod _).1 (frobNorm_pow_char hK x)

/-- For `x ≠ 0` the orbit product is a *nonzero* element of the prime subfield. -/
theorem frobNorm_mem_primeSubfield_ne_zero {x : K} (hx : x ≠ 0) :
    frobNorm p n x ∈ Set.range (primeSubfieldHom K p) ∧ frobNorm p n x ≠ 0 :=
  ⟨frobNorm_mem_primeSubfield hK x, frobNorm_ne_zero hx⟩

end Finite

/-! ### Behaviour on the prime subfield: a retraction of `Kˣ` onto `𝔽_pˣ` -/

omit hp [CharP K p] in
/-- On the prime subfield the orbit product is the `n`-th power map. -/
theorem frobNorm_of_pow_char_eq_self {n : ℕ} {a : K} (ha : a ^ p = a) :
    frobNorm p n a = a ^ n := by
  simp [frobNorm, pow_pow_char_eq_self ha]

omit [CharP K p] in
/-- If `p - 1 ∣ n - 1` (and `n ≠ 0`), the orbit product restricts to the identity on the prime
subfield: the norm is then a retraction of `Kˣ` onto the subgroup `𝔽_pˣ`. -/
theorem frobNorm_eq_self_of_pow_char_eq_self {n : ℕ} (hn : n ≠ 0) (hdvd : p - 1 ∣ n - 1)
    {a : K} (ha : a ^ p = a) : frobNorm p n a = a := by
  rw [frobNorm_of_pow_char_eq_self ha]
  rcases eq_or_ne a 0 with rfl | h0
  · simp [zero_pow hn]
  · have hp1 : a ^ (p - 1) = 1 := by
      have : a ^ (p - 1) * a = a := by
        rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, ha]
      exact mul_right_cancel₀ h0 (by rw [this, one_mul])
    obtain ⟨m, hm⟩ := hdvd
    have hnm : n = 1 + (p - 1) * m := by omega
    rw [hnm, pow_add, pow_mul, hp1, one_pow, pow_one, mul_one]

/-- **The orbit product as a retraction onto the prime subfield.**
For a finite field `K` with `#K = p ^ n` and `p - 1 ∣ n - 1`, the Frobenius orbit product
`x ↦ ∏ k < n, x ^ (p ^ k)` is multiplicative, sends every element into the prime subfield
`𝔽_p` (and every nonzero element to a nonzero element of it), and fixes `𝔽_p` pointwise.
In other words it is a retraction of the group `Kˣ` onto its subgroup `𝔽_pˣ`. -/
theorem frobNorm_retraction_onto_primeSubfield [Fintype K] {n : ℕ} (hK : Nat.card K = p ^ n)
    (hn : n ≠ 0) (hdvd : p - 1 ∣ n - 1) :
    (∀ x y : K, frobNorm p n (x * y) = frobNorm p n x * frobNorm p n y) ∧
      (∀ x : K, frobNorm p n x ∈ Set.range (primeSubfieldHom K p)) ∧
      (∀ x : K, x ≠ 0 → frobNorm p n x ≠ 0) ∧
      (∀ a ∈ Set.range (primeSubfieldHom K p), frobNorm p n a = a) := by
  refine ⟨frobNorm_mul n, frobNorm_mem_primeSubfield hK, fun _ hx => frobNorm_ne_zero hx,
    fun a ha => ?_⟩
  exact frobNorm_eq_self_of_pow_char_eq_self hn hdvd
    ((pow_char_eq_self_iff_mem_range_zmod a).2 ha)

end FrobeniusPrimeSubfield
