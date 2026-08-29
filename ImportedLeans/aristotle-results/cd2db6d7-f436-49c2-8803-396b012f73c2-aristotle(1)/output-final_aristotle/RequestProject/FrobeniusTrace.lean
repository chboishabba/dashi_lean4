import Mathlib
import RequestProject.Frobenius
import RequestProject.FrobeniusOrbit

/-!
# The additive Frobenius orbit sum (trace) and a retraction onto `𝔽_p`

This file is the additive counterpart of the multiplicative theory in `Frobenius.lean`.
For a field `K` of characteristic `p` we consider the *Frobenius orbit sum*

`frobTrace p n x = ∑_{k < n} x ^ (p ^ k)`,

the sum of the Frobenius orbit of `x`, i.e. the field trace of `K` over `𝔽_p` when
`#K = p ^ n`.

Main results (for a finite field `K` with `Nat.card K = p ^ n`, `n ≠ 0`):

* `frobTrace_add` : the orbit sum is additive (freshman's dream), and
  `frobTrace_smul_of_pow_char_eq_self` : it is `𝔽_p`-linear.
* `frobTrace_pow_char`, `frobTrace_mem_primeSubfield` : the orbit sum is Frobenius-fixed,
  hence **lands in the prime subfield `𝔽_p`**.
* `exists_frobTrace_ne_zero` : the orbit sum is not identically zero — the polynomial
  `∑_{k<n} X^(p^k)` has degree `p^(n-1) < p^n = #K`, so it cannot vanish on all of `K`.
* `frobTrace_range_eq_primeSubfield` : consequently the image of the orbit sum is *exactly*
  `𝔽_p`.
* `frobTrace_of_pow_char_eq_self` : on `𝔽_p` the orbit sum is `a ↦ n * a`; therefore when
  `p ∤ n` the normalized orbit sum `x ↦ (n : K)⁻¹ * frobTrace p n x` is an **additive
  retraction of `K` onto `𝔽_p`** (`frobTrace_retraction_onto_primeSubfield`), the additive
  analogue of the multiplicative retraction `Kˣ → 𝔽_pˣ` given by the orbit product.
-/

open Finset Polynomial

namespace FrobeniusPrimeSubfield

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]

variable (p) in
/-- The Frobenius orbit sum (the trace when `#K = p ^ n`): `x ↦ ∑_{k < n} x ^ (p ^ k)`. -/
def frobTrace (n : ℕ) (x : K) : K := ∑ k ∈ range n, x ^ p ^ k

/-- The `p`-th power map is additive on finite sums (freshman's dream). -/
theorem sum_pow_char (s : Finset ℕ) (f : ℕ → K) :
    (∑ k ∈ s, f k) ^ p = ∑ k ∈ s, (f k) ^ p := by
  simpa only [frobenius_def] using map_sum (frobenius K p) f s

theorem frobTrace_add (n : ℕ) (x y : K) :
    frobTrace p n (x + y) = frobTrace p n x + frobTrace p n y := by
  simp only [frobTrace, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => add_pow_char_pow x y p k

omit [CharP K p] in
theorem frobTrace_zero (n : ℕ) : frobTrace p n (0 : K) = 0 := by
  simp only [frobTrace]
  refine Finset.sum_eq_zero fun k _ => ?_
  exact zero_pow (pow_ne_zero k hp.out.ne_zero)

omit hp [CharP K p] in
/-- The orbit sum is `𝔽_p`-linear: scalars from the prime subfield pull out. -/
theorem frobTrace_smul_of_pow_char_eq_self {n : ℕ} {a : K} (ha : a ^ p = a) (x : K) :
    frobTrace p n (a * x) = a * frobTrace p n x := by
  simp only [frobTrace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_pow, pow_pow_char_eq_self ha k]

omit hp [CharP K p] in
/-- On the prime subfield the orbit sum is multiplication by `n`. -/
theorem frobTrace_of_pow_char_eq_self {n : ℕ} {a : K} (ha : a ^ p = a) :
    frobTrace p n a = (n : K) * a := by
  simp only [frobTrace]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ range n) => pow_pow_char_eq_self ha k]
  simp [mul_comm]

section Finite

variable [Fintype K] {n : ℕ}

/-- The orbit sum is Frobenius-fixed. -/
theorem frobTrace_pow_char (hK : Nat.card K = p ^ n) (x : K) :
    (frobTrace p n x) ^ p = frobTrace p n x := by
  set f : ℕ → K := fun k => x ^ p ^ k with hf
  have hpow : (frobTrace p n x) ^ p = ∑ k ∈ range n, f (k + 1) := by
    rw [frobTrace, sum_pow_char]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hf]
    rw [← pow_mul, ← pow_succ]
  have hshift : (∑ k ∈ range n, f (k + 1)) + f 0 = (∑ k ∈ range n, f k) + f n := by
    rw [← Finset.sum_range_succ' f n, Finset.sum_range_succ f n]
  have h0 : f 0 = x := by simp [hf]
  have hn : f n = x := by rw [hf]; exact pow_card_pow_eq_self hK x
  rw [h0, hn] at hshift
  rw [hpow, frobTrace]
  exact add_right_cancel hshift

/-- **The Frobenius orbit sum lands in the prime subfield `𝔽_p`.** -/
theorem frobTrace_mem_primeSubfield (hK : Nat.card K = p ^ n) (x : K) :
    frobTrace p n x ∈ Set.range (primeSubfieldHom K p) :=
  (pow_char_eq_self_iff_mem_range_zmod _).1 (frobTrace_pow_char hK x)

variable (K p n) in
/-- The polynomial `∑_{k<n} X ^ (p ^ k)`, whose evaluation is the Frobenius orbit sum. -/
noncomputable def tracePoly : K[X] := ∑ k ∈ range n, X ^ p ^ k

omit [Fintype K] [CharP K p] hp in
theorem eval_tracePoly (x : K) : (tracePoly K p n).eval x = frobTrace p n x := by
  simp [tracePoly, frobTrace, eval_finset_sum]

omit [Fintype K] [CharP K p] in
theorem natDegree_tracePoly_le : (tracePoly K p n).natDegree ≤ p ^ (n - 1) := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  rw [Polynomial.natDegree_X_pow]
  exact Nat.pow_le_pow_right hp.out.pos (by have := Finset.mem_range.1 hk; omega)

omit [Fintype K] [CharP K p] in
theorem tracePoly_ne_zero (hn : n ≠ 0) : (tracePoly K p n) ≠ 0 := by
  intro h
  have hcoeff : (tracePoly K p n).coeff (p ^ (n - 1)) = 1 := by
    rw [tracePoly, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single (n - 1)]
    · simp
    · intro k hk hkne
      rw [Polynomial.coeff_X_pow, if_neg]
      intro hpk
      exact hkne (Nat.pow_right_injective hp.out.two_le hpk.symm)
    · intro hmem
      exact absurd (Finset.mem_range.2 (by omega)) hmem
  rw [h] at hcoeff
  simp at hcoeff

omit [CharP K p] in
/-- **The Frobenius orbit sum is not identically zero.**  The polynomial `∑_{k<n} X^(p^k)`
has degree `p^(n-1)`, which is smaller than the number `p^n` of elements of `K`. -/
theorem exists_frobTrace_ne_zero (hK : Nat.card K = p ^ n) (hn : n ≠ 0) :
    ∃ x : K, frobTrace p n x ≠ 0 := by
  have hcard : (Fintype.card K) = p ^ n := by rwa [← Nat.card_eq_fintype_card]
  have hdeg : (tracePoly K p n).natDegree < Cardinal.mk K := by
    rw [Cardinal.mk_fintype, hcard]
    have h1 : (tracePoly K p n).natDegree ≤ p ^ (n - 1) := natDegree_tracePoly_le
    have h2 : p ^ (n - 1) < p ^ n := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
    exact_mod_cast lt_of_le_of_lt h1 h2
  obtain ⟨x, hx⟩ :=
    Polynomial.exists_eval_ne_zero_of_natDegree_lt_card _ (tracePoly_ne_zero hn) hdeg
  exact ⟨x, by rwa [eval_tracePoly] at hx⟩

/-- **The image of the Frobenius orbit sum is exactly the prime subfield `𝔽_p`.** -/
theorem frobTrace_range_eq_primeSubfield (hK : Nat.card K = p ^ n) (hn : n ≠ 0) :
    Set.range (frobTrace p n : K → K) = Set.range (primeSubfieldHom K p) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact frobTrace_mem_primeSubfield hK x
  · rintro a ha
    obtain ⟨x, hx⟩ := exists_frobTrace_ne_zero hK hn
    have ht : frobTrace p n x ∈ Set.range (primeSubfieldHom K p) :=
      frobTrace_mem_primeSubfield hK x
    -- the scalar `c = a * (frobTrace p n x)⁻¹` again lies in the prime subfield
    have hsub : (fixedSubfield K p 1 : Set K) = Set.range (primeSubfieldHom K p) :=
      fixedSubfield_one
    have haF : a ∈ fixedSubfield K p 1 := by rw [← SetLike.mem_coe, hsub]; exact ha
    have htF : frobTrace p n x ∈ fixedSubfield K p 1 := by
      rw [← SetLike.mem_coe, hsub]; exact ht
    have hcF : a * (frobTrace p n x)⁻¹ ∈ fixedSubfield K p 1 :=
      mul_mem haF (inv_mem htF)
    have hc : (a * (frobTrace p n x)⁻¹) ^ p = a * (frobTrace p n x)⁻¹ := by
      have := hcF
      rw [mem_fixedSubfield] at this
      simpa using this
    refine ⟨a * (frobTrace p n x)⁻¹ * x, ?_⟩
    rw [frobTrace_smul_of_pow_char_eq_self hc x, mul_assoc, inv_mul_cancel₀ hx, mul_one]

/-- **The normalized orbit sum is an additive retraction of `K` onto `𝔽_p`.**
When `p ∤ n`, the map `x ↦ (n : K)⁻¹ * ∑_{k<n} x ^ (p ^ k)` is additive, takes values in the
prime subfield `𝔽_p`, fixes `𝔽_p` pointwise, and is onto `𝔽_p`.  This is the additive
analogue of the multiplicative retraction `frobNorm_retraction_onto_primeSubfield`. -/
theorem frobTrace_retraction_onto_primeSubfield (hK : Nat.card K = p ^ n) (hpn : ¬ p ∣ n) :
    (∀ x y : K, (n : K)⁻¹ * frobTrace p n (x + y)
        = (n : K)⁻¹ * frobTrace p n x + (n : K)⁻¹ * frobTrace p n y) ∧
      (∀ x : K, (n : K)⁻¹ * frobTrace p n x ∈ Set.range (primeSubfieldHom K p)) ∧
      (∀ a ∈ Set.range (primeSubfieldHom K p), (n : K)⁻¹ * frobTrace p n a = a) ∧
      (∀ a ∈ Set.range (primeSubfieldHom K p),
        ∃ x : K, (n : K)⁻¹ * frobTrace p n x = a) := by
  have hn0 : (n : K) ≠ 0 := fun h => hpn ((CharP.cast_eq_zero_iff K p n).1 h)
  have hnF : (n : K) ∈ fixedSubfield K p 1 := by
    rw [mem_fixedSubfield, pow_one, ← map_natCast (primeSubfieldHom K p) n, ← map_pow,
      ZMod.pow_card]
  have hninv : ((n : K))⁻¹ ∈ Set.range (primeSubfieldHom K p) := by
    have := inv_mem hnF
    rw [← SetLike.mem_coe, fixedSubfield_one] at this
    exact this
  have hninvpow : ((n : K)⁻¹) ^ p = (n : K)⁻¹ :=
    (pow_char_eq_self_iff_mem_range_zmod _).2 hninv
  refine ⟨fun x y => by rw [frobTrace_add, mul_add], ?_, ?_, ?_⟩
  · intro x
    have hx : frobTrace p n x ∈ Set.range (primeSubfieldHom K p) :=
      frobTrace_mem_primeSubfield hK x
    obtain ⟨u, hu⟩ := hninv
    obtain ⟨v, hv⟩ := hx
    exact ⟨u * v, by rw [map_mul, hu, hv]⟩
  · intro a ha
    have hpa : a ^ p = a := (pow_char_eq_self_iff_mem_range_zmod a).2 ha
    rw [frobTrace_of_pow_char_eq_self hpa, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  · intro a ha
    have hpa : a ^ p = a := (pow_char_eq_self_iff_mem_range_zmod a).2 ha
    exact ⟨a, by rw [frobTrace_of_pow_char_eq_self hpa, ← mul_assoc, inv_mul_cancel₀ hn0,
      one_mul]⟩

end Finite

end FrobeniusPrimeSubfield
