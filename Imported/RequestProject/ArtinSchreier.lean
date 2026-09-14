import Mathlib
import RequestProject.Frobenius
import RequestProject.FrobeniusOrbit
import RequestProject.FrobeniusTrace

/-!
# The Artin–Schreier map `x ↦ x ^ p - x` and the kernel of the trace

This file is the additive Hilbert-90 companion of `FrobeniusTrace.lean`.  For a field `K` of
characteristic `p` the *Artin–Schreier map* is the additive endomorphism

`℘ : K →+ K`,  `℘ x = x ^ p - x`,

i.e. `frobenius - id`.  Its kernel is exactly the prime subfield `𝔽_p` (this is the fixed-point
theorem for the Frobenius, restated additively), so for a finite field with `p ^ n` elements its
image has `p ^ (n-1)` elements.  The Frobenius orbit sum (trace) kills every element of the image
by a telescoping computation, and the kernel of the trace also has `p ^ (n-1)` elements because
the trace is onto `𝔽_p`.  Hence:

* `range_asHom_eq_ker_traceHom` : **the image of `x ↦ x ^ p - x` is exactly the kernel of the
  trace** — the Artin–Schreier / additive Hilbert 90 theorem for finite fields;
* `exists_pow_sub_self_eq_iff` : the equation `x ^ p - x = a` is solvable in `K` if and only if
  `∑_{k<n} a ^ (p ^ k) = 0`.

Supporting results: `mem_ker_asHom_iff` and `card_ker_asHom` (kernel = `𝔽_p`, of size `p`),
`card_range_asHom` and `card_ker_traceHom` (both of size `p ^ (n-1)`),
`card_range_traceHom` (the trace is onto `𝔽_p`).
-/

open Finset

namespace FrobeniusPrimeSubfield

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-! ### The Artin–Schreier map and the trace as additive homomorphisms -/

variable (K p) in
/-- The Artin–Schreier map `℘ : x ↦ x ^ p - x`, i.e. `frobenius - id`, as an additive
endomorphism of `K`. -/
def asHom : K →+ K where
  toFun x := x ^ p - x
  map_zero' := by simp [zero_pow hp.out.ne_zero]
  map_add' x y := by rw [add_pow_char]; ring

@[simp] theorem asHom_apply (x : K) : asHom K p x = x ^ p - x := rfl

variable (K p) in
/-- The Frobenius orbit sum `x ↦ ∑_{k<n} x ^ (p ^ k)` as an additive endomorphism of `K`. -/
def traceHom (n : ℕ) : K →+ K where
  toFun := frobTrace p n
  map_zero' := frobTrace_zero n
  map_add' := frobTrace_add n

@[simp] theorem traceHom_apply (n : ℕ) (x : K) : traceHom K p n x = frobTrace p n x := rfl

/-- **The kernel of the Artin–Schreier map is the prime subfield `𝔽_p`.** -/
theorem mem_ker_asHom_iff (x : K) :
    x ∈ (asHom K p).ker ↔ x ∈ Set.range (primeSubfieldHom K p) := by
  rw [AddMonoidHom.mem_ker, asHom_apply, sub_eq_zero, pow_char_eq_self_iff_mem_range_zmod]

/-- The kernel of the Artin–Schreier map has exactly `p` elements. -/
theorem card_ker_asHom : Nat.card (asHom K p).ker = p := by
  have h : Nat.card (asHom K p).ker = Nat.card {x : K // x ^ p = x} :=
    Nat.card_congr <| Equiv.subtypeEquivRight fun x => by
      rw [mem_ker_asHom_iff, ← pow_char_eq_self_iff_mem_range_zmod]
  rw [h, card_fixedPoints_frobenius K p]

section Finite

variable [Fintype K] {n : ℕ}

omit [Fintype K] in
/-- First isomorphism theorem, in the cardinality form used below. -/
private theorem card_ker_mul_card_range (f : K →+ K) :
    Nat.card f.ker * Nat.card f.range = Nat.card K := by
  have h := AddSubgroup.card_mul_index f.ker
  have h2 : f.ker.index = Nat.card f.range := by
    rw [AddSubgroup.index]
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
  rwa [h2] at h

omit [Fintype K] in
/-- The image of the Artin–Schreier map has `p ^ (n-1)` elements. -/
theorem card_range_asHom (hK : Nat.card K = p ^ n) (hn : n ≠ 0) :
    Nat.card (asHom K p).range = p ^ (n - 1) := by
  have h := card_ker_mul_card_range (asHom K p)
  rw [card_ker_asHom, hK] at h
  have hpn : p ^ n = p * p ^ (n - 1) := by
    conv_lhs => rw [show n = 1 + (n - 1) by omega]
    rw [pow_add, pow_one]
  rw [hpn] at h
  exact (Nat.eq_of_mul_eq_mul_left hp.out.pos h)

/-- The trace is onto the prime subfield, so its image has exactly `p` elements. -/
theorem card_range_traceHom (hK : Nat.card K = p ^ n) (hn : n ≠ 0) :
    Nat.card (traceHom K p n).range = p := by
  have hset : ((traceHom K p n).range : Set K) = Set.range (primeSubfieldHom K p) := by
    rw [AddMonoidHom.coe_range]
    exact frobTrace_range_eq_primeSubfield hK hn
  have : Nat.card (traceHom K p n).range = Nat.card (Set.range (primeSubfieldHom K p)) := by
    congr 1
    exact congrArg _ hset
  rw [this, Nat.card_range_of_injective (primeSubfieldHom K p).injective,
    Nat.card_eq_fintype_card, ZMod.card]

/-- The kernel of the trace has `p ^ (n-1)` elements. -/
theorem card_ker_traceHom (hK : Nat.card K = p ^ n) (hn : n ≠ 0) :
    Nat.card (traceHom K p n).ker = p ^ (n - 1) := by
  have h := card_ker_mul_card_range (traceHom K p n)
  rw [card_range_traceHom hK hn, hK] at h
  have hpn : p ^ n = p ^ (n - 1) * p := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  rw [hpn] at h
  exact Nat.eq_of_mul_eq_mul_right hp.out.pos h

/-- **The trace kills the image of the Artin–Schreier map** (telescoping sum):
`∑_{k<n} (x ^ p - x) ^ (p ^ k) = x ^ (p ^ n) - x = 0`. -/
theorem frobTrace_pow_sub_self (hK : Nat.card K = p ^ n) (x : K) :
    frobTrace p n (x ^ p - x) = 0 := by
  have hterm : ∀ k ∈ range n, (x ^ p - x) ^ p ^ k = x ^ p ^ (k + 1) - x ^ p ^ k := by
    intro k _
    rw [sub_pow_char_pow, ← pow_mul, ← pow_succ']
  rw [frobTrace, Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun k => x ^ p ^ k) n,
    pow_zero, pow_one, pow_card_pow_eq_self hK x, sub_self]

/-- **Artin–Schreier / additive Hilbert 90 for finite fields.**
The image of `℘ : x ↦ x ^ p - x` is exactly the kernel of the trace `x ↦ ∑_{k<n} x ^ (p ^ k)`.
Both are `𝔽_p`-subspaces of index `p` in `K`, and the inclusion `range ℘ ≤ ker tr` is the
telescoping identity above. -/
theorem range_asHom_eq_ker_traceHom (hK : Nat.card K = p ^ n) (hn : n ≠ 0) :
    (asHom K p).range = (traceHom K p n).ker := by
  have hle : (asHom K p).range ≤ (traceHom K p n).ker := by
    rintro _ ⟨x, rfl⟩
    rw [AddMonoidHom.mem_ker, traceHom_apply, asHom_apply]
    exact frobTrace_pow_sub_self hK x
  refine AddSubgroup.eq_of_le_of_card_ge hle ?_
  rw [card_range_asHom hK hn, card_ker_traceHom hK hn]

/-- **Solvability of the Artin–Schreier equation.**  For `a` in a field with `p ^ n` elements,
`x ^ p - x = a` has a solution if and only if the trace of `a` vanishes. -/
theorem exists_pow_sub_self_eq_iff (hK : Nat.card K = p ^ n) (hn : n ≠ 0) (a : K) :
    (∃ x : K, x ^ p - x = a) ↔ frobTrace p n a = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact frobTrace_pow_sub_self hK x
  · intro ha
    have hmem : a ∈ (traceHom K p n).ker := by
      rw [AddMonoidHom.mem_ker, traceHom_apply]; exact ha
    rw [← range_asHom_eq_ker_traceHom hK hn] at hmem
    obtain ⟨x, hx⟩ := hmem
    exact ⟨x, hx⟩

omit [Fintype K] in
/-- The Artin–Schreier map is exactly `p`-to-one onto its image: `x ^ p - x = y ^ p - y` iff
`x - y` lies in the prime subfield. -/
theorem asHom_eq_asHom_iff (x y : K) :
    x ^ p - x = y ^ p - y ↔ x - y ∈ Set.range (primeSubfieldHom K p) := by
  rw [← mem_ker_asHom_iff, AddMonoidHom.mem_ker, map_sub, asHom_apply, asHom_apply, sub_eq_zero]

end Finite

end FrobeniusPrimeSubfield
