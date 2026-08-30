import RequestProject.FrobeniusTrace
import RequestProject.SubfieldLattice

/-!
# Relative norm and trace onto an intermediate subfield `𝔽_{p^d}`

`RequestProject.Frobenius` and `RequestProject.FrobeniusTrace` treat the product and the sum of
the *full* Frobenius orbit `x, x^p, …, x^(p^(n-1))`, which land in the prime subfield `𝔽_p`.
This file does the same for the orbit of `x` under the `d`-th iterate of the Frobenius, for
`d ∣ n`: with `n = d * m`,

`relNorm p d m x = ∏_{k < m} x ^ (p ^ (d k))`,  `relTrace p d m x = ∑_{k < m} x ^ (p ^ (d k))`,

the norm and trace of `K = 𝔽_{p^n}` down to the intermediate field `𝔽_{p^d}` — the fixed
subfield of the `d`-th Frobenius iterate (see `RequestProject.SubfieldLattice`, where these
are shown to be *all* the subfields of `K`). For `d = 1` they specialize to the orbit product
and orbit sum (`relNorm_one_eq_frobNorm`, `relTrace_one_eq_frobTrace`).

Main results (all for `d * m = n`, `#K = p ^ n`):

* `relNorm_mem_fixedSubfield`, `relTrace_mem_fixedSubfield` : both really do land in
  `𝔽_{p^d}`, being fixed by the `d`-th Frobenius iterate;
* `relNorm_mul`, `relNorm_ne_zero`, `relTrace_add`, `relTrace_smul_of_mem` : multiplicativity
  of the norm, additivity and `𝔽_{p^d}`-linearity of the trace;
* on `𝔽_{p^d}` the norm is `a ↦ a ^ m` and the trace is `a ↦ m * a`;
* `relNorm_retraction_onto_fixedSubfield` : hence when `p ^ d - 1 ∣ m - 1` the relative norm is
  a retraction of `Kˣ` onto `𝔽_{p^d}ˣ`, and `relTrace_retraction_onto_fixedSubfield` : when
  `p ∤ m` the normalized relative trace is an additive retraction of `K` onto `𝔽_{p^d}`.
-/

open Finset

namespace FrobeniusPrimeSubfield

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]

variable (p) in
/-- The product of the orbit of `x` under the `d`-th Frobenius iterate: the norm of
`K = 𝔽_{p^(d m)}` down to `𝔽_{p^d}`. -/
def relNorm (d m : ℕ) (x : K) : K := ∏ k ∈ range m, x ^ p ^ (d * k)

variable (p) in
/-- The sum of the orbit of `x` under the `d`-th Frobenius iterate: the trace of
`K = 𝔽_{p^(d m)}` down to `𝔽_{p^d}`. -/
def relTrace (d m : ℕ) (x : K) : K := ∑ k ∈ range m, x ^ p ^ (d * k)

omit hp [CharP K p] in
theorem relNorm_one_eq_frobNorm (n : ℕ) (x : K) : relNorm p 1 n x = frobNorm p n x := by
  simp [relNorm, frobNorm]

omit hp [CharP K p] in
theorem relTrace_one_eq_frobTrace (n : ℕ) (x : K) : relTrace p 1 n x = frobTrace p n x := by
  simp [relTrace, frobTrace]

omit hp [CharP K p] in
theorem relNorm_mul (d m : ℕ) (x y : K) :
    relNorm p d m (x * y) = relNorm p d m x * relNorm p d m y := by
  simp only [relNorm, ← Finset.prod_mul_distrib, mul_pow]

omit hp [CharP K p] in
theorem relNorm_ne_zero {d m : ℕ} {x : K} (hx : x ≠ 0) : relNorm p d m x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ hx

theorem relTrace_add (d m : ℕ) (x y : K) :
    relTrace p d m (x + y) = relTrace p d m x + relTrace p d m y := by
  simp only [relTrace, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => add_pow_char_pow x y p (d * k)

/-- Iterated freshman's dream for finite sums. -/
theorem sum_pow_char_pow (d : ℕ) (s : Finset ℕ) (f : ℕ → K) :
    (∑ k ∈ s, f k) ^ p ^ d = ∑ k ∈ s, (f k) ^ p ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ, pow_mul, ih, sum_pow_char]
      exact Finset.sum_congr rfl fun k _ => by rw [← pow_mul, ← pow_succ]

/-! ### The relative norm and trace land in `𝔽_{p^d}` -/

section Orbit

variable {d m : ℕ}

omit [CharP K p] in
/-- If the `(d m)`-th Frobenius iterate fixes `x`, the relative norm of `x` is fixed by the
`d`-th iterate, i.e. it lies in `𝔽_{p^d}`. -/
theorem relNorm_pow_char_pow {x : K} (hx : x ^ p ^ (d * m) = x) :
    (relNorm p d m x) ^ p ^ d = relNorm p d m x := by
  set f : ℕ → K := fun k => x ^ p ^ (d * k) with hf
  have hpow : (relNorm p d m x) ^ p ^ d = ∏ k ∈ range m, f (k + 1) := by
    rw [relNorm, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [hf]
    rw [← pow_mul, ← pow_add]
    ring_nf
  have hshift : (∏ k ∈ range m, f (k + 1)) * f 0 = (∏ k ∈ range m, f k) * f m := by
    rw [← Finset.prod_range_succ' f m, Finset.prod_range_succ f m]
  have h0 : f 0 = x := by simp [hf]
  have hm : f m = x := hx
  rw [h0, hm] at hshift
  rcases eq_or_ne x 0 with rfl | hx0
  · rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp [relNorm]
    · have hzero : relNorm p d m (0 : K) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_range.2 hm0) ?_
        simp
      rw [hzero, zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  · rw [hpow]
    exact mul_right_cancel₀ hx0 hshift

/-- If the `(d m)`-th Frobenius iterate fixes `x`, the relative trace of `x` lies in
`𝔽_{p^d}`. -/
theorem relTrace_pow_char_pow {x : K} (hx : x ^ p ^ (d * m) = x) :
    (relTrace p d m x) ^ p ^ d = relTrace p d m x := by
  set f : ℕ → K := fun k => x ^ p ^ (d * k) with hf
  have hpow : (relTrace p d m x) ^ p ^ d = ∑ k ∈ range m, f (k + 1) := by
    rw [relTrace, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hf]
    rw [← pow_mul, ← pow_add]
    ring_nf
  have hshift : (∑ k ∈ range m, f (k + 1)) + f 0 = (∑ k ∈ range m, f k) + f m := by
    rw [← Finset.sum_range_succ' f m, Finset.sum_range_succ f m]
  have h0 : f 0 = x := by simp [hf]
  have hm : f m = x := hx
  rw [h0, hm] at hshift
  rw [hpow, relTrace]
  exact add_right_cancel hshift

variable [Fintype K] {n : ℕ}

/-- **The relative norm lands in the subfield `𝔽_{p^d}`.** -/
theorem relNorm_mem_fixedSubfield (hK : Nat.card K = p ^ n) (hdm : d * m = n) (x : K) :
    relNorm p d m x ∈ fixedSubfield K p d :=
  relNorm_pow_char_pow (by rw [hdm]; exact pow_card_pow_eq_self hK x)

/-- **The relative trace lands in the subfield `𝔽_{p^d}`.** -/
theorem relTrace_mem_fixedSubfield (hK : Nat.card K = p ^ n) (hdm : d * m = n) (x : K) :
    relTrace p d m x ∈ fixedSubfield K p d :=
  relTrace_pow_char_pow (by rw [hdm]; exact pow_card_pow_eq_self hK x)

end Orbit

/-! ### Behaviour on the subfield `𝔽_{p^d}` -/

section Restriction

variable {d m : ℕ}

omit hp [CharP K p] in
/-- On `𝔽_{p^d}` the relative norm is the `m`-th power map. -/
theorem relNorm_of_mem {a : K} (ha : a ^ p ^ d = a) : relNorm p d m a = a ^ m := by
  simp [relNorm, pow_pow_char_of_mul ha]

omit hp [CharP K p] in
/-- On `𝔽_{p^d}` the relative trace is multiplication by `m`. -/
theorem relTrace_of_mem {a : K} (ha : a ^ p ^ d = a) : relTrace p d m a = (m : K) * a := by
  simp [relTrace, pow_pow_char_of_mul ha, mul_comm]

omit hp [CharP K p] in
/-- The relative trace is `𝔽_{p^d}`-linear. -/
theorem relTrace_smul_of_mem {a : K} (ha : a ^ p ^ d = a) (x : K) :
    relTrace p d m (a * x) = a * relTrace p d m x := by
  simp only [relTrace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_pow, pow_pow_char_of_mul ha]

omit [CharP K p] in
/-- If `p ^ d - 1 ∣ m - 1` (and `m ≠ 0`), the relative norm restricts to the identity on
`𝔽_{p^d}`. -/
theorem relNorm_eq_self_of_mem (hm : m ≠ 0) (hdvd : p ^ d - 1 ∣ m - 1)
    {a : K} (ha : a ^ p ^ d = a) : relNorm p d m a = a := by
  rw [relNorm_of_mem ha]
  rcases eq_or_ne a 0 with rfl | h0
  · simp [zero_pow hm]
  · have hp1 : a ^ (p ^ d - 1) = 1 := by
      have hpd : 1 ≤ p ^ d := Nat.one_le_pow _ _ hp.out.pos
      have h : a ^ (p ^ d - 1) * a = a := by
        rw [← pow_succ, Nat.sub_add_cancel hpd, ha]
      exact mul_right_cancel₀ h0 (by rw [h, one_mul])
    obtain ⟨c, hc⟩ := hdvd
    have hmc : m = 1 + (p ^ d - 1) * c := by omega
    rw [hmc, pow_add, pow_mul, hp1, one_pow, pow_one, mul_one]

end Restriction

/-! ### The two relative retractions -/

section Retraction

variable [Fintype K] {d m n : ℕ}

/-- **The relative norm as a retraction onto the intermediate field `𝔽_{p^d}`.**
For `#K = p ^ n` with `n = d * m` and `p ^ d - 1 ∣ m - 1`, the map
`x ↦ ∏_{k<m} x ^ (p ^ (d k))` is multiplicative, sends `K` into the subfield `𝔽_{p^d}`
(nonzero elements to nonzero elements), and fixes `𝔽_{p^d}` pointwise: a retraction of the
group `Kˣ` onto the subgroup `𝔽_{p^d}ˣ`. -/
theorem relNorm_retraction_onto_fixedSubfield (hK : Nat.card K = p ^ n) (hdm : d * m = n)
    (hm : m ≠ 0) (hdvd : p ^ d - 1 ∣ m - 1) :
    (∀ x y : K, relNorm p d m (x * y) = relNorm p d m x * relNorm p d m y) ∧
      (∀ x : K, relNorm p d m x ∈ fixedSubfield K p d) ∧
      (∀ x : K, x ≠ 0 → relNorm p d m x ≠ 0) ∧
      (∀ a ∈ fixedSubfield K p d, relNorm p d m a = a) :=
  ⟨relNorm_mul d m, relNorm_mem_fixedSubfield hK hdm, fun _ hx => relNorm_ne_zero hx,
    fun _ ha => relNorm_eq_self_of_mem hm hdvd ha⟩

/-- **The normalized relative trace as an additive retraction onto `𝔽_{p^d}`.**
For `#K = p ^ n` with `n = d * m` and `p ∤ m`, the map `x ↦ (m : K)⁻¹ * ∑_{k<m} x ^ (p ^ (d k))`
is additive, `𝔽_{p^d}`-linear, sends `K` into `𝔽_{p^d}`, and fixes `𝔽_{p^d}` pointwise. -/
theorem relTrace_retraction_onto_fixedSubfield (hK : Nat.card K = p ^ n) (hdm : d * m = n)
    (hpm : ¬ (p ∣ m)) :
    (∀ x y : K, ((m : K))⁻¹ * relTrace p d m (x + y)
        = ((m : K))⁻¹ * relTrace p d m x + ((m : K))⁻¹ * relTrace p d m y) ∧
      (∀ x : K, ((m : K))⁻¹ * relTrace p d m x ∈ fixedSubfield K p d) ∧
      (∀ a ∈ fixedSubfield K p d, ((m : K))⁻¹ * relTrace p d m a = a) := by
  have hm0 : (m : K) ≠ 0 := by
    intro h
    exact hpm ((CharP.cast_eq_zero_iff K p m).1 h)
  refine ⟨fun x y => by rw [relTrace_add, mul_add], fun x => ?_, fun a ha => ?_⟩
  · have hmem : (m : K) ^ p ^ d = (m : K) := by
      have hcast : ((m : K)) ^ p = (m : K) := by
        have h : frobenius K p (m : K) = (m : K) := map_natCast (frobenius K p) m
        rwa [frobenius_def] at h
      exact pow_pow_char_eq_self hcast d
    have hinv : ((m : K))⁻¹ ^ p ^ d = ((m : K))⁻¹ := by rw [inv_pow, hmem]
    show (((m : K))⁻¹ * relTrace p d m x) ^ p ^ d = ((m : K))⁻¹ * relTrace p d m x
    rw [mul_pow, hinv, (relTrace_mem_fixedSubfield hK hdm x : _ ^ _ = _)]
  · rw [relTrace_of_mem (mem_fixedSubfield.1 ha), ← mul_assoc, inv_mul_cancel₀ hm0, one_mul]

end Retraction

end FrobeniusPrimeSubfield
