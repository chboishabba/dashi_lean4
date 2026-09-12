/-
# The modular discriminant and its `q`-expansion coefficients

The picture drawn in `RequestProject/ModularSvg.lean` is the graph of the `q`-expansion of the
modular discriminant

```
Δ(z) = η(z)^24 = q ∏_{m ≥ 1} (1 - q^m)^24 = ∑_{n ≥ 1} τ(n) qⁿ ,      q = e^{2πiz},
```

with the prime-power fibers of `RequestProject/PrimeFibers.lean` highlighted.

This file provides:

* `modularDelta`, the modular discriminant built from Mathlib's Dedekind eta function, with the
  product formula `modularDelta_eq_qParam_mul` and non-vanishing on the upper half-plane;
* `tau`, a *computable* version of the coefficient `τ(n)`, obtained from the truncated product
  `∏_{m = 1}^{n} (1 - X^m)^24`, together with the theorem `tau_eq_coeff_deltaPoly` saying that
  `tau n` really is the `n`-th coefficient of `X * ∏_{m = 1}^{N} (1 - X^m)^24` for every
  truncation level `N ≥ n` (so `tau` does not depend on the truncation);
* arithmetic of the highlighted points: the Hecke recursion
  `τ(p^{k+2}) = τ(p) τ(p^{k+1}) - p^11 τ(p^k)` along every fiber inside the displayed range,
  Ramanujan's congruence `τ(p) ≡ 1 + p^11 (mod 691)` for the first twenty primes, Deligne's
  bound `τ(n)² ≤ d(n)² n^11`, and non-vanishing of `τ` on the displayed range.
-/
import RequestProject.FiberColors
import Mathlib.NumberTheory.ModularForms.DedekindEta

namespace RamanujanTau

open Polynomial

/-! ## The modular discriminant -/

/-- The modular discriminant `Δ = η^24`, built from Mathlib's Dedekind eta function. -/
noncomputable def modularDelta (z : ℂ) : ℂ := ModularForm.eta z ^ 24

/-- The product formula `Δ(z) = q ∏' (1 - q^{n+1})^24` with `q = e^{2πiz}`. -/
theorem modularDelta_eq_qParam_mul (z : ℂ) :
    modularDelta z = Function.Periodic.qParam 1 z *
      (∏' n : ℕ, (1 - Function.Periodic.qParam 1 z ^ (n + 1))) ^ 24 := by
  have hq : (Function.Periodic.qParam 24 z) ^ 24 = Function.Periodic.qParam 1 z := by
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    norm_num
    ring_nf
  rw [modularDelta, ModularForm.eta, mul_pow, hq]

/-- `Δ` does not vanish on the upper half-plane. -/
theorem modularDelta_ne_zero {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    modularDelta z ≠ 0 :=
  pow_ne_zero _ (ModularForm.eta_ne_zero hz)

/-! ## The truncated eta product, as an array of coefficients -/

/-- Reading an entry of an array built as `(Array.range n).map f`. -/
theorem getElem!_rangeMap {f : ℕ → ℤ} {n i : ℕ} (h : i < n) :
    ((Array.range n).map f)[i]! = f i := by
  have h' : i < ((Array.range n).map f).size := by simpa using h
  rw [getElem!_pos ((Array.range n).map f) i h']
  simp

/-- Multiply a coefficient array by `1 - X^m` (coefficients beyond the length are dropped). -/
def mulOneSubXPow (a : Array ℤ) (m : ℕ) : Array ℤ :=
  (Array.range a.size).map (fun i => a[i]! - if m ≤ i then a[i - m]! else 0)

/-- Multiply a coefficient array by `(1 - X^m)^24`. -/
def mulFactor (a : Array ℤ) (m : ℕ) : Array ℤ := (fun b => mulOneSubXPow b m)^[24] a

/-- Coefficients (up to degree `N`) of `∏_{m = 1}^{M} (1 - X^m)^24`. -/
def etaArr (N : ℕ) : ℕ → Array ℤ
  | 0 => (Array.range (N + 1)).map (fun i => if i = 0 then (1 : ℤ) else 0)
  | M + 1 => mulFactor (etaArr N M) (M + 1)

/-- Ramanujan's `τ`: the coefficient of `qⁿ` in `Δ = q ∏ (1 - q^m)^24`. -/
def tau (n : ℕ) : ℤ := if n = 0 then 0 else (etaArr n n)[n - 1]!

/-- The truncated `q`-expansion of `Δ`, as a polynomial. -/
noncomputable def deltaPoly (N : ℕ) : Polynomial ℤ :=
  X * ∏ m ∈ Finset.Icc 1 N, (1 - X ^ m) ^ 24

/-! ## Correctness of the computation -/

theorem size_mulOneSubXPow (a : Array ℤ) (m : ℕ) : (mulOneSubXPow a m).size = a.size := by
  simp [mulOneSubXPow]

theorem getElem!_mulOneSubXPow {a : Array ℤ} {m i : ℕ} (hi : i < a.size) :
    (mulOneSubXPow a m)[i]! = a[i]! - if m ≤ i then a[i - m]! else 0 := by
  rw [mulOneSubXPow, getElem!_rangeMap hi]

/-- Multiplying a polynomial by `1 - X^m` on coefficients. -/
theorem coeff_mul_one_sub_X_pow (P : Polynomial ℤ) (m i : ℕ) :
    (P * (1 - X ^ m)).coeff i = P.coeff i - if m ≤ i then P.coeff (i - m) else 0 := by
  rw [mul_sub, mul_one, coeff_sub, Polynomial.coeff_mul_X_pow']

/-- An array `a` of length `N + 1` represents the polynomial `P` up to degree `N`. -/
def Represents (N : ℕ) (a : Array ℤ) (P : Polynomial ℤ) : Prop :=
  a.size = N + 1 ∧ ∀ i ≤ N, a[i]! = P.coeff i

theorem represents_mulOneSubXPow {N : ℕ} {a : Array ℤ} {P : Polynomial ℤ}
    (h : Represents N a P) (m : ℕ) :
    Represents N (mulOneSubXPow a m) (P * (1 - X ^ m)) := by
  obtain ⟨hsize, hrep⟩ := h
  refine ⟨by rw [size_mulOneSubXPow, hsize], fun i hi => ?_⟩
  have hi' : i < a.size := by omega
  rw [getElem!_mulOneSubXPow hi', coeff_mul_one_sub_X_pow, hrep i hi]
  by_cases hm : m ≤ i
  · simp only [hm, if_pos]
    rw [hrep (i - m) (by omega)]
  · simp [hm]

theorem represents_mulFactor {N : ℕ} {a : Array ℤ} {P : Polynomial ℤ}
    (h : Represents N a P) (m : ℕ) :
    Represents N (mulFactor a m) (P * (1 - X ^ m) ^ 24) := by
  have key : ∀ j : ℕ, ∀ b : Array ℤ, ∀ Q : Polynomial ℤ, Represents N b Q →
      Represents N ((fun c => mulOneSubXPow c m)^[j] b) (Q * (1 - X ^ m) ^ j) := by
    intro j
    induction j with
    | zero => intro b Q hb; simpa using hb
    | succ j ih =>
        intro b Q hb
        rw [Function.iterate_succ_apply]
        have h2 := ih (mulOneSubXPow b m) (Q * (1 - X ^ m)) (represents_mulOneSubXPow hb m)
        have heq : Q * (1 - X ^ m) * (1 - X ^ m) ^ j = Q * (1 - X ^ m) ^ (j + 1) := by ring
        rwa [heq] at h2
  exact key 24 a P h

theorem represents_etaArr (N M : ℕ) :
    Represents N (etaArr N M) (∏ m ∈ Finset.Icc 1 M, (1 - X ^ m) ^ 24) := by
  induction M with
  | zero =>
      refine ⟨by simp [etaArr], fun i hi => ?_⟩
      rw [etaArr, getElem!_rangeMap (show i < N + 1 by omega)]
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · simp
      · rw [if_neg (by omega)]
        simp [Polynomial.coeff_one, hpos.ne']
  | succ M ih =>
      rw [Finset.prod_Icc_succ_top (by omega), etaArr]
      exact represents_mulFactor ih (M + 1)

/-- The `24`-th power of `1 - X^m` is `1` plus something divisible by `X^m`. -/
theorem exists_one_add_X_pow_mul (m e : ℕ) :
    ∃ Q : Polynomial ℤ, (1 - X ^ m) ^ e = 1 + X ^ m * Q := by
  induction e with
  | zero => exact ⟨0, by simp⟩
  | succ e ih =>
      obtain ⟨Q, hQ⟩ := ih
      refine ⟨Q - 1 - X ^ m * Q, ?_⟩
      rw [pow_succ, hQ]; ring

/-- Multiplying by a factor `(1 - X^m)^24` with `m > i` does not change the `i`-th
coefficient. -/
theorem coeff_mul_factor_of_lt {P : Polynomial ℤ} {m i : ℕ} (h : i < m) :
    (P * (1 - X ^ m) ^ 24).coeff i = P.coeff i := by
  obtain ⟨Q, hQ⟩ := exists_one_add_X_pow_mul m 24
  have hrw : P * (1 - X ^ m) ^ 24 = P + (P * Q) * X ^ m := by rw [hQ]; ring
  rw [hrw, coeff_add, Polynomial.coeff_mul_X_pow', if_neg (by omega), add_zero]

/-- The truncation level does not matter: for `i ≤ M ≤ M'` the `i`-th coefficients of the
product over `m ≤ M` and over `m ≤ M'` agree. -/
theorem coeff_prod_stable {i M M' : ℕ} (hiM : i ≤ M) (hMM' : M ≤ M') :
    (∏ m ∈ Finset.Icc 1 M', (1 - X ^ m) ^ 24 : Polynomial ℤ).coeff i =
      (∏ m ∈ Finset.Icc 1 M, (1 - X ^ m) ^ 24 : Polynomial ℤ).coeff i := by
  induction M' with
  | zero =>
      have hM : M = 0 := by omega
      subst hM; rfl
  | succ M' ih =>
      rcases Nat.lt_or_ge M (M' + 1) with hlt | hge
      · rw [Finset.prod_Icc_succ_top (by omega), coeff_mul_factor_of_lt (by omega)]
        exact ih (by omega)
      · have hM : M = M' + 1 := by omega
        subst hM; rfl

/-- `tau n` is the `n`-th coefficient of the truncated `q`-expansion of `Δ`, for any truncation
level `N ≥ n`; in particular it does not depend on the truncation. -/
theorem tau_eq_coeff_deltaPoly {n N : ℕ} (hn : 0 < n) (hN : n ≤ N) :
    tau n = (deltaPoly N).coeff n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have h1 : tau (j + 1)
      = (∏ m ∈ Finset.Icc 1 (j + 1), (1 - X ^ m) ^ 24 : Polynomial ℤ).coeff j := by
    rw [tau, if_neg (by omega)]
    exact (represents_etaArr (j + 1) (j + 1)).2 j (by omega)
  have h2 : (deltaPoly N).coeff (j + 1)
      = (∏ m ∈ Finset.Icc 1 N, (1 - X ^ m) ^ 24 : Polynomial ℤ).coeff j := by
    rw [deltaPoly, Polynomial.coeff_X_mul]
  rw [h1, h2, coeff_prod_stable (show j ≤ j + 1 by omega) hN]

/-! ## Small values -/

theorem tau_zero : tau 0 = 0 := rfl

theorem tau_one : tau 1 = 1 := by native_decide

theorem tau_two : tau 2 = -24 := by native_decide

theorem tau_three : tau 3 = 252 := by native_decide

theorem tau_four : tau 4 = -1472 := by native_decide

theorem tau_five : tau 5 = 4830 := by native_decide

/-! ## Arithmetic along the highlighted fibers -/

/-- The number of integers drawn in the picture. -/
def displayN : ℕ := 256

private def heckeCheck : Bool :=
  PrimeFibers.primeList.all fun p =>
    (List.range 9).all fun k =>
      decide (displayN < p ^ (k + 2)) ||
        (tau (p ^ (k + 2)) == tau p * tau (p ^ (k + 1)) - (p : ℤ) ^ 11 * tau (p ^ k))

private theorem heckeCheck_true : heckeCheck = true := by native_decide

/-- **Hecke recursion along a fiber.** For each of the first twenty primes `p`, the highlighted
points `p^k` of its fiber inside the displayed range satisfy
`τ(p^{k+2}) = τ(p) τ(p^{k+1}) - p^{11} τ(p^k)`. -/
theorem tau_hecke_on_fiber {p k : ℕ} (hp : p ∈ PrimeFibers.first20Primes)
    (hk : p ^ (k + 2) ≤ displayN) :
    tau (p ^ (k + 2)) = tau p * tau (p ^ (k + 1)) - (p : ℤ) ^ 11 * tau (p ^ k) := by
  have hp2 : 2 ≤ p := (PrimeFibers.prime_of_mem_first20Primes hp).two_le
  have hk9 : k < 9 := by
    by_contra hc
    have h1 : 2 ^ (k + 2) ≤ p ^ (k + 2) := Nat.pow_le_pow_left hp2 _
    have h2 : 2 ^ 11 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [displayN] at hk
    omega
  have h := heckeCheck_true
  rw [heckeCheck, List.all_eq_true] at h
  have hk' := (List.all_eq_true.1 (h p (PrimeFibers.mem_primeList_iff.2 hp))) k
    (List.mem_range.2 hk9)
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hk'
  rcases hk' with hlt | heq
  · omega
  · exact heq

private def ramanujanCheck : Bool :=
  PrimeFibers.primeList.all fun p => (tau p - (1 + (p : ℤ) ^ 11)) % 691 == 0

private theorem ramanujanCheck_true : ramanujanCheck = true := by native_decide

/-- **Ramanujan's congruence** `τ(p) ≡ 1 + p^{11} (mod 691)`, for each of the twenty
highlighted primes. -/
theorem tau_congr_691 {p : ℕ} (hp : p ∈ PrimeFibers.first20Primes) :
    (691 : ℤ) ∣ tau p - (1 + (p : ℤ) ^ 11) := by
  have h := ramanujanCheck_true
  rw [ramanujanCheck, List.all_eq_true] at h
  have h2 := h p (PrimeFibers.mem_primeList_iff.2 hp)
  simp only [beq_iff_eq] at h2
  exact Int.dvd_of_emod_eq_zero h2

private def deligneCheck : Bool :=
  (List.range (displayN + 1)).all fun n =>
    decide (tau n ^ 2 ≤ ((n.divisors.card : ℤ)) ^ 2 * (n : ℤ) ^ 11)

private theorem deligneCheck_true : deligneCheck = true := by native_decide

/-- **Deligne's bound** `τ(n)² ≤ d(n)² n^{11}`, verified over the displayed range: this is what
sets the vertical scale of the picture. -/
theorem tau_sq_le_deligne {n : ℕ} (hn : n ≤ displayN) :
    tau n ^ 2 ≤ ((n.divisors.card : ℤ)) ^ 2 * (n : ℤ) ^ 11 := by
  have h := deligneCheck_true
  rw [deligneCheck, List.all_eq_true] at h
  have h2 := h n (List.mem_range.2 (by omega))
  simpa using h2

private def nonvanishingCheck : Bool :=
  (List.range displayN).all fun n => !(tau (n + 1) == 0)

private theorem nonvanishingCheck_true : nonvanishingCheck = true := by native_decide

/-- `τ` does not vanish on the displayed range (Lehmer's conjecture, checked for `n ≤ 256`):
every plotted point is off the axis. -/
theorem tau_ne_zero_of_le {n : ℕ} (hn : 0 < n) (hn' : n ≤ displayN) : tau n ≠ 0 := by
  have h := nonvanishingCheck_true
  rw [nonvanishingCheck, List.all_eq_true] at h
  have h2 := h (n - 1) (List.mem_range.2 (by omega))
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h2
  rwa [Nat.sub_add_cancel hn] at h2

end RamanujanTau
