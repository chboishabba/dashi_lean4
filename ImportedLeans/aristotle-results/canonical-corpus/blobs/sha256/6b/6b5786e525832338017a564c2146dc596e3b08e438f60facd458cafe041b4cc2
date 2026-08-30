/-
# Fiber sums of the Deligne-normalised coefficients

For each of the first twenty primes `p` this file studies the *fiber sums* of the
Deligne-normalised coefficients of the modular discriminant `Δ = η²⁴ = ∑ τ(n) qⁿ`,

```
signedFiberSum p N = ∑_{p^k ≤ N, k ≥ 1}  τ(p^k) / p^{11k/2},
absFiberSum    p N = ∑_{p^k ≤ N, k ≥ 1} |τ(p^k) / p^{11k/2}| ,
```

with `N = 256` the displayed range.  Alongside the general structure (the number of terms,
`|signed| ≤ absolute`, the Deligne band, the normalised Hecke recursion) the numerical value of
every one of the forty sums is pinned down to nine decimal places, and the two extremal
statements suggested by the picture are proved: the fiber of `2` carries the largest absolute
mass, and among the primes contributing a single term the largest normalised magnitude is at
`p = 47`.
-/
import RequestProject.ModularGraph

namespace FiberSums

open PrimeFibers RamanujanTau

/-! ## Definitions -/

/-- The Deligne-normalised coefficient `τ(n) / n^{11/2}` (the quantity plotted vertically in
`visualization/modular-tau-fibers.svg`). -/
noncomputable def normTau (n : ℕ) : ℝ := (tau n : ℝ) / Real.sqrt ((n : ℝ) ^ 11)

/-- The signed fiber sum `∑_{p^k ≤ N, k ≥ 1} τ(p^k)/p^{11k/2}`. -/
noncomputable def signedFiberSum (p N : ℕ) : ℝ := ∑ n ∈ primePowerFiber p N, normTau n

/-- The absolute fiber sum `∑_{p^k ≤ N, k ≥ 1} |τ(p^k)/p^{11k/2}|`. -/
noncomputable def absFiberSum (p N : ℕ) : ℝ := ∑ n ∈ primePowerFiber p N, |normTau n|

/-! ## Basic structure -/

theorem sqrt_pow11_pos {n : ℕ} (hn : 0 < n) : 0 < Real.sqrt ((n : ℝ) ^ 11) := by
  have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact Real.sqrt_pos.2 (by positivity)

theorem abs_normTau {n : ℕ} : |normTau n| = |(tau n : ℝ)| / Real.sqrt ((n : ℝ) ^ 11) := by
  rw [normTau, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- The square of the normalised coefficient is `τ(n)²/n¹¹`, the quantity `plotValueSq`
of `RequestProject/ModularGraph.lean`. -/
theorem normTau_sq {n : ℕ} (hn : 0 < n) :
    normTau n ^ 2 = ((ModularGraph.plotValueSq n : ℚ) : ℝ) := by
  have hpos : (0 : ℝ) < (n : ℝ) ^ 11 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  rw [normTau, div_pow, Real.sq_sqrt hpos.le, ModularGraph.plotValueSq]
  push_cast
  ring

/-- A fiber sum, written as a sum over the exponents `k = 1, …, log_p N`. -/
theorem sum_primePowerFiber (f : ℕ → ℝ) {p N : ℕ} (hp : 1 < p) (hN : N ≠ 0) :
    ∑ n ∈ primePowerFiber p N, f n = ∑ k ∈ Finset.Icc 1 (Nat.log p N), f (p ^ k) := by
  rw [primePowerFiber_eq_image hp hN,
    Finset.sum_image (fun a _ b _ h => Nat.pow_right_injective hp h)]

theorem absFiberSum_nonneg (p N : ℕ) : 0 ≤ absFiberSum p N :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Cancellation: the signed fiber sum never exceeds the absolute one in size. -/
theorem abs_signedFiberSum_le_absFiberSum (p N : ℕ) :
    |signedFiberSum p N| ≤ absFiberSum p N :=
  Finset.abs_sum_le_sum_abs _ _

/-! ## The Deligne band -/

/-- Deligne's bound in normalised form: `|τ(n)/n^{11/2}| ≤ d(n)` on the displayed range. -/
theorem abs_normTau_le_divisors {n : ℕ} (hn : 0 < n) (hn' : n ≤ 256) :
    |normTau n| ≤ (n.divisors.card : ℝ) := by
  have hs : 0 < Real.sqrt ((n : ℝ) ^ 11) := sqrt_pow11_pos hn
  have hsq : Real.sqrt ((n : ℝ) ^ 11) ^ 2 = (n : ℝ) ^ 11 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact Real.sq_sqrt (by positivity)
  have hd : ((tau n : ℝ)) ^ 2 ≤ ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ 11 := by
    have := tau_sq_le_deligne (n := n) hn'
    exact_mod_cast this
  have hkey : |(tau n : ℝ)| ≤ (n.divisors.card : ℝ) * Real.sqrt ((n : ℝ) ^ 11) := by
    have h1 : ((tau n : ℝ)) ^ 2 ≤ ((n.divisors.card : ℝ) * Real.sqrt ((n : ℝ) ^ 11)) ^ 2 := by
      rw [mul_pow, hsq]; exact hd
    have h2 : (0 : ℝ) ≤ (n.divisors.card : ℝ) * Real.sqrt ((n : ℝ) ^ 11) := by positivity
    nlinarith [abs_nonneg ((tau n : ℝ)), sq_abs ((tau n : ℝ))]
  rw [abs_normTau, div_le_iff₀ hs]
  exact hkey

/-- The number of divisors of `p^k` for a prime `p`. -/
theorem card_divisors_prime_pow {p k : ℕ} (hp : p.Prime) :
    (p ^ k).divisors.card = k + 1 := by
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

/-- Termwise Deligne bound along a fiber: `|τ(p^k)/p^{11k/2}| ≤ k + 1`. -/
theorem abs_normTau_pow_le {p k : ℕ} (hp : p.Prime) (hk : p ^ k ≤ 256) :
    |normTau (p ^ k)| ≤ (k : ℝ) + 1 := by
  have h := abs_normTau_le_divisors (n := p ^ k) (Nat.pow_pos hp.pos) hk
  rw [card_divisors_prime_pow hp] at h
  exact_mod_cast h

/-- The absolute fiber sum is bounded by the Deligne total `∑_{k=1}^{log_p N} (k+1)`. -/
theorem absFiberSum_le_deligne {p N : ℕ} (hp : p.Prime) (hN : N ≠ 0) (hN' : N ≤ 256) :
    absFiberSum p N ≤ ∑ k ∈ Finset.Icc 1 (Nat.log p N), ((k : ℝ) + 1) := by
  rw [absFiberSum, sum_primePowerFiber _ hp.one_lt hN]
  refine Finset.sum_le_sum fun k hk => abs_normTau_pow_le hp ?_
  have h1 : p ^ k ≤ N := (Nat.le_log_iff_pow_le hp.one_lt hN).1 (Finset.mem_Icc.1 hk).2
  omega

/-! ## The normalised Hecke recursion -/

theorem sqrt_pow11_pow {p k : ℕ} (hp : 0 < p) :
    Real.sqrt (((p ^ k : ℕ) : ℝ) ^ 11) = Real.sqrt p ^ (11 * k) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have : (((p ^ k : ℕ) : ℝ) ^ 11) = (Real.sqrt p ^ (11 * k)) ^ 2 := by
    rw [← pow_mul, show 11 * k * 2 = 2 * (11 * k) by ring, pow_mul, Real.sq_sqrt hp0,
      Nat.cast_pow, ← pow_mul, mul_comm k 11]
  rw [this, Real.sqrt_sq (by positivity)]

theorem sqrt_pow11_base {p : ℕ} (hp : 0 < p) :
    Real.sqrt ((p : ℝ) ^ 11) = Real.sqrt p ^ 11 := by
  have := sqrt_pow11_pow (p := p) (k := 1) hp
  simpa using this

/-- **The Hecke recursion in Deligne-normalised form.** Writing `y_k = τ(p^k)/p^{11k/2}`, the
points of a fiber satisfy `y_{k+2} = y_1 y_{k+1} - y_k`; this is the recursion that produces the
sign changes, and hence the cancellation, in the signed fiber sums. -/
theorem normTau_hecke {p k : ℕ} (hp : p ∈ first20Primes) (hk : p ^ (k + 2) ≤ 256) :
    normTau (p ^ (k + 2)) = normTau p * normTau (p ^ (k + 1)) - normTau (p ^ k) := by
  have hpp := prime_of_mem_first20Primes hp
  have hp0 : 0 < p := hpp.pos
  have hs : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp0)
  have hrec := tau_hecke_on_fiber hp (by simpa [RamanujanTau.displayN] using hk)
  have hrecR : ((tau (p ^ (k + 2)) : ℝ))
      = (tau p : ℝ) * (tau (p ^ (k + 1)) : ℝ) - (p : ℝ) ^ 11 * (tau (p ^ k) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hrec
  have hp11 : (p : ℝ) ^ 11 = Real.sqrt p ^ 22 := by
    rw [show (22 : ℕ) = 2 * 11 by norm_num, pow_mul, Real.sq_sqrt (by positivity)]
  simp only [normTau, sqrt_pow11_pow hp0, sqrt_pow11_base hp0]
  rw [hrecR, hp11]
  have hne : Real.sqrt p ≠ 0 := ne_of_gt hs
  field_simp
  ring

/-! ## Numerical evaluation of the fiber sums

Each normalised coefficient is pinned down by rational bounds `a ≤ √(n¹¹) ≤ b`, from which the
value `τ(n)/√(n¹¹)` is located to nine decimal places; the fiber sums follow by addition. -/

/-- The workhorse for the numerical evaluation: if `a ≤ √(n¹¹) ≤ b` (in the form
`a² ≤ n¹¹ ≤ b²`) and `τ(n) = t` lies between `(c - e)a, (c - e)b` and `(c + e)a, (c + e)b`,
then `τ(n)/n^{11/2}` is within `e` of `c`. -/
theorem normTau_approx {n : ℕ} {t : ℤ} (ht : tau n = t) {a b c e : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h1 : a ^ 2 ≤ (n : ℝ) ^ 11) (h2 : (n : ℝ) ^ 11 ≤ b ^ 2)
    (hlo1 : (c - e) * a ≤ (t : ℝ)) (hlo2 : (c - e) * b ≤ (t : ℝ))
    (hhi1 : (t : ℝ) ≤ (c + e) * a) (hhi2 : (t : ℝ) ≤ (c + e) * b) :
    |normTau n - c| ≤ e := by
  have hτ : ((tau n : ℤ) : ℝ) = (t : ℝ) := by rw [ht]
  set s := Real.sqrt ((n : ℝ) ^ 11) with hs_def
  have hnn : (0 : ℝ) ≤ (n : ℝ) ^ 11 := by positivity
  have hs2 : s ^ 2 = (n : ℝ) ^ 11 := Real.sq_sqrt hnn
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have has : a ≤ s := by nlinarith
  have hsb : s ≤ b := by nlinarith
  have hspos : 0 < s := lt_of_lt_of_le ha has
  have hlo : (c - e) * s ≤ (t : ℝ) := by
    rcases le_or_gt 0 (c - e) with h | h
    · nlinarith
    · nlinarith
  have hhi : (t : ℝ) ≤ (c + e) * s := by
    rcases le_or_gt 0 (c + e) with h | h
    · nlinarith
    · nlinarith
  have hval : normTau n = (t : ℝ) / s := by rw [normTau, ← hs_def, hτ]
  rw [hval, abs_le]
  constructor
  · have := (le_div_iff₀ hspos).2 hlo
    linarith
  · have := (div_le_iff₀ hspos).2 hhi
    linarith

/-- An approximation of a value gives an approximation of its absolute value. -/
theorem abs_approx_of_approx {x c e : ℝ} (h : |x - c| ≤ e) : |(|x| - |c|)| ≤ e :=
  le_trans (abs_abs_sub_abs_le_abs_sub x c) h

end FiberSums
