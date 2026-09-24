/-
# The factors of the Monster versus the factors of the zeta function

The order of the Monster group is a finite product of prime powers,

```
|M| = 2^46 · 3^20 · 5^9 · 7^6 · 11^2 · 13^3 · 17 · 19 · 23 · 29 · 31 · 41 · 47 · 59 · 71,
```

while the Riemann zeta function is an infinite product of local factors,

```
ζ(s) = ∏_p (1 - p^{-s})⁻¹ ,     Re s > 1.
```

This file compares the two, over the real line `s > 1`:

* `Sporadic.monsterDivisorSum s = ∑_{d ∣ |M|} d^{-s}` factors as a product of *truncated*
  Euler factors, one for each prime dividing `|M|`, truncated at exactly the exponent that
  prime carries in `|M|` (`Sporadic.monsterDivisorSum_eq_prod`);
* each truncated factor `∑_{j ≤ e} p^{-js}` sits below the corresponding zeta factor
  `(1 - p^{-s})⁻¹`, with the exact defect `p^{-(e+1)s} (1 - p^{-s})⁻¹`
  (`Sporadic.eulerFactor_sub_truncFactor`);
* the whole Monster contribution is dominated by the fifteen-factor sub-product of ζ's Euler
  product, which in turn is dominated by ζ itself:
  `monsterDivisorSum s ≤ monsterEulerProduct s ≤ ζ(s)`
  (`Sporadic.monsterDivisorSum_le_monsterEulerProduct`,
  `Sporadic.monsterEulerProduct_le_zeta`).

The real series `Sporadic.zetaR s = ∑' n, n^{-s}` is identified with Mathlib's
`riemannZeta` in `Sporadic.ofReal_zetaR`, so these really are statements about ζ.
-/
import Mathlib
import RequestProject.SporadicGroups

open Finset Filter ArithmeticFunction

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Sporadic

variable {s : ℝ}

/-! ## The zeta function on the real axis -/

/-- The Riemann zeta function on the real axis, as the Dirichlet series `∑ n^{-s}`
(the `n = 0` term is `0`). -/
noncomputable def zetaR (s : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-s)

theorem summable_rpow (hs : 1 < s) : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
  Real.summable_nat_rpow.mpr (by linarith)

/-- `zetaR` is the Riemann zeta function: on the real axis `s > 1` it agrees with Mathlib's
`riemannZeta`. -/
theorem ofReal_zetaR (hs : 1 < s) : ((zetaR s : ℝ) : ℂ) = riemannZeta (s : ℂ) := by
  rw [zetaR, zeta_eq_tsum_one_div_nat_cpow (by simpa using hs), Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have h1 : ((0 : ℕ) : ℝ) ^ (-s) = 0 := by
      rw [Nat.cast_zero]
      exact Real.zero_rpow (neg_ne_zero.mpr (by linarith : s ≠ 0))
    have h2 : ((0 : ℕ) : ℂ) ^ (s : ℂ) = 0 := by
      rw [Nat.cast_zero]
      exact Complex.zero_cpow (by simpa using (by linarith : s ≠ 0))
    rw [h1, h2]
    simp
  · rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    rw [Complex.cpow_neg, ← one_div]

/-- Any finite sum of `d^{-s}` over distinct positive integers is at most `ζ(s)`. -/
theorem sum_le_zetaR (hs : 1 < s) (A : Finset ℕ) : ∑ d ∈ A, (d : ℝ) ^ (-s) ≤ zetaR s :=
  Summable.sum_le_tsum A (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _) (summable_rpow hs)

/-! ## Local factors -/

/-- The Euler factor of `ζ` at the prime `p`. -/
noncomputable def eulerFactor (p : ℕ) (s : ℝ) : ℝ := (1 - (p : ℝ) ^ (-s))⁻¹

/-- The Euler factor of `ζ` at `p`, truncated at the exponent `e`: this is the local factor
contributed by a group order that is divisible by exactly `p ^ e`. -/
noncomputable def truncFactor (p e : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (e + 1), ((p : ℝ) ^ (-s)) ^ j

theorem rpow_neg_mem_Ioo {p : ℕ} (hp : 2 ≤ p) (hs : 0 < s) : (p : ℝ) ^ (-s) ∈ Set.Ioo 0 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
  constructor
  · exact Real.rpow_pos_of_pos (by linarith) _
  · exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)

/-- The truncated factor is the partial sum of the geometric series whose total is the Euler
factor. -/
theorem truncFactor_eq {p : ℕ} (hp : 2 ≤ p) (hs : 0 < s) (e : ℕ) :
    truncFactor p e s = (1 - ((p : ℝ) ^ (-s)) ^ (e + 1)) * eulerFactor p s := by
  obtain ⟨hx0, hx1⟩ := rpow_neg_mem_Ioo hp hs
  set x : ℝ := (p : ℝ) ^ (-s) with hx
  have hne : x ≠ 1 := ne_of_lt hx1
  have h1 : (1 : ℝ) - x ≠ 0 := by linarith
  have hneg : (1 - x)⁻¹ = -(x - 1)⁻¹ := by
    rw [show (1 : ℝ) - x = -(x - 1) by ring, inv_neg]
  rw [truncFactor, geom_sum_eq hne, eulerFactor, ← hx, hneg, div_eq_mul_inv]
  ring

/-- The zeta Euler factor exceeds the truncated one by exactly `p^{-(e+1)s}` times itself. -/
theorem eulerFactor_sub_truncFactor {p : ℕ} (hp : 2 ≤ p) (hs : 0 < s) (e : ℕ) :
    eulerFactor p s - truncFactor p e s = ((p : ℝ) ^ (-s)) ^ (e + 1) * eulerFactor p s := by
  rw [truncFactor_eq hp hs]
  ring

theorem eulerFactor_pos {p : ℕ} (hp : 2 ≤ p) (hs : 0 < s) : 0 < eulerFactor p s := by
  obtain ⟨hx0, hx1⟩ := rpow_neg_mem_Ioo hp hs
  exact inv_pos.mpr (by linarith)

theorem one_le_eulerFactor {p : ℕ} (hp : 2 ≤ p) (hs : 0 < s) : 1 ≤ eulerFactor p s := by
  obtain ⟨hx0, hx1⟩ := rpow_neg_mem_Ioo hp hs
  rw [eulerFactor, le_inv_comm₀ (by norm_num) (by linarith)]
  linarith

theorem truncFactor_pos {p : ℕ} (hp : 2 ≤ p) (hs : 0 < s) (e : ℕ) : 0 < truncFactor p e s := by
  obtain ⟨hx0, hx1⟩ := rpow_neg_mem_Ioo hp hs
  refine Finset.sum_pos (fun j _ => pow_pos hx0 j) ⟨0, by simp⟩

/-- Truncating the Euler factor can only decrease it. -/
theorem truncFactor_le_eulerFactor {p : ℕ} (hp : 2 ≤ p) (hs : 0 < s) (e : ℕ) :
    truncFactor p e s ≤ eulerFactor p s := by
  obtain ⟨hx0, hx1⟩ := rpow_neg_mem_Ioo hp hs
  have h := eulerFactor_sub_truncFactor hp hs e
  have hnn : 0 ≤ ((p : ℝ) ^ (-s)) ^ (e + 1) * eulerFactor p s :=
    mul_nonneg (pow_nonneg hx0.le _) (eulerFactor_pos hp hs).le
  linarith

/-! ## The divisor sum of a natural number as a product of truncated Euler factors -/

/-- `n ↦ n^{-s}` as an arithmetic function. -/
noncomputable def rpowAF (s : ℝ) : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else (n : ℝ) ^ (-s)
  map_zero' := by simp

theorem rpowAF_apply (s : ℝ) {n : ℕ} (hn : n ≠ 0) : rpowAF s n = (n : ℝ) ^ (-s) := if_neg hn

theorem isMultiplicative_rpowAF (s : ℝ) : (rpowAF s).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [rpowAF], ?_⟩
  intro m n hm hn _
  rw [rpowAF_apply s (mul_ne_zero hm hn), rpowAF_apply s hm, rpowAF_apply s hn]
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity)]

/-- **The finite Euler product of a divisor sum.** For any `n ≠ 0`,
`∑_{d ∣ n} d^{-s}` is the product over the primes dividing `n` of the Euler factor of `ζ`
truncated at the exponent of that prime in `n`. -/
theorem sum_divisors_rpow_eq_prod (s : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (d : ℝ) ^ (-s)
      = ∏ p ∈ n.primeFactors, truncFactor p (n.factorization p) s := by
  have hmul : (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) *
      rpowAF s).IsMultiplicative :=
    isMultiplicative_zeta.natCast.mul (isMultiplicative_rpowAF s)
  have key := ArithmeticFunction.IsMultiplicative.multiplicative_factorization _ hmul hn
  rw [ArithmeticFunction.coe_zeta_mul_apply] at key
  have hL : ∑ d ∈ n.divisors, rpowAF s d = ∑ d ∈ n.divisors, (d : ℝ) ^ (-s) :=
    Finset.sum_congr rfl fun d hd => rpowAF_apply s (Nat.pos_of_mem_divisors hd).ne'
  rw [hL] at key
  rw [key, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hpp, truncFactor]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rpowAF_apply s (pow_ne_zero _ hpp.pos.ne')]
  push_cast
  rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) j, ← Real.rpow_natCast (p : ℝ) j,
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
  ring_nf

/-! ## The Monster -/

/-- The Dirichlet-series mass carried by the divisors of the order of the Monster. -/
noncomputable def monsterDivisorSum (s : ℝ) : ℝ := ∑ d ∈ monsterOrder.divisors, (d : ℝ) ^ (-s)

/-- The product of the fifteen zeta Euler factors at the primes dividing `|M|`. -/
noncomputable def monsterEulerProduct (s : ℝ) : ℝ := ∏ p ∈ monsterPrimes, eulerFactor p s

/-- **The Monster's factors are truncated zeta factors.** The divisor sum of `|M|` is the
product, over the fifteen supersingular primes, of the Euler factor of `ζ` truncated at the
exponent that prime carries in `|M|` — `46` for `2`, `20` for `3`, `9` for `5`, and so on. -/
theorem monsterDivisorSum_eq_prod (s : ℝ) :
    monsterDivisorSum s = ∏ p ∈ monsterPrimes, truncFactor p (monsterOrder.factorization p) s := by
  rw [monsterDivisorSum, sum_divisors_rpow_eq_prod s monsterOrder_ne_zero,
    primeFactors_monsterOrder]

/-- The same, with the exponents spelled out. -/
theorem monsterDivisorSum_eq_explicit (s : ℝ) :
    monsterDivisorSum s =
      truncFactor 2 46 s * (truncFactor 3 20 s * (truncFactor 5 9 s * (truncFactor 7 6 s *
      (truncFactor 11 2 s * (truncFactor 13 3 s * (truncFactor 17 1 s * (truncFactor 19 1 s *
      (truncFactor 23 1 s * (truncFactor 29 1 s * (truncFactor 31 1 s * (truncFactor 41 1 s *
      (truncFactor 47 1 s * (truncFactor 59 1 s * (truncFactor 71 1 s)))))))))))))) := by
  rw [monsterDivisorSum_eq_prod]
  have h : ∀ p ∈ monsterPrimes,
      truncFactor p (monsterOrder.factorization p) s = truncFactor p (monster.exponent p) s :=
    fun p _ => by rw [monsterOrder, exponent_eq_factorization monster_mem p]
  rw [Finset.prod_congr rfl h, monsterPrimes]
  repeat rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_singleton]
  norm_num [monster, Group.exponent]

/-- Every truncated Monster factor is dominated by the corresponding zeta Euler factor. -/
theorem monsterDivisorSum_le_monsterEulerProduct (hs : 0 < s) :
    monsterDivisorSum s ≤ monsterEulerProduct s := by
  rw [monsterDivisorSum_eq_prod, monsterEulerProduct]
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · have hp2 : 2 ≤ p := (prime_of_mem_sporadicPrimes p (monsterPrimes_subset hp)).two_le
    exact (truncFactor_pos hp2 hs _).le
  · have hp2 : 2 ≤ p := (prime_of_mem_sporadicPrimes p (monsterPrimes_subset hp)).two_le
    exact truncFactor_le_eulerFactor hp2 hs _

/-! ## The Euler product of ζ over the Monster's primes -/

/-- Transfer of a convergent infinite product from `ℂ` back to `ℝ`. -/
theorem hasProd_real_of_complex {ι : Type*} (f : ι → ℝ) (a : ℝ)
    (h : HasProd (fun i => ((f i : ℝ) : ℂ)) ((a : ℝ) : ℂ)) : HasProd f a := by
  rw [HasProd] at h ⊢
  refine tendsto_ofReal_iff.mp ?_
  simpa [Function.comp_def, Complex.ofReal_prod] using h

/-- The Euler product of `ζ` on the real axis: the family of local factors
`(1 - p^{-s})⁻¹` has product `ζ(s)` for real `s > 1`. -/
theorem hasProd_eulerFactor (hs : 1 < s) :
    HasProd (fun p : Nat.Primes => eulerFactor (p : ℕ) s) (zetaR s) := by
  refine hasProd_real_of_complex _ _ ?_
  rw [ofReal_zetaR hs]
  have h := riemannZeta_eulerProduct_hasProd (s := (s : ℂ)) (by simpa using hs)
  convert h using 2 with p
  rw [eulerFactor]
  push_cast
  rw [Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ))]
  push_cast
  ring_nf

/-- A finite partial product of a convergent product of factors `≥ 1` is at most the total
product. -/
theorem finset_prod_le_of_hasProd {ι : Type*} (f : ι → ℝ) (a : ℝ) (h : HasProd f a)
    (S : Finset ι) (hf : ∀ i, 1 ≤ f i) : ∏ i ∈ S, f i ≤ a := by
  classical
  have htend : Tendsto (fun T : Finset ι => ∏ i ∈ T, f i) atTop (nhds a) := h
  refine ge_of_tendsto htend ?_
  filter_upwards [Filter.eventually_ge_atTop S] with T hT
  have hsplit : ∏ i ∈ T, f i = (∏ i ∈ S, f i) * ∏ i ∈ T \ S, f i := by
    rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hT]
  have h1 : (1 : ℝ) ≤ ∏ i ∈ T \ S, f i := by
    calc (1 : ℝ) = ∏ _i ∈ T \ S, (1 : ℝ) := by simp
      _ ≤ ∏ i ∈ T \ S, f i := Finset.prod_le_prod (fun i _ => zero_le_one) (fun i _ => hf i)
  have h0 : 0 ≤ ∏ i ∈ S, f i := Finset.prod_nonneg fun i _ => le_trans zero_le_one (hf i)
  rw [hsplit]
  exact le_mul_of_one_le_right h0 h1

/-- Any finite set of primes contributes at most `ζ(s)` to the Euler product. -/
theorem prod_eulerFactor_le_zeta (hs : 1 < s) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, eulerFactor p s ≤ zetaR s := by
  classical
  have hconv : ∏ q ∈ S.attach.image (fun p => (⟨p.1, hS p.1 p.2⟩ : Nat.Primes)),
      eulerFactor (q : ℕ) s = ∏ p ∈ S, eulerFactor p s := by
    rw [Finset.prod_image (by rintro ⟨a, ha⟩ _ ⟨b, hb⟩ _ h; simpa [Subtype.ext_iff] using h)]
    exact Finset.prod_attach S (fun p => eulerFactor p s)
  rw [← hconv]
  refine finset_prod_le_of_hasProd _ _ (hasProd_eulerFactor hs) _ (fun q => ?_)
  exact one_le_eulerFactor q.2.two_le (by linarith)

/-- The fifteen Euler factors of `ζ` at the Monster's primes have product at most `ζ(s)`. -/
theorem monsterEulerProduct_le_zeta (hs : 1 < s) : monsterEulerProduct s ≤ zetaR s :=
  prod_eulerFactor_le_zeta hs monsterPrimes
    (fun p hp => prime_of_mem_sporadicPrimes p (monsterPrimes_subset hp))

/-- **The comparison.** For every real `s > 1`, the Dirichlet mass of the divisors of the
Monster's order is at most the product of the fifteen zeta Euler factors at the primes of the
Monster, and that in turn is at most `ζ(s)`. -/
theorem monsterDivisorSum_le_zeta (hs : 1 < s) : monsterDivisorSum s ≤ zetaR s :=
  le_trans (monsterDivisorSum_le_monsterEulerProduct (by linarith)) (monsterEulerProduct_le_zeta hs)

/-! ## The comparison at `s = 2` -/

/-- `ζ(2) = π²/6`, on the real axis. -/
theorem zetaR_two : zetaR 2 = Real.pi ^ 2 / 6 := by
  have h : ((zetaR 2 : ℝ) : ℂ) = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
    rw [ofReal_zetaR (by norm_num)]
    push_cast
    simpa using riemannZeta_two
  exact_mod_cast h

/-- At `s = 2`: the fifteen Euler factors of `ζ` at the Monster's primes, and a fortiori the
divisor sum of `|M|`, stay below `π²/6`. -/
theorem monsterEulerProduct_two_le : monsterEulerProduct 2 ≤ Real.pi ^ 2 / 6 := by
  rw [← zetaR_two]
  exact monsterEulerProduct_le_zeta (by norm_num)

theorem monsterDivisorSum_two_le : monsterDivisorSum 2 ≤ Real.pi ^ 2 / 6 := by
  rw [← zetaR_two]
  exact monsterDivisorSum_le_zeta (by norm_num)

end Sporadic
