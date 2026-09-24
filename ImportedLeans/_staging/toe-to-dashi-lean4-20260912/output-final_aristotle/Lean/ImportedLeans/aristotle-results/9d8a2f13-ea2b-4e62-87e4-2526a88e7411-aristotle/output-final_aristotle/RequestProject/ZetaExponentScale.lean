/-
# The exponents on the zeta graph, and the triple-logarithmic scale of the Monster

The order of the Monster is far too large to put on any ordinary axis:

```
|M| = 2^46 · 3^20 · 5^9 · 7^6 · 11^2 · 13^3 · 17 · 19 · 23 · 29 · 31 · 41 · 47 · 59 · 71
    = 808017424794512875886459904961710757005754368000000000 ≈ 8.08 · 10^53 .
```

Taking the logarithm three times compresses it to a number of size `1.57`.  This file
develops that scale and proves where the objects of the diagram sit on it.

* `Sporadic.lll x = log (log (log x))`, strictly increasing above `e^e` — so the scale is
  *faithful*: it reorders nothing (`Sporadic.lll_lt_lll`, `Sporadic.lll_le_lll`).
* The first logarithm is exactly the exponent data: `log |M| = ∑_p e_p log p`, with the
  exponents `46, 20, 9, 6, 2, 3, 1, …, 1` as the coefficients
  (`Sporadic.log_monsterOrder_eq_sum`, `Sporadic.log_monsterOrder_eq_explicit`).
* The Monster sits at `1.57 < log log log |M| < 1.58` (`Sporadic.monster_lll_bounds`), its
  largest prime power `2^46` at `1.24 < log log log 2^46 < 1.25`
  (`Sporadic.twoPow46_lll_bounds`), and the smallest sporadic group `M11` (order `7920`) at
  `0.72 < log log log 7920 < 0.79` (`Sporadic.m11_lll_bounds`).
* Consequently all twenty-six sporadic groups fit in the window `[0.72, 1.58]` of the triple
  logarithm (`Sporadic.lll_sporadic_bounds`), which is what makes the picture
  `visualization/zeta-exponent-scale.svg` possible.

The numeric bounds are obtained from `Real.exp_one_lt_d9` / `Real.exp_one_gt_d9` through the
two comparison lemmas `Sporadic.lt_log_of_pow_lt` and `Sporadic.log_lt_of_lt_pow`, which turn a
statement `a/b < log x` into an inequality between rational numbers.
-/
import Mathlib
import RequestProject.MonsterZeta

open Finset

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Sporadic

/-! ## Rational bounds for logarithms -/

/-- If `e^a < x^b` (with `e` replaced by a rational upper bound for it), then `a/b < log x`. -/
theorem lt_log_of_pow_lt {x : ℝ} (hx : 0 < x) {a b : ℕ} (hb : 0 < b)
    (h : (2.7182818286 : ℝ) ^ a < x ^ b) : (a : ℝ) / b < Real.log x := by
  have h1 : Real.exp (a : ℝ) ≤ (2.7182818286 : ℝ) ^ a := by
    rw [show ((a : ℝ)) = (a : ℝ) * 1 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le a
  have h2 : x ^ b = Real.exp ((b : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx]
  have h3 : Real.exp (a : ℝ) < Real.exp ((b : ℝ) * Real.log x) := by rw [← h2]; linarith
  have h4 := Real.exp_lt_exp.mp h3
  rw [div_lt_iff₀ (by exact_mod_cast hb)]
  linarith

/-- If `x^b < e^a` (with `e` replaced by a rational lower bound for it), then `log x < a/b`. -/
theorem log_lt_of_lt_pow {x : ℝ} (hx : 0 < x) {a b : ℕ} (hb : 0 < b)
    (h : x ^ b < (2.7182818283 : ℝ) ^ a) : Real.log x < (a : ℝ) / b := by
  have h1 : (2.7182818283 : ℝ) ^ a ≤ Real.exp (a : ℝ) := by
    rw [show ((a : ℝ)) = (a : ℝ) * 1 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le a
  have h2 : x ^ b = Real.exp ((b : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx]
  have h3 : Real.exp ((b : ℝ) * Real.log x) < Real.exp (a : ℝ) := by rw [← h2]; linarith
  have h4 := Real.exp_lt_exp.mp h3
  rw [lt_div_iff₀ (by exact_mod_cast hb)]
  linarith

/-! ## The triple logarithm -/

/-- The triple logarithm `log (log (log x))`: the scale on which the Monster is visible. -/
noncomputable def lll (x : ℝ) : ℝ := Real.log (Real.log (Real.log x))

/-- **The scale is faithful.** Above `e` the triple logarithm is strictly increasing, so
plotting `log log log` reorders nothing. -/
theorem lll_lt_lll {x y : ℝ} (hx : Real.exp 1 < x) (hxy : x < y) : lll x < lll y := by
  have hx0 : 0 < x := lt_trans (Real.exp_pos 1) hx
  have hy0 : 0 < y := lt_trans hx0 hxy
  have h1 : 1 < Real.log x := by
    have := Real.log_lt_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at this
  have h2 : Real.log x < Real.log y := Real.log_lt_log hx0 hxy
  have h3 : Real.log (Real.log x) < Real.log (Real.log y) :=
    Real.log_lt_log (by linarith) h2
  have h4 : 0 < Real.log (Real.log x) := Real.log_pos h1
  exact Real.log_lt_log h4 h3

theorem lll_le_lll {x y : ℝ} (hx : Real.exp 1 < x) (hxy : x ≤ y) : lll x ≤ lll y := by
  rcases eq_or_lt_of_le hxy with rfl | h
  · exact le_rfl
  · exact (lll_lt_lll hx h).le

theorem exp_one_lt_three : Real.exp 1 < 3 := by
  have := Real.exp_one_lt_d9
  linarith

/-! ## Level one: the exponents -/

/-- The logarithm of a positive integer is the exponent-weighted sum of the logarithms of its
prime factors. -/
theorem log_natCast_eq_sum {n : ℕ} (hn : n ≠ 0) :
    Real.log (n : ℝ) = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  push_cast
  rw [Real.log_prod]
  · exact Finset.sum_congr rfl fun p _ => by
      rw [Real.log_pow]
  · intro p hp
    have hp1 : 1 < p := (Nat.prime_of_mem_primeFactors hp).one_lt
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp1
    positivity

/-- **The first logarithm is the exponent data.** `log |M|` is the sum of the fifteen
exponents of `|M|`, each weighting the logarithm of its prime. -/
theorem log_monsterOrder_eq_sum :
    Real.log (monsterOrder : ℝ)
      = ∑ p ∈ monsterPrimes, (monsterOrder.factorization p : ℝ) * Real.log p := by
  rw [log_natCast_eq_sum monsterOrder_ne_zero, primeFactors_monsterOrder]

/-- The same, with the exponents `46, 20, 9, 6, 2, 3, 1, …, 1` spelled out. -/
theorem log_monsterOrder_eq_explicit :
    Real.log (monsterOrder : ℝ)
      = 46 * Real.log 2 + 20 * Real.log 3 + 9 * Real.log 5 + 6 * Real.log 7 +
        2 * Real.log 11 + 3 * Real.log 13 + Real.log 17 + Real.log 19 + Real.log 23 +
        Real.log 29 + Real.log 31 + Real.log 41 + Real.log 47 + Real.log 59 +
        Real.log 71 := by
  have h : ∀ p ∈ monsterPrimes,
      ((monsterOrder.factorization p : ℕ) : ℝ) * Real.log p
        = ((monster.exponent p : ℕ) : ℝ) * Real.log p := by
    intro p _
    rw [monsterOrder, exponent_eq_factorization monster_mem p]
  rw [log_monsterOrder_eq_sum, Finset.sum_congr rfl h, monsterPrimes]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  norm_num [monster, Group.exponent]
  ring

/-! ## Level three: where the Monster sits -/

theorem monsterOrder_pos_real : (0 : ℝ) < (monsterOrder : ℝ) := by
  rw [monster_order_value]
  norm_num

/-- `log |M| > 124`. -/
theorem log_monsterOrder_gt : (124 : ℝ) < Real.log (monsterOrder : ℝ) := by
  have h : ((124 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) < Real.log (monsterOrder : ℝ) := by
    refine lt_log_of_pow_lt monsterOrder_pos_real Nat.one_pos ?_
    rw [monster_order_value]
    norm_num
  simpa using h

/-- `log |M| < 125`. -/
theorem log_monsterOrder_lt : Real.log (monsterOrder : ℝ) < 125 := by
  have h : Real.log (monsterOrder : ℝ) < ((125 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by
    refine log_lt_of_lt_pow monsterOrder_pos_real Nat.one_pos ?_
    rw [monster_order_value]
    norm_num
  simpa using h

theorem log_124_gt : (4.82 : ℝ) < Real.log 124 := by
  have h : ((241 : ℕ) : ℝ) / ((50 : ℕ) : ℝ) < Real.log 124 := by
    refine lt_log_of_pow_lt (by norm_num) (by norm_num) ?_
    norm_num
  norm_num at h
  linarith

theorem log_125_lt : Real.log 125 < 4.84 := by
  have h : Real.log 125 < ((242 : ℕ) : ℝ) / ((50 : ℕ) : ℝ) := by
    refine log_lt_of_lt_pow (by norm_num) (by norm_num) ?_
    norm_num
  norm_num at h
  linarith

theorem log_482_gt : (1.57 : ℝ) < Real.log 4.82 := by
  have h : ((157 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) < Real.log 4.82 := by
    refine lt_log_of_pow_lt (by norm_num) (by norm_num) ?_
    norm_num
  norm_num at h
  linarith

theorem log_484_lt : Real.log 4.84 < 1.58 := by
  have h : Real.log 4.84 < ((158 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) := by
    refine log_lt_of_lt_pow (by norm_num) (by norm_num) ?_
    norm_num
  norm_num at h
  linarith

/-- The second logarithm of the Monster's order: `4.82 < log log |M| < 4.84`. -/
theorem loglog_monsterOrder_bounds :
    (4.82 : ℝ) < Real.log (Real.log (monsterOrder : ℝ)) ∧
      Real.log (Real.log (monsterOrder : ℝ)) < 4.84 := by
  constructor
  · have h := Real.log_lt_log (by norm_num : (0:ℝ) < 124) log_monsterOrder_gt
    linarith [log_124_gt]
  · have h := Real.log_lt_log (by linarith [log_monsterOrder_gt] :
      (0:ℝ) < Real.log (monsterOrder : ℝ)) log_monsterOrder_lt
    linarith [log_125_lt]

/-- **The Monster on the triple-logarithmic scale**: `1.57 < log log log |M| < 1.58`. -/
theorem monster_lll_bounds :
    (1.57 : ℝ) < lll (monsterOrder : ℝ) ∧ lll (monsterOrder : ℝ) < 1.58 := by
  obtain ⟨h1, h2⟩ := loglog_monsterOrder_bounds
  constructor
  · have h := Real.log_lt_log (by norm_num : (0:ℝ) < 4.82) h1
    have := log_482_gt
    rw [lll]
    linarith
  · have h := Real.log_lt_log (by linarith : (0:ℝ) < Real.log (Real.log (monsterOrder : ℝ))) h2
    have := log_484_lt
    rw [lll]
    linarith

/-! ## Where the largest prime power `2^46` sits -/

theorem twoPow46_eq : ((2 : ℝ) ^ 46) = 70368744177664 := by norm_num

theorem log_twoPow46_gt : (31.88 : ℝ) < Real.log (70368744177664 : ℝ) := by
  rw [← twoPow46_eq, Real.log_pow]
  have := Real.log_two_gt_d9
  push_cast
  linarith

theorem log_twoPow46_lt : Real.log (70368744177664 : ℝ) < 31.89 := by
  rw [← twoPow46_eq, Real.log_pow]
  have := Real.log_two_lt_d9
  push_cast
  linarith

theorem log_3188_gt : (3.46 : ℝ) < Real.log 31.88 := by
  have h : ((173 : ℕ) : ℝ) / ((50 : ℕ) : ℝ) < Real.log 31.88 := by
    refine lt_log_of_pow_lt (by norm_num) (by norm_num) ?_
    norm_num
  norm_num at h
  linarith

theorem log_3189_lt : Real.log 31.89 < 3.48 := by
  have h : Real.log 31.89 < ((174 : ℕ) : ℝ) / ((50 : ℕ) : ℝ) := by
    refine log_lt_of_lt_pow (by norm_num) (by norm_num) ?_
    norm_num
  norm_num at h
  linarith

theorem log_346_gt : (1.24 : ℝ) < Real.log 3.46 := by
  have h : ((124 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) < Real.log 3.46 := by
    refine lt_log_of_pow_lt (by norm_num) (by norm_num) ?_
    norm_num
  norm_num at h
  linarith

theorem log_348_lt : Real.log 3.48 < 1.25 := by
  have h : Real.log 3.48 < ((125 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) := by
    refine log_lt_of_lt_pow (by norm_num) (by norm_num) ?_
    norm_num
  norm_num at h
  linarith

/-- **The forty-six exponents of `2` on the same scale**: the largest prime power dividing
`|M|`, namely `2^46 = 70368744177664 ≈ 7.04 · 10^13`, sits at
`1.24 < log log log 2^46 < 1.25`. -/
theorem twoPow46_lll_bounds :
    (1.24 : ℝ) < lll ((2 : ℝ) ^ 46) ∧ lll ((2 : ℝ) ^ 46) < 1.25 := by
  rw [twoPow46_eq]
  have hpos : (0 : ℝ) < Real.log (70368744177664 : ℝ) := by linarith [log_twoPow46_gt]
  have h1 : (3.46 : ℝ) < Real.log (Real.log (70368744177664 : ℝ)) := by
    have := Real.log_lt_log (by norm_num : (0:ℝ) < 31.88) log_twoPow46_gt
    linarith [log_3188_gt]
  have h2 : Real.log (Real.log (70368744177664 : ℝ)) < 3.48 := by
    have := Real.log_lt_log hpos log_twoPow46_lt
    linarith [log_3189_lt]
  refine ⟨?_, ?_⟩
  · have := Real.log_lt_log (by norm_num : (0:ℝ) < 3.46) h1
    rw [lll]
    linarith [log_346_gt]
  · have := Real.log_lt_log (by linarith : (0:ℝ) < Real.log (Real.log (70368744177664 : ℝ))) h2
    rw [lll]
    linarith [log_348_lt]

/-! ## The smallest sporadic group -/

/-- The Mathieu group `M11`, the smallest sporadic group. -/
def m11 : Group := ⟨"M11", [(2,4),(3,2),(5,1),(11,1)]⟩

theorem m11_mem : m11 ∈ groups := by decide

/-- The smallest sporadic group is `M11`, of order `7920`. -/
theorem m11_order : m11.order = 7920 := by norm_num [m11, Group.order, factProd]

theorem log_7920_gt : (8 : ℝ) < Real.log 7920 := by
  have h : ((8 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) < Real.log 7920 := by
    refine lt_log_of_pow_lt (by norm_num) Nat.one_pos ?_
    norm_num
  simpa using h

theorem log_7920_lt : Real.log 7920 < 9 := by
  have h : Real.log 7920 < ((9 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by
    refine log_lt_of_lt_pow (by norm_num) Nat.one_pos ?_
    norm_num
  simpa using h

theorem log_8_gt : (2.07 : ℝ) < Real.log 8 := by
  have h : ((207 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) < Real.log 8 := by
    refine lt_log_of_pow_lt (by norm_num) (by norm_num) ?_
    norm_num
  norm_num at h
  linarith

theorem log_9_lt : Real.log 9 < 2.2 := by
  have h : Real.log 9 < ((22 : ℕ) : ℝ) / ((10 : ℕ) : ℝ) := by
    refine log_lt_of_lt_pow (by norm_num) (by norm_num) ?_
    norm_num
  norm_num at h
  linarith

theorem log_207_gt : (0.72 : ℝ) < Real.log 2.07 := by
  have h : ((72 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) < Real.log 2.07 := by
    refine lt_log_of_pow_lt (by norm_num) (by norm_num) ?_
    norm_num
  norm_num at h
  linarith

theorem log_22_lt : Real.log 2.2 < 0.79 := by
  have h : Real.log 2.2 < ((79 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) := by
    refine log_lt_of_lt_pow (by norm_num) (by norm_num) ?_
    norm_num
  norm_num at h
  linarith

/-- **The smallest sporadic group on the triple-logarithmic scale**: `M11`, of order `7920`,
sits at `0.72 < log log log 7920 < 0.79`. -/
theorem m11_lll_bounds : (0.72 : ℝ) < lll 7920 ∧ lll 7920 < 0.79 := by
  have hpos : (0 : ℝ) < Real.log 7920 := by linarith [log_7920_gt]
  have h1 : (2.07 : ℝ) < Real.log (Real.log 7920) := by
    have := Real.log_lt_log (by norm_num : (0:ℝ) < 8) log_7920_gt
    linarith [log_8_gt]
  have h2 : Real.log (Real.log 7920) < 2.2 := by
    have := Real.log_lt_log hpos log_7920_lt
    linarith [log_9_lt]
  constructor
  · have := Real.log_lt_log (by norm_num : (0:ℝ) < 2.07) h1
    rw [lll]
    linarith [log_207_gt]
  · have := Real.log_lt_log (by linarith : (0:ℝ) < Real.log (Real.log 7920)) h2
    rw [lll]
    linarith [log_22_lt]

/-! ## The whole window -/

/-- Every sporadic group order lies between `|M11| = 7920` and `|M|`. -/
theorem order_mem_Icc : ∀ G ∈ groups, 7920 ≤ G.order ∧ G.order ≤ monsterOrder := by decide

/-- **The window of the picture.** On the triple-logarithmic scale all twenty-six sporadic
groups — spanning fourteen orders of magnitude from `7920` to `8·10^53` — fit between `0.72`
and `1.58`. -/
theorem lll_sporadic_bounds :
    ∀ G ∈ groups, (0.72 : ℝ) < lll (G.order : ℝ) ∧ lll (G.order : ℝ) < 1.58 := by
  intro G hG
  obtain ⟨h1, h2⟩ := order_mem_Icc G hG
  have e3 : Real.exp 1 < (7920 : ℝ) := by linarith [exp_one_lt_three]
  have hle1 : lll (7920 : ℝ) ≤ lll (G.order : ℝ) :=
    lll_le_lll e3 (by exact_mod_cast h1)
  have hle2 : lll (G.order : ℝ) ≤ lll (monsterOrder : ℝ) := by
    refine lll_le_lll ?_ (by exact_mod_cast h2)
    have : (7920 : ℝ) ≤ (G.order : ℝ) := by exact_mod_cast h1
    linarith [exp_one_lt_three]
  exact ⟨lt_of_lt_of_le m11_lll_bounds.1 hle1,
    lt_of_le_of_lt hle2 monster_lll_bounds.2⟩

end Sporadic
