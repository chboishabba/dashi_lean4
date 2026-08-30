/-
# All twenty-six sporadic groups against `ζ`

`RequestProject/MonsterZeta.lean` compared the Monster's factors with the Euler factors of
`ζ`, and `RequestProject/Lessons.lean` showed that nothing there is special to the Monster.
This file carries the comparison out for the *whole* table: each of the twenty-six sporadic
orders gets its own truncated Euler product, its value at `s = 2` is computed exactly as a
rational number, and the twenty-six values are ranked against each other and against
`ζ(2) = π²/6`.
-/
import Mathlib
import RequestProject.Lessons

open Finset

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SporadicZeta

open Sporadic Lessons

/-! ## The divisor sum of a factored order -/

/-- In a well-formed factorization each listed prime carries exactly its listed exponent. -/
theorem filter_sum_of_mem {l : List (ℕ × ℕ)} (h : l.Pairwise fun a b => a.1 ≠ b.1) :
    ∀ pe ∈ l, ((l.filter fun q => q.1 = pe.1).map Prod.snd).sum = pe.2 := by
  induction l with
  | nil => intro pe hpe; cases hpe
  | cons a t ih =>
      obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
      intro pe hpe
      rcases List.mem_cons.mp hpe with rfl | hpe
      · have hnil : (t.filter fun q => q.1 = pe.1) = [] := by
          rw [List.filter_eq_nil_iff]
          intro b hb hbq
          exact ha b hb (of_decide_eq_true hbq).symm
        simp [List.filter_cons_of_pos, hnil]
      · have hne : ¬ ((a.1 = pe.1 : Bool) = true) := by simpa using ha pe hpe
        rw [List.filter_cons, if_neg hne]
        exact ih ht pe hpe

/-- **Every sporadic order is a product of truncated zeta factors, one per listed prime.**
For a well-formed list of `(prime, exponent)` pairs the divisor sum of the product is the
product of the truncated Euler factors. -/
theorem divisorSum_factProd (s : ℝ) (l : List (ℕ × ℕ)) (h : WF l) :
    divisorSum (factProd l) s = (l.map fun pe => truncFactor pe.1 pe.2 s).prod := by
  rw [divisorSum_eq_prod s (factProd_ne_zero l h), primeFactors_factProd l h]
  have hnd : (l.map Prod.fst).Nodup := List.pairwise_map.mpr h.2
  rw [List.prod_toFinset _ hnd, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun pe hpe => ?_)
  have hexp : (factProd l).factorization pe.1 = pe.2 := by
    rw [factorization_factProd l h pe.1]
    exact filter_sum_of_mem h.2 pe hpe
  simp only [Function.comp_apply, hexp]

/-- The divisor sum of the order of a sporadic group, read off from its factor list. -/
theorem divisorSum_order (s : ℝ) {G : Group} (hG : G ∈ groups) :
    divisorSum G.order s = (G.factors.map fun pe => truncFactor pe.1 pe.2 s).prod :=
  divisorSum_factProd s G.factors (wf_groups G hG)

/-! ## The value at `s = 2`, exactly -/

/-- The truncated Euler factor at `s = 2`, as a rational number:
`1 + p⁻² + ⋯ + p^{-2e}`. -/
def truncQ (p e : ℕ) : ℚ := ∑ j ∈ Finset.range (e + 1), (((p : ℚ) ^ 2)⁻¹) ^ j

/-- The zeta mass of a sporadic group: `∑_{d ∣ |G|} d⁻²`, as an exact rational number. -/
def zetaMassQ (G : Group) : ℚ := (G.factors.map fun pe => truncQ pe.1 pe.2).prod

theorem rpow_neg_two {x : ℝ} (hx : 0 ≤ x) : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
  rw [Real.rpow_neg hx, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem truncFactor_two (p e : ℕ) : truncFactor p e 2 = (truncQ p e : ℝ) := by
  rw [truncFactor, truncQ]
  push_cast
  exact Finset.sum_congr rfl fun j _ => by rw [rpow_neg_two (by positivity)]

/-- **The exact value.** For every sporadic group, `∑_{d ∣ |G|} d⁻²` is the rational number
`zetaMassQ G`. -/
theorem divisorSum_order_two {G : Group} (hG : G ∈ groups) :
    divisorSum G.order 2 = (zetaMassQ G : ℝ) := by
  rw [divisorSum_order 2 hG, zetaMassQ, Rat.cast_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun pe _ => truncFactor_two pe.1 pe.2)

/-! ## Divisibility: why the Monster dominates, for every `s` -/

/-- **Dividing orders means smaller zeta mass.** If `m ∣ n` then every divisor of `m` is a
divisor of `n`, so the Dirichlet mass of `m` is at most that of `n`, for every `s ≥ 0`. -/
theorem divisorSum_le_of_dvd {m n : ℕ} (hn : n ≠ 0) (hmn : m ∣ n) (s : ℝ) :
    divisorSum m s ≤ divisorSum n s := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hn hmn) ?_
  intro d _ _
  positivity

/-- Lyons' group. -/
def lyons : Group := ⟨"Ly", [(2,8),(3,7),(5,6),(7,1),(11,1),(31,1),(37,1),(67,1)]⟩

/-- The fourth Janko group. -/
def janko4 : Group := ⟨"J4", [(2,21),(3,3),(5,1),(7,1),(11,3),(23,1),(29,1),(31,1),(37,1),(43,1)]⟩

/-- The first Mathieu group, the smallest sporadic group. -/
def mathieu11 : Group := ⟨"M11", [(2,4),(3,2),(5,1),(11,1)]⟩

theorem lyons_mem : lyons ∈ groups := by decide

theorem janko4_mem : janko4 ∈ groups := by decide

theorem mathieu11_mem : mathieu11 ∈ groups := by decide

/-- **Twenty-four of the twenty-six orders divide `|M|`.** Every sporadic group other than
Lyons' group and `J4` has order dividing the order of the Monster. -/
theorem order_dvd_monsterOrder : ∀ G ∈ groups, G ≠ lyons → G ≠ janko4 →
    G.order ∣ monsterOrder := by decide

/-- The two exceptions: `|Ly|` does not divide `|M|` (it has the primes `37` and `67`). -/
theorem lyons_order_not_dvd : ¬ (lyons.order ∣ monsterOrder) := by decide

/-- The second exception: `|J4|` does not divide `|M|` (it has `11³`, `37` and `43`). -/
theorem janko4_order_not_dvd : ¬ (janko4.order ∣ monsterOrder) := by decide

/-- **The structural half of the domination.** For the twenty-four sporadic groups whose
order divides `|M|`, the Monster's divisor sum dominates theirs at *every* `s ≥ 0` — no
computation needed, only divisibility. -/
theorem divisorSum_le_monster_of_ne {G : Group} (hG : G ∈ groups) (h1 : G ≠ lyons)
    (h2 : G ≠ janko4) (s : ℝ) : divisorSum G.order s ≤ divisorSum monsterOrder s :=
  divisorSum_le_of_dvd monsterOrder_ne_zero (order_dvd_monsterOrder G hG h1 h2) s

/-! ## The ranking at `s = 2` -/

/-- **The Monster maximises the zeta mass.** Among the twenty-six sporadic groups, no group
has a larger value of `∑_{d ∣ |G|} d⁻²` than the Monster — including the two, `Ly` and `J4`,
whose orders do not divide `|M|`. -/
theorem zetaMassQ_le_monster : ∀ G ∈ groups, zetaMassQ G ≤ zetaMassQ monster := by
  intro G hG
  fin_cases hG <;> norm_num [zetaMassQ, truncQ, monster, Finset.sum_range_succ]

/-- **`M11` minimises it.** The smallest sporadic group also carries the least zeta mass. -/
theorem mathieu11_le_zetaMassQ : ∀ G ∈ groups, zetaMassQ mathieu11 ≤ zetaMassQ G := by
  intro G hG
  fin_cases hG <;> norm_num [zetaMassQ, truncQ, mathieu11, Finset.sum_range_succ]

/-- **All twenty-six values sit in a band of width `0.07`.** Every sporadic zeta mass lies
strictly between `1.569` and `1.638`, well below `ζ(2) = 1.6449…`. -/
theorem zetaMassQ_mem_band : ∀ G ∈ groups,
    1569 / 1000 < zetaMassQ G ∧ zetaMassQ G < 1638 / 1000 := by
  intro G hG
  fin_cases hG <;>
    refine ⟨by norm_num [zetaMassQ, truncQ, Finset.sum_range_succ],
      by norm_num [zetaMassQ, truncQ, Finset.sum_range_succ]⟩

/-- The Monster's zeta mass to four decimals: `1.6372 < ∑_{d ∣ |M|} d⁻² < 1.6373`. -/
theorem zetaMassQ_monster_bounds :
    16372 / 10000 < zetaMassQ monster ∧ zetaMassQ monster < 16373 / 10000 := by
  constructor <;> norm_num [zetaMassQ, truncQ, monster, Finset.sum_range_succ]

/-! ## The two gaps to `ζ(2)`: truncation versus the missing primes -/

/-- The untruncated Euler factor of `ζ` at `s = 2`, as a rational number: `p²/(p²-1)`. -/
def eulerQ (p : ℕ) : ℚ := ((p : ℚ) ^ 2) / ((p : ℚ) ^ 2 - 1)

theorem eulerFactor_two {p : ℕ} (hp : 2 ≤ p) : eulerFactor p 2 = (eulerQ p : ℝ) := by
  have hp1 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hne : ((p : ℝ) ^ 2 - 1) ≠ 0 := by nlinarith
  rw [eulerFactor, rpow_neg_two (by positivity), eulerQ]
  push_cast
  rw [eq_div_iff hne]
  field_simp

/-- The fifteen supersingular primes, as a list. -/
def monsterPrimeList : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

theorem monsterPrimeList_toFinset : monsterPrimeList.toFinset = monsterPrimes := by decide

/-- The product of the fifteen *untruncated* Euler factors of `ζ` at the Monster's primes,
as an exact rational number. -/
def monsterEulerQ : ℚ := (monsterPrimeList.map eulerQ).prod

/-- The Monster's fifteen-factor Euler product at `s = 2` is the rational `monsterEulerQ`. -/
theorem monsterEulerProduct_two : monsterEulerProduct 2 = (monsterEulerQ : ℝ) := by
  rw [monsterEulerProduct, ← monsterPrimeList_toFinset,
    List.prod_toFinset _ (by decide : monsterPrimeList.Nodup), monsterEulerQ,
    Rat.cast_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  have hall : ∀ q ∈ monsterPrimeList, 2 ≤ q := by decide
  exact eulerFactor_two (hall p hp)

/-- **The truncation costs almost nothing.** Cutting the fifteen Euler factors off at the
Monster's own exponents loses less than `10⁻⁴`. -/
theorem truncation_gap :
    monsterEulerProduct 2 - divisorSum monsterOrder 2 < 1 / 10000 := by
  have hval : divisorSum monsterOrder 2 = (zetaMassQ monster : ℝ) := divisorSum_order_two monster_mem
  have hq : monsterEulerQ - zetaMassQ monster < 1 / 10000 := by
    norm_num [monsterEulerQ, monsterPrimeList, eulerQ, zetaMassQ, truncQ, monster,
      Finset.sum_range_succ]
  rw [monsterEulerProduct_two, hval]
  have : ((monsterEulerQ - zetaMassQ monster : ℚ) : ℝ) < ((1 / 10000 : ℚ) : ℝ) := by
    exact_mod_cast hq
  push_cast at this
  linarith

/-! ## Back to the reals: the whole table inside `ζ(2)` -/

/-- `ζ(2) = π²/6 > 1.6449`. -/
theorem zetaR_two_gt : (16449 : ℝ) / 10000 < zetaR 2 := by
  rw [zetaR_two]
  nlinarith [Real.pi_gt_d6, Real.pi_pos]

theorem one_point_638_lt_zetaR_two : (1638 : ℝ) / 1000 < zetaR 2 := by
  have := zetaR_two_gt
  linarith

/-- **Every sporadic group sits strictly inside `ζ(2)`, with room to spare.** For each of the
twenty-six groups, `∑_{d ∣ |G|} d⁻² < 1.638 < π²/6 = ζ(2)`. -/
theorem divisorSum_two_lt_zeta : ∀ G ∈ groups, divisorSum G.order 2 < zetaR 2 := by
  intro G hG
  have h := (zetaMassQ_mem_band G hG).2
  have hlt : divisorSum G.order 2 < (1638 : ℝ) / 1000 := by
    rw [divisorSum_order_two hG]
    have hc : ((zetaMassQ G : ℚ) : ℝ) < ((1638 / 1000 : ℚ) : ℝ) := by exact_mod_cast h
    simpa using hc
  exact hlt.trans one_point_638_lt_zetaR_two

/-- **The Monster is the closest of the twenty-six to `ζ(2)`, and still `0.007` away.** -/
theorem monster_gap :
    (16372 : ℝ) / 10000 < divisorSum monsterOrder 2 ∧
      divisorSum monsterOrder 2 < zetaR 2 - 7 / 1000 := by
  have hval : divisorSum monsterOrder 2 = (zetaMassQ monster : ℝ) := by
    have := divisorSum_order_two monster_mem
    rwa [show monster.order = monsterOrder from rfl] at this
  obtain ⟨hlo, hhi⟩ := zetaMassQ_monster_bounds
  refine ⟨?_, ?_⟩
  · rw [hval]
    have hc : ((16372 / 10000 : ℚ) : ℝ) < ((zetaMassQ monster : ℚ) : ℝ) := by exact_mod_cast hlo
    simpa using hc
  · have h1 : divisorSum monsterOrder 2 < (16373 : ℝ) / 10000 := by
      rw [hval]
      have hc : ((zetaMassQ monster : ℚ) : ℝ) < ((16373 / 10000 : ℚ) : ℝ) := by exact_mod_cast hhi
      simpa using hc
    have h2 := zetaR_two_gt
    linarith

/-- **The visible gap is the primes the Monster does not have.** Even with *no* truncation,
the fifteen supersingular Euler factors fall short of `ζ(2)` by more than `0.007` — more than
seventy times the loss from truncation. -/
theorem missing_primes_gap : 7 / 1000 < zetaR 2 - monsterEulerProduct 2 := by
  have hq : monsterEulerQ < 16373 / 10000 := by
    norm_num [monsterEulerQ, monsterPrimeList, eulerQ]
  have hr : monsterEulerProduct 2 < (16373 : ℝ) / 10000 := by
    rw [monsterEulerProduct_two]
    have hc : ((monsterEulerQ : ℚ) : ℝ) < ((16373 / 10000 : ℚ) : ℝ) := by exact_mod_cast hq
    simpa using hc
  have h2 := zetaR_two_gt
  linarith

/-- **The two gaps, side by side.** Between the Monster's divisor sum and `ζ(2)` there are two
losses: truncating the Euler factors at the Monster's exponents, worth less than `10⁻⁴`, and
the primes missing from `|M|`, worth more than `7·10⁻³`. The picture is decided by the second
one. -/
theorem two_gaps :
    monsterEulerProduct 2 - divisorSum monsterOrder 2 < 1 / 10000 ∧
      7 / 1000 < zetaR 2 - monsterEulerProduct 2 :=
  ⟨truncation_gap, missing_primes_gap⟩

/-- **The ranking, transported to the reals.** At `s = 2` the Monster's divisor sum is the
largest and `M11`'s the smallest of the twenty-six. -/
theorem divisorSum_two_ranking : ∀ G ∈ groups,
    divisorSum mathieu11.order 2 ≤ divisorSum G.order 2 ∧
      divisorSum G.order 2 ≤ divisorSum monsterOrder 2 := by
  intro G hG
  have hM : divisorSum monsterOrder 2 = (zetaMassQ monster : ℝ) := divisorSum_order_two monster_mem
  rw [divisorSum_order_two hG, divisorSum_order_two mathieu11_mem, hM]
  exact ⟨by exact_mod_cast mathieu11_le_zetaMassQ G hG, by exact_mod_cast zetaMassQ_le_monster G hG⟩

/-- **The expanded diagram, as one statement.** For every one of the twenty-six sporadic
groups: its Dirichlet mass at `s = 2` is the exact rational `zetaMassQ G`, it is at most the
Monster's, and it is strictly below `ζ(2)`; and the Monster's own shortfall splits into a
negligible truncation loss and the loss from the primes it does not contain. -/
theorem sporadic_table_against_zeta :
    (∀ G ∈ groups, divisorSum G.order 2 = (zetaMassQ G : ℝ) ∧
        divisorSum G.order 2 ≤ divisorSum monsterOrder 2 ∧
        divisorSum G.order 2 < zetaR 2) ∧
      monsterEulerProduct 2 - divisorSum monsterOrder 2 < 1 / 10000 ∧
      7 / 1000 < zetaR 2 - monsterEulerProduct 2 :=
  ⟨fun G hG => ⟨divisorSum_order_two hG, (divisorSum_two_ranking G hG).2,
    divisorSum_two_lt_zeta G hG⟩, two_gaps⟩

end SporadicZeta
