/-
# The zeta spectrum of the twenty-six sporadic groups

`RequestProject/SporadicZeta.lean` compared the twenty-six sporadic orders with `ζ` at the
single point `s = 2`. This file lets `s` move.

For every natural `s ≥ 1` the Dirichlet mass `∑_{d ∣ |G|} d^{-s}` of a sporadic order is again
an exact rational number (`massQ`), so the whole table becomes a *spectrum*: twenty-six curves
of `s`. The curves decrease, they all collapse to `1` as `s → ∞` (and each unit step of `s`
at least halves the distance to `1`), and every one of them stays strictly below `ζ(s)` for
`s > 1`. At the left end, `s = 1`, the mass is the abundancy index `σ(n)/n`: the Monster's is
`6.9801…`, so `|M|` is abundant many times over — while `ζ(1)` diverges, so there the twenty-six
finite values are passed by the harmonic series.

The ranking is *not* the same at every `s`: the Monster is the largest at `s = 1, 2, 3, 4`, but
the smallest group changes (`M11` at `s = 1, 2`, `J3` at `s = 3, 4`) and `J1`/`J3` swap between
`s = 1` and `s = 2`.
-/
import Mathlib
import RequestProject.SporadicZeta

open Finset

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SporadicSpectrum

open Sporadic Lessons SporadicZeta

/-! ## The mass at an integer `s`, exactly -/

/-- The Dirichlet mass `∑_{d ∣ |G|} d^{-s}` of a sporadic order at a natural number `s`, as an
exact rational number: the product of the truncated Euler factors `1 + p^{-s} + ⋯ + p^{-es}`. -/
def massQ (G : Group) (s : ℕ) : ℚ :=
  (G.factors.map fun pe => ∑ j ∈ Finset.range (pe.2 + 1), (((pe.1 : ℚ) ^ s)⁻¹) ^ j).prod

/-- At `s = 2` this is the zeta mass of `RequestProject/SporadicZeta.lean`. -/
theorem massQ_two (G : Group) : massQ G 2 = zetaMassQ G := rfl

theorem rpow_neg_natCast {x : ℝ} (hx : 0 ≤ x) (s : ℕ) : x ^ (-(s : ℝ)) = ((x ^ s)⁻¹) := by
  rw [Real.rpow_neg hx, Real.rpow_natCast]

theorem truncFactor_natCast (p e s : ℕ) :
    truncFactor p e (s : ℝ)
      = ((∑ j ∈ Finset.range (e + 1), (((p : ℚ) ^ s)⁻¹) ^ j : ℚ) : ℝ) := by
  rw [truncFactor]
  push_cast
  exact Finset.sum_congr rfl fun j _ => by rw [rpow_neg_natCast (by positivity) s]

/-- **The exact value at every integer `s`.** For each of the twenty-six groups and each
natural number `s`, `∑_{d ∣ |G|} d^{-s}` is the rational number `massQ G s`. -/
theorem divisorSum_order_nat {G : Group} (hG : G ∈ groups) (s : ℕ) :
    divisorSum G.order (s : ℝ) = (massQ G s : ℝ) := by
  rw [divisorSum_order (s : ℝ) hG, massQ, Rat.cast_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun pe _ => truncFactor_natCast pe.1 pe.2 s)

/-! ## The shape of every curve: decreasing, collapsing to `1` -/

/-- **The mass decreases in `s`.** For every `n` the divisor sum is antitone. -/
theorem divisorSum_antitone (n : ℕ) : Antitone (divisorSum n) := by
  intro s t hst
  refine Finset.sum_le_sum fun d hd => ?_
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
  exact Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)

theorem one_mem_divisors {n : ℕ} (hn : n ≠ 0) : 1 ∈ n.divisors :=
  Nat.one_mem_divisors.mpr hn

/-- The divisor sum, with the constant term `1` split off. -/
theorem divisorSum_eq_one_add {n : ℕ} (hn : n ≠ 0) (s : ℝ) :
    divisorSum n s = 1 + ∑ d ∈ n.divisors.erase 1, (d : ℝ) ^ (-s) := by
  rw [divisorSum, ← Finset.add_sum_erase _ _ (one_mem_divisors hn)]
  norm_num

/-- **Each unit step in `s` at least halves the distance to `1`.** -/
theorem divisorSum_succ_sub_one_le {n : ℕ} (hn : n ≠ 0) (s : ℝ) :
    divisorSum n (s + 1) - 1 ≤ (divisorSum n s - 1) / 2 := by
  rw [divisorSum_eq_one_add hn, divisorSum_eq_one_add hn]
  have key : ∀ d ∈ n.divisors.erase 1,
      (d : ℝ) ^ (-(s + 1)) ≤ (d : ℝ) ^ (-s) / 2 := by
    intro d hd
    have hd2 : 2 ≤ d := by
      have h1 : d ≠ 1 := Finset.ne_of_mem_erase hd
      have hpos : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_of_mem_erase hd)
      omega
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
    have hsplit : (d : ℝ) ^ (-(s + 1)) = (d : ℝ) ^ (-s) * ((d : ℝ))⁻¹ := by
      rw [show -(s + 1) = -s + (-1 : ℝ) by ring, Real.rpow_add hd0]
      congr 1
      rw [Real.rpow_neg_one]
    have hinv : ((d : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [one_div]
      exact inv_anti₀ (by norm_num) hdR
    have hpow : (0 : ℝ) ≤ (d : ℝ) ^ (-s) := Real.rpow_nonneg (le_of_lt hd0) _
    calc (d : ℝ) ^ (-(s + 1)) = (d : ℝ) ^ (-s) * ((d : ℝ))⁻¹ := hsplit
      _ ≤ (d : ℝ) ^ (-s) * (1 / 2) := by nlinarith
      _ = (d : ℝ) ^ (-s) / 2 := by ring
  have := Finset.sum_le_sum key
  rw [← Finset.sum_div] at this
  simpa using this

/-- **All the curves collapse to `1`.** For every `n ≠ 0` the divisor sum tends to `1` as
`s → ∞`. -/
theorem divisorSum_tendsto_one {n : ℕ} (hn : n ≠ 0) :
    Filter.Tendsto (divisorSum n) Filter.atTop (nhds 1) := by
  have hterm : ∀ d ∈ n.divisors,
      Filter.Tendsto (fun s : ℝ => (d : ℝ) ^ (-s)) Filter.atTop
        (nhds (if d = 1 then (1 : ℝ) else 0)) := by
    intro d hd
    by_cases h1 : d = 1
    · subst h1
      simp only [Nat.cast_one, Real.one_rpow]
      exact tendsto_const_nhds
    · have hd2 : 2 ≤ d := by
        have hpos : 0 < d := Nat.pos_of_mem_divisors hd
        omega
      have hdR : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd2.trans_lt' one_lt_two
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := by linarith
      rw [if_neg h1]
      have : Filter.Tendsto (fun s : ℝ => ((d : ℝ)⁻¹) ^ s) Filter.atTop (nhds 0) := by
        apply tendsto_rpow_atTop_of_base_lt_one
        · have : (0 : ℝ) < (d : ℝ)⁻¹ := by positivity
          linarith
        · rw [inv_lt_one_iff₀]
          right; exact hdR
      refine this.congr fun s => ?_
      rw [Real.inv_rpow hd0, Real.rpow_neg hd0]
  have hsum := tendsto_finset_sum n.divisors hterm
  have hval : ∑ d ∈ n.divisors, (if d = 1 then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_ite_eq' n.divisors 1 (fun _ => (1 : ℝ))]
    simp [one_mem_divisors hn]
  rwa [hval] at hsum

/-! ## Strictly inside `ζ`, for every `n` -/

/-- **Every finite order is *strictly* inside `ζ`.** For `s > 1` and every `n`, the divisor sum
misses at least the term `(n+1)^{-s}`. -/
theorem divisorSum_lt_zeta {s : ℝ} (hs : 1 < s) (n : ℕ) : divisorSum n s < zetaR s := by
  have hnot : (n + 1) ∉ n.divisors := by
    intro h
    obtain ⟨hdvd, hn0⟩ := Nat.mem_divisors.mp h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
    omega
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ (-s) := by
    apply Real.rpow_pos_of_pos
    exact_mod_cast Nat.succ_pos n
  have hle : ∑ d ∈ insert (n + 1) n.divisors, (d : ℝ) ^ (-s) ≤ zetaR s := sum_le_zetaR hs _
  rw [Finset.sum_insert hnot] at hle
  have : divisorSum n s < ((n + 1 : ℕ) : ℝ) ^ (-s) + divisorSum n s := by
    rw [divisorSum]; linarith
  exact this.trans_le hle

/-! ## The left end `s = 1`: the abundancy index -/

/-- **At `s = 1` the mass is the abundancy index.** For `n ≠ 0`,
`∑_{d ∣ n} d⁻¹ = σ(n)/n`. -/
theorem divisorSum_one {n : ℕ} (hn : n ≠ 0) :
    divisorSum n 1 = (∑ d ∈ n.divisors, (d : ℝ)) / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [divisorSum, eq_div_iff hn0.ne', Finset.sum_mul]
  rw [← Nat.sum_div_divisors n (fun d => (d : ℝ))]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hcast : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) := by
    rw [Nat.cast_div hdvd hd0.ne']
  rw [hcast, Real.rpow_neg_one, inv_mul_eq_div]

/-! ## The spectrum of the table -/

/-- The first Janko group. -/
def janko1 : Group := ⟨"J1", [(2,3),(3,1),(5,1),(7,1),(11,1),(19,1)]⟩

/-- The third Janko group. -/
def janko3 : Group := ⟨"J3", [(2,7),(3,5),(5,1),(17,1),(19,1)]⟩

theorem janko1_mem : janko1 ∈ groups := by decide

theorem janko3_mem : janko3 ∈ groups := by decide

/-- **The Monster is the largest at `s = 1`** — its abundancy index is the biggest of the
twenty-six. -/
theorem massQ_one_le_monster : ∀ G ∈ groups, massQ G 1 ≤ massQ monster 1 := by
  intro G hG
  fin_cases hG <;> norm_num [massQ, monster, Finset.sum_range_succ]

/-- **The Monster is the largest at `s = 3`.** -/
theorem massQ_three_le_monster : ∀ G ∈ groups, massQ G 3 ≤ massQ monster 3 := by
  intro G hG
  fin_cases hG <;> norm_num [massQ, monster, Finset.sum_range_succ]

/-- **The Monster is the largest at `s = 4`.** -/
theorem massQ_four_le_monster : ∀ G ∈ groups, massQ G 4 ≤ massQ monster 4 := by
  intro G hG
  fin_cases hG <;> norm_num [massQ, monster, Finset.sum_range_succ]

/-- **The Monster is the largest at `s = 5`.** -/
theorem massQ_five_le_monster : ∀ G ∈ groups, massQ G 5 ≤ massQ monster 5 := by
  intro G hG
  fin_cases hG <;> norm_num [massQ, monster, Finset.sum_range_succ]

/-- The band at `s = 1`: every sporadic abundancy index lies between `3.66` and `6.981`. -/
theorem massQ_one_band : ∀ G ∈ groups, 366 / 100 < massQ G 1 ∧ massQ G 1 < 6981 / 1000 := by
  intro G hG
  fin_cases hG <;>
    refine ⟨by norm_num [massQ, Finset.sum_range_succ],
      by norm_num [massQ, Finset.sum_range_succ]⟩

/-- The band at `s = 3`: the twenty-six values are squeezed into a window of width `0.006`. -/
theorem massQ_three_band : ∀ G ∈ groups,
    1196 / 1000 < massQ G 3 ∧ massQ G 3 < 1202 / 1000 := by
  intro G hG
  fin_cases hG <;>
    refine ⟨by norm_num [massQ, Finset.sum_range_succ],
      by norm_num [massQ, Finset.sum_range_succ]⟩

/-- The band at `s = 4`: width `0.0006`. -/
theorem massQ_four_band : ∀ G ∈ groups,
    10817 / 10000 < massQ G 4 ∧ massQ G 4 < 108233 / 100000 := by
  intro G hG
  fin_cases hG <;>
    refine ⟨by norm_num [massQ, Finset.sum_range_succ],
      by norm_num [massQ, Finset.sum_range_succ]⟩

/-- The Monster's abundancy index to four decimals: `6.9801 < σ(|M|)/|M| < 6.9803`. -/
theorem massQ_monster_one_bounds :
    69801 / 10000 < massQ monster 1 ∧ massQ monster 1 < 69803 / 10000 := by
  constructor <;> norm_num [massQ, monster, Finset.sum_range_succ]

/-- **`|M|` is abundant, six times over.** `σ(|M|) > 6 |M|`. -/
theorem monster_abundant : 6 * (monsterOrder : ℝ) < ∑ d ∈ monsterOrder.divisors, (d : ℝ) := by
  have hn0 : (0 : ℝ) < (monsterOrder : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero monsterOrder_ne_zero
  have hval : divisorSum monsterOrder 1 = (massQ monster 1 : ℝ) := by
    have := divisorSum_order_nat monster_mem 1
    simpa using this
  have hlo : (69801 : ℝ) / 10000 < (massQ monster 1 : ℝ) := by
    have h := massQ_monster_one_bounds.1
    have hc : ((69801 / 10000 : ℚ) : ℝ) < ((massQ monster 1 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    linarith
  have hdiv := divisorSum_one monsterOrder_ne_zero
  rw [hval] at hdiv
  rw [eq_div_iff hn0.ne'] at hdiv
  nlinarith

/-! ## The ranking depends on `s` -/

/-- **The order of the table changes with `s`.** `J1` carries less mass than `J3` at `s = 1`,
and more at `s = 2`: the ranking of the twenty-six is not a single universal list. -/
theorem ranking_swaps_one_two :
    massQ janko1 1 < massQ janko3 1 ∧ massQ janko3 2 < massQ janko1 2 := by
  constructor <;> norm_num [massQ, janko1, janko3, Finset.sum_range_succ]

/-- **The bottom of the table moves too.** `M11` is the smallest at `s = 2`, but at `s = 3`
`J3` has slipped below it. -/
theorem minimum_swaps_two_three :
    massQ mathieu11 2 < massQ janko3 2 ∧ massQ janko3 3 < massQ mathieu11 3 := by
  constructor <;> norm_num [massQ, mathieu11, janko3, Finset.sum_range_succ]

/-- `M11` is the smallest at `s = 1`. -/
theorem massQ_one_mathieu11_min : ∀ G ∈ groups, massQ mathieu11 1 ≤ massQ G 1 := by
  intro G hG
  fin_cases hG <;> norm_num [massQ, mathieu11, Finset.sum_range_succ]

/-- `J3` is the smallest at `s = 3`. -/
theorem massQ_three_janko3_min : ∀ G ∈ groups, massQ janko3 3 ≤ massQ G 3 := by
  intro G hG
  fin_cases hG <;> norm_num [massQ, janko3, Finset.sum_range_succ]

/-- **The rational masses decrease in `s` too.** -/
theorem massQ_antitone {G : Group} (hG : G ∈ groups) {s t : ℕ} (hst : s ≤ t) :
    massQ G t ≤ massQ G s := by
  have h : ((massQ G t : ℚ) : ℝ) ≤ ((massQ G s : ℚ) : ℝ) := by
    rw [← divisorSum_order_nat hG, ← divisorSum_order_nat hG]
    exact divisorSum_antitone _ (by exact_mod_cast hst)
  exact_mod_cast h

/-- The band at `s = 5`: the twenty-six values agree to four decimals. -/
theorem massQ_five_band : ∀ G ∈ groups,
    10368 / 10000 < massQ G 5 ∧ massQ G 5 < 1037 / 1000 := by
  intro G hG
  fin_cases hG <;>
    refine ⟨by norm_num [massQ, Finset.sum_range_succ],
      by norm_num [massQ, Finset.sum_range_succ]⟩

/-- **The window of the spectrum picture.** For every group and every `1 ≤ s ≤ 5` the excess
mass `∑_{d ∣ |G|} d^{-s} - 1` lies between `1/32` and `7`, so all twenty-six curves fit inside
the drawn logarithmic window. -/
theorem massQ_in_window : ∀ G ∈ groups, ∀ s : ℕ, 1 ≤ s → s ≤ 5 →
    1 / 32 < massQ G s - 1 ∧ massQ G s - 1 < 7 := by
  intro G hG s h1 h5
  have hlo : massQ G 5 ≤ massQ G s := massQ_antitone hG h5
  have hhi : massQ G s ≤ massQ G 1 := massQ_antitone hG h1
  have h5b := (massQ_five_band G hG).1
  have h1b := (massQ_one_band G hG).2
  constructor <;> [linarith; linarith]

/-! ## The left end against `ζ(1)` -/

/-- **At `s = 1` the harmonic series overtakes the Monster.** The twenty-six masses are finite
at `s = 1`, but `ζ` is not: some partial sum of `∑ 1/n` exceeds the Monster's abundancy index,
so the containment `∑_{d ∣ |M|} d^{-s} < ζ(s)` of `s > 1` degenerates at `s = 1`. -/
theorem harmonic_overtakes_monster :
    ∃ N : ℕ, divisorSum monsterOrder 1 < ∑ i ∈ Finset.range N, (1 : ℝ) / (i + 1) := by
  have h := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have := (Filter.tendsto_atTop.mp h) (divisorSum monsterOrder 1 + 1)
  obtain ⟨N, hN⟩ := this.exists
  exact ⟨N, by linarith [hN]⟩

/-! ## The spectrum, as one statement -/

/-- **The sporadic zeta spectrum.** For every one of the twenty-six sporadic groups and every
natural `s`: the Dirichlet mass is the exact rational `massQ G s`; the curve `s ↦ ∑_{d ∣ |G|}
d^{-s}` is decreasing, each unit step at least halving the distance to `1`, and it converges to
`1`; and for `s > 1` it stays strictly below `ζ(s)`. -/
theorem sporadic_spectrum : ∀ G ∈ groups,
    (∀ s : ℕ, divisorSum G.order (s : ℝ) = (massQ G s : ℝ)) ∧
      Antitone (divisorSum G.order) ∧
      (∀ s : ℝ, divisorSum G.order (s + 1) - 1 ≤ (divisorSum G.order s - 1) / 2) ∧
      Filter.Tendsto (divisorSum G.order) Filter.atTop (nhds 1) ∧
      (∀ s : ℝ, 1 < s → divisorSum G.order s < zetaR s) := by
  intro G hG
  exact ⟨fun s => divisorSum_order_nat hG s, divisorSum_antitone _,
    fun s => divisorSum_succ_sub_one_le (order_ne_zero hG) s,
    divisorSum_tendsto_one (order_ne_zero hG), fun s hs => divisorSum_lt_zeta hs _⟩

end SporadicSpectrum
