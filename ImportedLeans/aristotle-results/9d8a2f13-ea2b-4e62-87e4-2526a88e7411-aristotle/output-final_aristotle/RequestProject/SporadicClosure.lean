/-
# Closing the table: the sporadic lcm, the sporadic ceiling, and where the curves cross

`RequestProject/SporadicZeta.lean` compared the twenty-six sporadic orders with `ζ` at `s = 2`
and `RequestProject/SporadicSpectrum.lean` let `s` move. Both work group by group. This file
closes the table up.

* **The lcm.** `sporadicLcm` is the smallest number that all twenty-six sporadic orders divide:
  `|M| · 11 · 37 · 43 · 67`, the Monster's order corrected by `J4`'s `11³, 37, 43` and Lyons'
  `67`. Its Dirichlet mass dominates all twenty-six at every `s`, and is still strictly inside
  `ζ`.
* **The ceiling.** No number built from sporadic primes can do better than the eighteen
  *untruncated* Euler factors, `sporadicCeiling s`. This is a ceiling for the whole table at
  once, and it is strictly below `ζ(s)`: the prime `53` — the smallest prime that divides no
  sporadic order — already separates them. At `s = 2` the ceiling is `1.63973…`, so the
  sporadic world can never come nearer to `ζ(2) = 1.64493…` than `0.005`; the lcm already sits
  within `0.00005` of that ceiling.
* **The crossings.** The masses are continuous in `s`, so wherever the ranking of two groups
  swaps between two integers there is a real `s` in between at which the two curves actually
  meet: `J1` and `J3` cross between `s = 1` and `s = 2`, and `M11` and `J3` cross between
  `s = 2` and `s = 3`.
-/
import Mathlib
import RequestProject.SporadicSpectrum

open Finset

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SporadicClosure

open Sporadic Lessons SporadicZeta SporadicSpectrum

/-! ## The lcm of the twenty-six orders -/

/-- The factorization of the least common multiple of the twenty-six sporadic orders. -/
def lcmFactors : List (ℕ × ℕ) :=
  [(2,46),(3,20),(5,9),(7,6),(11,3),(13,3),(17,1),(19,1),(23,1),(29,1),(31,1),(37,1),(41,1),
   (43,1),(47,1),(59,1),(67,1),(71,1)]

/-- The least common multiple of the orders of the twenty-six sporadic simple groups. -/
def sporadicLcm : ℕ := factProd lcmFactors

theorem wf_lcmFactors : WF lcmFactors := by decide

theorem sporadicLcm_ne_zero : sporadicLcm ≠ 0 := factProd_ne_zero _ wf_lcmFactors

/-- The value of the sporadic lcm. -/
theorem sporadicLcm_value :
    sporadicLcm = 947454567739027579339558631381238297209966382022656000000000 := by
  norm_num [sporadicLcm, lcmFactors, factProd]

/-- **The lcm is the Monster's order corrected at four primes.** `J4` contributes `11³`, `37`
and `43`, and Lyons' group contributes `67`; everything else is already inside `|M|`. -/
theorem sporadicLcm_eq_monster_mul : sporadicLcm = monsterOrder * (11 * 37 * 43 * 67) := by
  rw [sporadicLcm_value, monster_order_value]

/-- **It really is the lcm of the table.** -/
theorem sporadicLcm_eq_foldr : sporadicLcm = (groups.map Group.order).foldr Nat.lcm 1 := by
  norm_num [sporadicLcm, lcmFactors, factProd, groups, Group.order]

/-- Every sporadic order divides the sporadic lcm. -/
theorem order_dvd_sporadicLcm : ∀ G ∈ groups, G.order ∣ sporadicLcm := by
  rw [sporadicLcm_value]
  decide

/-- A fold of `Nat.lcm` divides any common multiple of the entries. -/
theorem foldr_lcm_dvd (l : List ℕ) (m : ℕ) (h : ∀ a ∈ l, a ∣ m) : l.foldr Nat.lcm 1 ∣ m := by
  induction l with
  | nil => simp
  | cons a t ih =>
      exact Nat.lcm_dvd (h a (List.mem_cons_self ..))
        (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- **Minimality.** Any number that all twenty-six sporadic orders divide is a multiple of the
sporadic lcm. -/
theorem sporadicLcm_dvd_of_forall {m : ℕ} (h : ∀ G ∈ groups, G.order ∣ m) : sporadicLcm ∣ m := by
  rw [sporadicLcm_eq_foldr]
  refine foldr_lcm_dvd _ m ?_
  intro a ha
  obtain ⟨G, hG, rfl⟩ := List.mem_map.mp ha
  exact h G hG

/-- The primes of the lcm are exactly the eighteen sporadic primes. -/
theorem primeFactors_sporadicLcm : sporadicLcm.primeFactors = sporadicPrimes := by
  rw [sporadicLcm, primeFactors_factProd _ wf_lcmFactors, sporadicPrimes_eq]
  decide

/-! ## The mass of the lcm -/

/-- The Dirichlet mass `∑_{d ∣ N} d^{-s}` of the sporadic lcm at a natural number `s`, as an
exact rational number. -/
def lcmMassQ (s : ℕ) : ℚ :=
  (lcmFactors.map fun pe => ∑ j ∈ Finset.range (pe.2 + 1), (((pe.1 : ℚ) ^ s)⁻¹) ^ j).prod

/-- The exact value of the lcm's mass at every integer `s`. -/
theorem divisorSum_sporadicLcm (s : ℕ) :
    divisorSum sporadicLcm (s : ℝ) = (lcmMassQ s : ℝ) := by
  rw [sporadicLcm, divisorSum_factProd (s : ℝ) _ wf_lcmFactors, lcmMassQ, Rat.cast_list_prod,
    List.map_map]
  exact congrArg List.prod (List.map_congr_left fun pe _ => truncFactor_natCast pe.1 pe.2 s)

/-- **The lcm dominates the whole table, at every `s ≥ 0`.** -/
theorem divisorSum_le_sporadicLcm {G : Group} (hG : G ∈ groups) (s : ℝ) :
    divisorSum G.order s ≤ divisorSum sporadicLcm s :=
  divisorSum_le_of_dvd sporadicLcm_ne_zero (order_dvd_sporadicLcm G hG) s

/-- The same statement for the exact rational masses at integer `s`. -/
theorem massQ_le_lcmMassQ {G : Group} (hG : G ∈ groups) (s : ℕ) : massQ G s ≤ lcmMassQ s := by
  have h : ((massQ G s : ℚ) : ℝ) ≤ ((lcmMassQ s : ℚ) : ℝ) := by
    rw [← divisorSum_order_nat hG, ← divisorSum_sporadicLcm]
    exact divisorSum_le_sporadicLcm hG _
  exact_mod_cast h

/-- The lcm's mass at `s = 2`, to four decimals. -/
theorem lcmMassQ_two_band : 16396 / 10000 < lcmMassQ 2 ∧ lcmMassQ 2 < 16397 / 10000 := by
  constructor <;> norm_num [lcmMassQ, lcmFactors, Finset.sum_range_succ]

/-- **Even the lcm stays inside `ζ(2)`, with `0.005` to spare.** -/
theorem lcm_mass_two_lt_zeta : divisorSum sporadicLcm 2 < zetaR 2 - 5 / 1000 := by
  have hval : divisorSum sporadicLcm ((2 : ℕ) : ℝ) = (lcmMassQ 2 : ℝ) := divisorSum_sporadicLcm 2
  have hcast : divisorSum sporadicLcm 2 = (lcmMassQ 2 : ℝ) := by simpa using hval
  have hb : ((lcmMassQ 2 : ℚ) : ℝ) < ((16397 / 10000 : ℚ) : ℝ) := by
    exact_mod_cast lcmMassQ_two_band.2
  push_cast at hb
  have hz := zetaR_two_gt
  rw [hcast]
  linarith

/-! ## The ceiling: the eighteen untruncated Euler factors -/

/-- The product of the *untruncated* zeta Euler factors at the eighteen sporadic primes: the
largest Dirichlet mass any number built from sporadic primes can have. -/
noncomputable def sporadicCeiling (s : ℝ) : ℝ := ∏ p ∈ sporadicPrimes, eulerFactor p s

/-- Enlarging a finite product of factors `≥ 1` only increases it. -/
theorem prod_le_prod_of_subset_one_le {S T : Finset ℕ} (hST : S ⊆ T) (f : ℕ → ℝ)
    (hf : ∀ p ∈ T, 1 ≤ f p) : ∏ p ∈ S, f p ≤ ∏ p ∈ T, f p := by
  rw [← Finset.prod_sdiff hST]
  have h1 : (1 : ℝ) ≤ ∏ p ∈ T \ S, f p := by
    calc (1 : ℝ) = ∏ _p ∈ T \ S, (1 : ℝ) := by simp
      _ ≤ ∏ p ∈ T \ S, f p :=
          Finset.prod_le_prod (fun _ _ => zero_le_one)
            (fun p hp => hf p (Finset.mem_sdiff.mp hp).1)
  have h0 : 0 ≤ ∏ p ∈ S, f p :=
    Finset.prod_nonneg fun p hp => le_trans zero_le_one (hf p (hST hp))
  exact le_mul_of_one_le_left h0 h1

/-- **The ceiling caps every number built from sporadic primes.** -/
theorem divisorSum_le_sporadicCeiling {n : ℕ} (hn : n ≠ 0) (hsub : n.primeFactors ⊆ sporadicPrimes)
    {s : ℝ} (hs : 0 < s) : divisorSum n s ≤ sporadicCeiling s := by
  rw [divisorSum_eq_prod s hn]
  have step1 : ∏ p ∈ n.primeFactors, truncFactor p (n.factorization p) s
      ≤ ∏ p ∈ n.primeFactors, eulerFactor p s := by
    refine Finset.prod_le_prod (fun p hp => le_of_lt (truncFactor_pos ?_ hs _))
      (fun p hp => truncFactor_le_eulerFactor ?_ hs _) <;>
      exact (Nat.prime_of_mem_primeFactors hp).two_le
  refine step1.trans (prod_le_prod_of_subset_one_le hsub _ fun p hp => ?_)
  exact one_le_eulerFactor (prime_of_mem_sporadicPrimes p hp).two_le hs

/-- Each of the twenty-six groups sits under the ceiling. -/
theorem divisorSum_order_le_sporadicCeiling {G : Group} (hG : G ∈ groups) {s : ℝ} (hs : 0 < s) :
    divisorSum G.order s ≤ sporadicCeiling s := by
  refine divisorSum_le_sporadicCeiling (order_ne_zero hG) ?_ hs
  intro p hp
  exact (mem_sporadicPrimes_iff p).2 ⟨G, hG, hp⟩

/-- So does the lcm — the largest mass the sporadic primes can build with these exponents. -/
theorem divisorSum_sporadicLcm_le_sporadicCeiling {s : ℝ} (hs : 0 < s) :
    divisorSum sporadicLcm s ≤ sporadicCeiling s :=
  divisorSum_le_sporadicCeiling sporadicLcm_ne_zero (le_of_eq primeFactors_sporadicLcm) hs

/-- **The ceiling never reaches `ζ`.** The prime `53` — the smallest prime dividing no sporadic
group order — already separates the eighteen sporadic Euler factors from `ζ(s)`. -/
theorem sporadicCeiling_lt_zeta {s : ℝ} (hs : 1 < s) : sporadicCeiling s < zetaR s := by
  have hs0 : (0 : ℝ) < s := by linarith
  have h53 : (53 : ℕ) ∉ sporadicPrimes := by decide
  have hprimes : ∀ p ∈ insert 53 sporadicPrimes, Nat.Prime p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · norm_num
    · exact prime_of_mem_sporadicPrimes p hp
  have hle : ∏ p ∈ insert 53 sporadicPrimes, eulerFactor p s ≤ zetaR s :=
    prod_eulerFactor_le_zeta hs _ hprimes
  rw [Finset.prod_insert h53] at hle
  have hpos : 0 < sporadicCeiling s :=
    Finset.prod_pos fun p hp => eulerFactor_pos (prime_of_mem_sporadicPrimes p hp).two_le hs0
  have h1 : 1 < eulerFactor 53 s := one_lt_eulerFactor (by norm_num) hs0
  calc sporadicCeiling s = 1 * sporadicCeiling s := (one_mul _).symm
    _ < eulerFactor 53 s * sporadicCeiling s := mul_lt_mul_of_pos_right h1 hpos
    _ ≤ zetaR s := hle

/-! ## The ceiling, exactly, at an integer `s` -/

/-- The eighteen untruncated Euler factors at a natural number `s`, as an exact rational
number: `∏_p (1 - p^{-s})⁻¹`. -/
def ceilingQ (s : ℕ) : ℚ := (lcmFactors.map fun pe => (1 - (((pe.1 : ℚ) ^ s)⁻¹))⁻¹).prod

theorem sporadicPrimes_eq_toFinset : sporadicPrimes = (lcmFactors.map Prod.fst).toFinset := by
  decide

theorem nodup_lcmPrimes : (lcmFactors.map Prod.fst).Nodup := by decide

/-- A product over the eighteen sporadic primes is the corresponding list product. -/
theorem prod_sporadicPrimes (f : ℕ → ℝ) :
    ∏ p ∈ sporadicPrimes, f p = (lcmFactors.map (fun pe => f pe.1)).prod := by
  rw [sporadicPrimes_eq_toFinset, List.prod_toFinset _ nodup_lcmPrimes, List.map_map]
  rfl

/-- **The exact value of the ceiling at every integer `s`.** -/
theorem sporadicCeiling_natCast (s : ℕ) : sporadicCeiling (s : ℝ) = (ceilingQ s : ℝ) := by
  rw [sporadicCeiling, prod_sporadicPrimes, ceilingQ, Rat.cast_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun pe _ => ?_)
  simp only [Function.comp_apply, eulerFactor, rpow_neg_natCast (by positivity : (0:ℝ) ≤ (pe.1 : ℝ)) s]
  push_cast
  ring_nf

/-- The lcm's mass never exceeds the ceiling, as exact rational numbers. -/
theorem lcmMassQ_le_ceilingQ {s : ℕ} (hs : 1 ≤ s) : lcmMassQ s ≤ ceilingQ s := by
  have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have h : ((lcmMassQ s : ℚ) : ℝ) ≤ ((ceilingQ s : ℚ) : ℝ) := by
    rw [← divisorSum_sporadicLcm, ← sporadicCeiling_natCast]
    exact divisorSum_sporadicLcm_le_sporadicCeiling hs0
  exact_mod_cast h

/-- Every sporadic group's mass is under the ceiling, as exact rational numbers. -/
theorem massQ_le_ceilingQ {G : Group} (hG : G ∈ groups) {s : ℕ} (hs : 1 ≤ s) :
    massQ G s ≤ ceilingQ s :=
  le_trans (massQ_le_lcmMassQ hG s) (lcmMassQ_le_ceilingQ hs)

/-- The ceiling at `s = 2`, to five decimals: `1.63972…`. -/
theorem ceilingQ_two_band : 163972 / 100000 < ceilingQ 2 ∧ ceilingQ 2 < 163973 / 100000 := by
  constructor <;> norm_num [ceilingQ, lcmFactors]

/-- **The lcm all but attains the ceiling**: at `s = 2` the two differ by less than `5·10^{-5}`,
so the twenty-six orders already exhaust what the sporadic primes can carry. -/
theorem lcm_near_ceiling : 0 < ceilingQ 2 - lcmMassQ 2 ∧ ceilingQ 2 - lcmMassQ 2 < 1 / 20000 := by
  constructor <;> norm_num [ceilingQ, lcmMassQ, lcmFactors, Finset.sum_range_succ]

/-- **The permanent gap to `ζ(2)`.** No number built from sporadic primes has Dirichlet mass
within `0.005` of `ζ(2) = π²/6`. -/
theorem sporadicCeiling_two_gap : sporadicCeiling 2 < zetaR 2 - 5 / 1000 := by
  have hval : sporadicCeiling ((2 : ℕ) : ℝ) = (ceilingQ 2 : ℝ) := sporadicCeiling_natCast 2
  have hcast : sporadicCeiling 2 = (ceilingQ 2 : ℝ) := by simpa using hval
  have hb : ((ceilingQ 2 : ℚ) : ℝ) < ((163973 / 100000 : ℚ) : ℝ) := by
    exact_mod_cast ceilingQ_two_band.2
  push_cast at hb
  have hz := zetaR_two_gt
  rw [hcast]
  linarith

/-! ## The curves are continuous, and they cross -/

/-- The Dirichlet mass of a fixed `n` is a continuous function of `s`. -/
theorem continuous_divisorSum (n : ℕ) : Continuous (divisorSum n) := by
  refine continuous_finset_sum _ fun d hd => ?_
  have hd0 : ((d : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
  exact (Real.continuous_const_rpow hd0).comp continuous_neg

/-- **Where the ranking swaps, the curves meet.** If the mass of `G` is below that of `H` at
the integer `a` and above it at the integer `b`, then at some real `s` strictly between the two
the curves cross. -/
theorem exists_crossing_of_swap {G H : Group} (hG : G ∈ groups) (hH : H ∈ groups) {a b : ℕ}
    (hab : a < b) (h1 : massQ G a < massQ H a) (h2 : massQ H b < massQ G b) :
    ∃ s ∈ Set.Ioo (a : ℝ) (b : ℝ), divisorSum G.order s = divisorSum H.order s := by
  set f : ℝ → ℝ := fun s => divisorSum H.order s - divisorSum G.order s with hf
  have hcont : ContinuousOn f (Set.Icc (a : ℝ) (b : ℝ)) :=
    ((continuous_divisorSum H.order).sub (continuous_divisorSum G.order)).continuousOn
  have hfa : 0 < f (a : ℝ) := by
    have : ((massQ G a : ℚ) : ℝ) < ((massQ H a : ℚ) : ℝ) := by exact_mod_cast h1
    rw [hf]
    simp only
    rw [divisorSum_order_nat hG, divisorSum_order_nat hH]
    linarith
  have hfb : f (b : ℝ) < 0 := by
    have : ((massQ H b : ℚ) : ℝ) < ((massQ G b : ℚ) : ℝ) := by exact_mod_cast h2
    rw [hf]
    simp only
    rw [divisorSum_order_nat hG, divisorSum_order_nat hH]
    linarith
  have hle : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab.le
  have hmem : (0 : ℝ) ∈ Set.Ioo (f (b : ℝ)) (f (a : ℝ)) := ⟨hfb, hfa⟩
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Ioo' hle hcont hmem
  refine ⟨s, hs, ?_⟩
  have : divisorSum H.order s - divisorSum G.order s = 0 := hs0
  linarith

/-- **`J1` and `J3` cross between `s = 1` and `s = 2`.** -/
theorem janko_curves_cross :
    ∃ s ∈ Set.Ioo (1 : ℝ) 2, divisorSum janko1.order s = divisorSum janko3.order s := by
  have h := exists_crossing_of_swap janko1_mem janko3_mem (a := 1) (b := 2) (by norm_num)
    ranking_swaps_one_two.1 ranking_swaps_one_two.2
  simpa using h

/-- **`M11` and `J3` cross between `s = 2` and `s = 3`**: that is where the bottom of the table
changes hands. -/
theorem bottom_curves_cross :
    ∃ s ∈ Set.Ioo (2 : ℝ) 3, divisorSum mathieu11.order s = divisorSum janko3.order s := by
  have h := exists_crossing_of_swap mathieu11_mem janko3_mem (a := 2) (b := 3) (by norm_num)
    minimum_swaps_two_three.1 minimum_swaps_two_three.2
  simpa using h

end SporadicClosure
