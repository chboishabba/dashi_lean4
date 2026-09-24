/-
# What the diagram taught us

The previous files built the objects: the twenty-six sporadic groups with their prime
factorizations (`RequestProject/SporadicGroups.lean`), the comparison of the Monster's
factors with the Euler factors of `ζ` (`RequestProject/MonsterZeta.lean`), and the Hecke
"shape" of each group (`RequestProject/HeckeShapes.lean`).

This file is the *conclusion*: the lessons that the whole picture teaches, each one stated
as a theorem and proved.

* **Lesson 1 — a group order is a truncated Euler product.** Nothing in the comparison is
  special to the Monster: for *every* `n ≠ 0` the divisor sum `∑_{d ∣ n} d^{-s}` is a finite
  product of truncated zeta factors and is bounded by `ζ(s)` (`divisorSum_le_zeta`).
  The Monster is only the largest instance.

* **Lesson 2 — the containment is strict, and the gap is the rest of the primes.** The
  fifteen supersingular Euler factors never reach `ζ` (`monsterEulerProduct_lt_zeta`);
  what is missing is exactly the primes the Monster does not see, `37` being the first.

* **Lesson 3 — size sits at the small primes.** The `{2,3,5,7,11,13}`-part of `|M|` exceeds
  `|M|^{2/3}` while the nine primes `17,…,71` together stay below `|M|^{1/3}`, and the
  prime `2` alone lies between `|M|^{1/4}` and `|M|^{1/3}`.

* **Lesson 4 — the zeta defect sits at the large primes.** The relative defect between the
  Monster's local factor at `p` and the zeta factor at `p` is exactly `p^{-(v_p+1)s}`, so it
  is *smallest* precisely where the exponent is largest. The defect at `2` (with its
  forty-six exponents) is smaller than the defect at `71`, for every `s > 0`
  (`relDefect_two_lt_relDefect_seventyone`). Size and defect live at opposite ends of the
  prime list.

* **Lesson 5 — above `13` the Monster is squarefree.** Having exponent `≥ 2` in `|M|` is the
  same as being one of the six primes `≤ 13` (`monster_two_le_exponent_iff`); this is why
  only the small fibers of the picture ever curve.

* **Lesson 6 — `46` is the ceiling of the whole table.** No prime power in any of the
  twenty-six sporadic orders has exponent above `46`, and `46` is attained only by the
  Monster at `2` (`sporadic_exponent_le_46`, `exponent_eq_46_iff`), while every sporadic
  group has even order, so all twenty-six sit on the ladder `2^1, …, 2^46`.

* **Lesson 7 — the same small/large split governs the τ side.** In Hecke space the nine
  large primes give the Monster nine of its ninety-five coordinates and less than a fifth of
  its mass, so the shape too is decided by the small primes.
-/
import Mathlib
import RequestProject.MonsterZeta
import RequestProject.HeckeShapes

open Finset

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Lessons

open Sporadic

variable {s : ℝ}

/-! ## Lesson 1: a group order is a truncated Euler product, and the Monster is not special -/

/-- The Dirichlet mass carried by the divisors of any `n`. -/
noncomputable def divisorSum (n : ℕ) (s : ℝ) : ℝ := ∑ d ∈ n.divisors, (d : ℝ) ^ (-s)

/-- **Every finite order is a finite Euler product.** For any `n ≠ 0` the divisor sum of `n`
is the product, over the primes dividing `n`, of the zeta Euler factor truncated at the
exponent that prime carries in `n`. The Monster is just one instance of this. -/
theorem divisorSum_eq_prod (s : ℝ) {n : ℕ} (hn : n ≠ 0) :
    divisorSum n s = ∏ p ∈ n.primeFactors, truncFactor p (n.factorization p) s :=
  sum_divisors_rpow_eq_prod s hn

/-- **Every finite order sits below `ζ`.** For any `n` and any `s > 1`. -/
theorem divisorSum_le_zeta (hs : 1 < s) (n : ℕ) : divisorSum n s ≤ zetaR s :=
  sum_le_zetaR hs _

/-- The Monster's case is the special case `n = |M|`. -/
theorem monsterDivisorSum_eq_divisorSum (s : ℝ) :
    monsterDivisorSum s = divisorSum monsterOrder s := rfl

/-! ## Lesson 2: the containment in `ζ` is strict -/

/-- Each zeta Euler factor is strictly larger than `1`. -/
theorem one_lt_eulerFactor {p : ℕ} (hp : 2 ≤ p) (hs : 0 < s) : 1 < eulerFactor p s := by
  obtain ⟨hx0, hx1⟩ := rpow_neg_mem_Ioo hp hs
  rw [eulerFactor, lt_inv_comm₀ (by norm_num) (by linarith)]
  linarith

/-- **The fifteen supersingular factors never reach `ζ`.** The missing mass is the primes the
Monster does not see; `37` alone already separates the two. -/
theorem monsterEulerProduct_lt_zeta (hs : 1 < s) : monsterEulerProduct s < zetaR s := by
  have hs0 : (0 : ℝ) < s := by linarith
  have h37 : (37 : ℕ) ∉ monsterPrimes := by decide
  have hprimes : ∀ p ∈ insert 37 monsterPrimes, Nat.Prime p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · norm_num
    · exact prime_of_mem_sporadicPrimes p (monsterPrimes_subset hp)
  have hle : ∏ p ∈ insert 37 monsterPrimes, eulerFactor p s ≤ zetaR s :=
    prod_eulerFactor_le_zeta hs _ hprimes
  rw [Finset.prod_insert h37] at hle
  have hpos : 0 < monsterEulerProduct s :=
    Finset.prod_pos fun p hp =>
      eulerFactor_pos (prime_of_mem_sporadicPrimes p (monsterPrimes_subset hp)).two_le hs0
  have h1 : 1 < eulerFactor 37 s := one_lt_eulerFactor (by norm_num) hs0
  calc monsterEulerProduct s = 1 * monsterEulerProduct s := (one_mul _).symm
    _ < eulerFactor 37 s * monsterEulerProduct s := by
        exact mul_lt_mul_of_pos_right h1 hpos
    _ ≤ zetaR s := hle

/-- **The full comparison.** For every real `s > 1` the Monster's divisor sum is at most its
fifteen-factor Euler product, and that is *strictly* below `ζ(s)`. -/
theorem monster_strictly_inside_zeta (hs : 1 < s) :
    monsterDivisorSum s ≤ monsterEulerProduct s ∧ monsterEulerProduct s < zetaR s :=
  ⟨monsterDivisorSum_le_monsterEulerProduct (by linarith), monsterEulerProduct_lt_zeta hs⟩

/-! ## Lesson 3: the size of `|M|` sits at the small primes -/

/-- The part of `|M|` carried by the six primes `p ≤ 13`. -/
def monsterSmallPart : ℕ := 2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3

/-- The part of `|M|` carried by the nine primes `p ≥ 17`; it is squarefree. -/
def monsterLargePart : ℕ := 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71

theorem monsterOrder_eq_parts : monsterOrder = monsterSmallPart * monsterLargePart := by
  rw [monster_order_value, monsterSmallPart, monsterLargePart]
  norm_num

/-- **The six small primes carry more than two thirds of `|M|`**: their part exceeds
`|M|^{2/3}`. -/
theorem monsterOrder_sq_lt_smallPart_cube : monsterOrder ^ 2 < monsterSmallPart ^ 3 := by
  rw [monster_order_value, monsterSmallPart]
  norm_num

/-- **The nine large primes carry less than a third of `|M|`**: their part stays below
`|M|^{1/3}`. -/
theorem largePart_cube_lt_monsterOrder : monsterLargePart ^ 3 < monsterOrder := by
  rw [monster_order_value, monsterLargePart]
  norm_num

/-- **The forty-six exponents of `2` alone account for between a quarter and a third of
`|M|`**: `|M|^{1/4} < 2^46 < |M|^{1/3}`. -/
theorem twoPart_between : (2 ^ 46 : ℕ) ^ 3 < monsterOrder ∧ monsterOrder < (2 ^ 46 : ℕ) ^ 4 := by
  rw [monster_order_value]
  constructor <;> norm_num

/-! ## Lesson 4: the defect against `ζ` sits at the large primes -/

/-- The relative defect at `p`: the fraction of the zeta Euler factor at `p` that the
truncation at exponent `e` misses. -/
noncomputable def relDefect (p e : ℕ) (s : ℝ) : ℝ := ((p : ℝ) ^ (-s)) ^ (e + 1)

/-- The defect between the local factor of a finite order and the local factor of `ζ` is
exactly the relative defect times the zeta factor. -/
theorem eulerFactor_sub_truncFactor_eq {p : ℕ} (hp : 2 ≤ p) (hs : 0 < s) (e : ℕ) :
    eulerFactor p s - truncFactor p e s = relDefect p e s * eulerFactor p s :=
  eulerFactor_sub_truncFactor hp hs e

theorem rpow_neg_pow (x : ℝ) (hx : 0 ≤ x) (s : ℝ) (n : ℕ) :
    (x ^ (-s)) ^ n = (x ^ n : ℝ) ^ (-s) := by
  rw [← Real.rpow_natCast (x ^ (-s)) n, ← Real.rpow_natCast x n, ← Real.rpow_mul hx,
    ← Real.rpow_mul hx]
  ring_nf

/-- The relative defect is `(p^{e+1})^{-s}`: it is governed by the prime power `p^{e+1}`
alone. -/
theorem relDefect_eq (p e : ℕ) (s : ℝ) : relDefect p e s = ((p ^ (e + 1) : ℕ) : ℝ) ^ (-s) := by
  rw [relDefect, rpow_neg_pow _ (Nat.cast_nonneg p)]
  push_cast
  ring_nf

/-- **The bigger the prime power, the smaller the defect.** -/
theorem relDefect_lt_relDefect {p e q f : ℕ} (hq : 0 < q) (hs : 0 < s)
    (h : q ^ (f + 1) < p ^ (e + 1)) : relDefect p e s < relDefect q f s := by
  rw [relDefect_eq, relDefect_eq, Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  have hq0 : (0 : ℝ) < ((q ^ (f + 1) : ℕ) : ℝ) := by positivity
  have hlt : ((q ^ (f + 1) : ℕ) : ℝ) < ((p ^ (e + 1) : ℕ) : ℝ) := by exact_mod_cast h
  exact (inv_lt_inv₀ (Real.rpow_pos_of_pos (hq0.trans hlt) s)
    (Real.rpow_pos_of_pos hq0 s)).mpr (Real.rpow_lt_rpow hq0.le hlt hs)

/-- **Size and defect live at opposite ends of the prime list.** The prime `2`, which carries
the largest part of `|M|`, is also the prime at which the Monster's local factor is closest
to the corresponding factor of `ζ`; the prime `71`, which contributes least to the size, is
where the truncation loses the most. -/
theorem relDefect_two_lt_relDefect_seventyone (hs : 0 < s) :
    relDefect 2 46 s < relDefect 71 1 s :=
  relDefect_lt_relDefect (by norm_num) hs (by norm_num)

/-- At every prime of `|M|` other than `2`, the prime power `p^{v_p+1}` controlling the local
defect is smaller than `2^47`. -/
theorem monster_defect_power_lt :
    ∀ p ∈ monsterPrimes, p ≠ 2 → p ^ (monster.exponent p + 1) < 2 ^ (46 + 1) := by decide

/-- The same statement across the whole factorization: at every prime of `|M|` other than
`2`, the truncation loses relatively more than it does at `2`. -/
theorem relDefect_two_min (hs : 0 < s) :
    ∀ p ∈ monsterPrimes, p ≠ 2 →
      relDefect 2 46 s < relDefect p (monsterOrder.factorization p) s := by
  have hexp : ∀ p ∈ monsterPrimes, monsterOrder.factorization p = monster.exponent p := by
    intro p _
    rw [monsterOrder, exponent_eq_factorization monster_mem p]
  intro p hp hp2
  rw [hexp p hp]
  have hpos : 0 < p := (prime_of_mem_sporadicPrimes p (monsterPrimes_subset hp)).pos
  exact relDefect_lt_relDefect hpos hs (monster_defect_power_lt p hp hp2)

/-! ## Lesson 5: above `13` the Monster is squarefree -/

/-- **Exponent `≥ 2` in `|M|` means prime `≤ 13`.** -/
theorem monster_two_le_exponent_iff :
    ∀ p ∈ monsterPrimes, (2 ≤ monsterOrder.factorization p ↔ p ≤ 13) := by
  intro p hp
  rw [monsterOrder, exponent_eq_factorization monster_mem p]
  revert hp
  revert p
  decide

/-- Consequently every prime `≥ 17` divides `|M|` exactly once. -/
theorem monster_exponent_one_of_large :
    ∀ p ∈ monsterPrimes, 17 ≤ p → monsterOrder.factorization p = 1 := by
  intro p hp hple
  rw [monsterOrder, exponent_eq_factorization monster_mem p]
  revert hp hple
  revert p
  decide

/-- The large part of `|M|` really is squarefree. -/
theorem squarefree_monsterLargePart : Squarefree monsterLargePart := by
  rw [monsterLargePart]
  decide +kernel

/-! ## Lesson 6: `46` is the ceiling of the whole sporadic table -/

/-- No prime power in any of the twenty-six sporadic orders carries an exponent above `46`. -/
theorem sporadic_exponent_le_46 : ∀ G ∈ Sporadic.groups, ∀ pe ∈ G.factors, pe.2 ≤ 46 := by
  decide

/-- And `46` is reached exactly once: by the Monster, at the prime `2`. -/
theorem exponent_eq_46_iff :
    ∀ G ∈ Sporadic.groups, ∀ pe ∈ G.factors, pe.2 = 46 ↔ (G.name = "M" ∧ pe.1 = 2) := by
  decide

/-- Every sporadic group has even order, so all twenty-six sit somewhere on the ladder
`2^1, …, 2^46` of the picture. -/
theorem sporadic_on_the_two_ladder :
    ∀ G ∈ Sporadic.groups, 1 ≤ G.exponent 2 ∧ G.exponent 2 ≤ 46 := by
  decide

/-- The ladder has exactly forty-six rungs. -/
theorem two_ladder_card : (PrimeFibers.primePowerFiber 2 (2 ^ 46)).card = 46 :=
  Sporadic.card_primePowerFiber_two_46

/-! ## Lesson 7: the same split governs the τ side -/

/-- In Hecke space the Monster has `95 = Ω(|M|)` coordinates, of which only `9` come from the
nine primes `≥ 17`. -/
theorem hecke_dim_split :
    HeckeShapes.dim Sporadic.monster = 95 ∧ HeckeShapes.largeDim Sporadic.monster = 9 :=
  ⟨HeckeShapes.dim_monster, HeckeShapes.largeDim_monster⟩

/-- **The small primes decide the shape too.** The nine large primes carry less than a third
of the mass carried by the six small ones. -/
theorem hecke_mass_small_dominates :
    3 * HeckeShapes.largeHeckeMass Sporadic.monster < HeckeShapes.smallHeckeMass Sporadic.monster :=
  HeckeShapes.monster_large_lt_third_small

/-! ## The summary statement

The two sides of the picture, in one place: the Monster's Dirichlet mass is a finite
truncation of `ζ` that never reaches it, its size is concentrated on the small primes while
its defect against `ζ` is concentrated on the large ones, and above `13` it is squarefree.
-/

theorem what_we_learned (hs : 1 < s) :
    -- the Monster is a truncated Euler product, strictly inside ζ
    (monsterDivisorSum s = ∏ p ∈ monsterPrimes, truncFactor p (monsterOrder.factorization p) s
      ∧ monsterDivisorSum s ≤ monsterEulerProduct s ∧ monsterEulerProduct s < zetaR s) ∧
    -- the size is carried by the small primes
    (monsterOrder = monsterSmallPart * monsterLargePart
      ∧ monsterOrder ^ 2 < monsterSmallPart ^ 3
      ∧ monsterLargePart ^ 3 < monsterOrder) ∧
    -- the defect against ζ is carried by the large primes
    (∀ p ∈ monsterPrimes, p ≠ 2 →
        relDefect 2 46 s < relDefect p (monsterOrder.factorization p) s) ∧
    -- and above 13 the Monster is squarefree
    (∀ p ∈ monsterPrimes, (2 ≤ monsterOrder.factorization p ↔ p ≤ 13)) := by
  refine ⟨⟨monsterDivisorSum_eq_prod s, monster_strictly_inside_zeta hs⟩,
    ⟨monsterOrder_eq_parts, monsterOrder_sq_lt_smallPart_cube, largePart_cube_lt_monsterOrder⟩,
    relDefect_two_min (by linarith), monster_two_le_exponent_iff⟩

end Lessons
