/-
# The twenty-six sporadic simple groups and their prime factors

This file records the orders of the twenty-six sporadic finite simple groups in factored
form, proves that the recorded exponents really are the `p`-adic valuations of the orders,
and identifies the primes that occur.

The headline data point is the Monster:

```
|M| = 2^46 · 3^20 · 5^9 · 7^6 · 11^2 · 13^3 · 17 · 19 · 23 · 29 · 31 · 41 · 47 · 59 · 71
```

so the fiber of `2` now carries the forty-six exponents `2^1, …, 2^46`, and the primes
dividing `|M|` are the fifteen supersingular primes, all of them among the first twenty
primes `2, …, 71` used elsewhere in this project.
-/
import Mathlib
import RequestProject.PrimeFibers

open scoped BigOperators

open PrimeFibers

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Sporadic

/-! ## Factored natural numbers -/

/-- The natural number described by a list of `(prime, exponent)` pairs. -/
def factProd : List (ℕ × ℕ) → ℕ
  | [] => 1
  | pe :: t => pe.1 ^ pe.2 * factProd t

/-- A list of `(prime, exponent)` pairs is *well formed* when every entry is a prime with a
positive exponent and no prime is repeated. -/
def WF (l : List (ℕ × ℕ)) : Prop :=
  (∀ pe ∈ l, Nat.Prime pe.1 ∧ 0 < pe.2) ∧ l.Pairwise (fun a b => a.1 ≠ b.1)

instance : ∀ l : List (ℕ × ℕ), Decidable (WF l) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem WF.tail {pe : ℕ × ℕ} {t : List (ℕ × ℕ)} (h : WF (pe :: t)) : WF t :=
  ⟨fun x hx => h.1 x (List.mem_cons_of_mem _ hx), (List.pairwise_cons.mp h.2).2⟩

theorem factProd_ne_zero : ∀ (l : List (ℕ × ℕ)), WF l → factProd l ≠ 0 := by
  intro l
  induction l with
  | nil => intro _; simp [factProd]
  | cons pe t ih =>
      intro h
      have hp : Nat.Prime pe.1 := (h.1 pe (List.mem_cons_self ..)).1
      have ht := ih h.tail
      simp only [factProd, ne_eq, mul_eq_zero, not_or]
      exact ⟨pow_ne_zero _ hp.pos.ne', ht⟩

/-- The prime factors of a well-formed factored number are exactly the listed primes. -/
theorem primeFactors_factProd : ∀ (l : List (ℕ × ℕ)), WF l →
    (factProd l).primeFactors = (l.map Prod.fst).toFinset := by
  intro l
  induction l with
  | nil => intro _; simp [factProd]
  | cons pe t ih =>
      intro h
      have hp : Nat.Prime pe.1 := (h.1 pe (List.mem_cons_self ..)).1
      have he : 0 < pe.2 := (h.1 pe (List.mem_cons_self ..)).2
      have ht := ih h.tail
      have h0 : factProd t ≠ 0 := factProd_ne_zero t h.tail
      have hpow : (pe.1 ^ pe.2) ≠ 0 := pow_ne_zero _ hp.pos.ne'
      simp only [factProd, Nat.primeFactors_mul hpow h0, ht,
        Nat.primeFactors_pow _ he.ne', hp.primeFactors, List.map_cons, List.toFinset_cons]
      rfl

/-- The `p`-adic valuation of a well-formed factored number is read off from the list. -/
theorem factorization_factProd : ∀ (l : List (ℕ × ℕ)), WF l → ∀ q : ℕ,
    (factProd l).factorization q = ((l.filter fun pe => pe.1 = q).map Prod.snd).sum := by
  intro l
  induction l with
  | nil => intro _ q; simp [factProd]
  | cons pe t ih =>
      intro h q
      have hp : Nat.Prime pe.1 := (h.1 pe (List.mem_cons_self ..)).1
      have h0 : factProd t ≠ 0 := factProd_ne_zero t h.tail
      have hpow : (pe.1 ^ pe.2) ≠ 0 := pow_ne_zero _ hp.pos.ne'
      have hfac : (factProd (pe :: t)).factorization q
          = (pe.1 ^ pe.2).factorization q + (factProd t).factorization q := by
        simp [factProd, Nat.factorization_mul hpow h0]
      rw [hfac, ih h.tail q, hp.factorization_pow]
      by_cases hq : pe.1 = q
      · subst hq
        simp
      · simp [hq]

/-! ## The table of the twenty-six sporadic groups -/

/-- A sporadic simple group, recorded by its name and the factorization of its order. -/
structure Group where
  /-- ATLAS name of the group. -/
  name : String
  /-- The `(prime, exponent)` pairs of its order. -/
  factors : List (ℕ × ℕ)
  deriving DecidableEq, Repr

/-- The order of a sporadic group, as the product of its prime powers. -/
def Group.order (G : Group) : ℕ := factProd G.factors

/-- The exponent of the prime `p` in the order of `G`, read off from the table. -/
def Group.exponent (G : Group) (p : ℕ) : ℕ :=
  ((G.factors.filter fun pe => pe.1 = p).map Prod.snd).sum

/-- The orders of the twenty-six sporadic simple groups, in factored form. -/
def groups : List Group :=
  [ ⟨"M11",   [(2,4),(3,2),(5,1),(11,1)]⟩,
    ⟨"M12",   [(2,6),(3,3),(5,1),(11,1)]⟩,
    ⟨"M22",   [(2,7),(3,2),(5,1),(7,1),(11,1)]⟩,
    ⟨"M23",   [(2,7),(3,2),(5,1),(7,1),(11,1),(23,1)]⟩,
    ⟨"M24",   [(2,10),(3,3),(5,1),(7,1),(11,1),(23,1)]⟩,
    ⟨"J1",    [(2,3),(3,1),(5,1),(7,1),(11,1),(19,1)]⟩,
    ⟨"J2",    [(2,7),(3,3),(5,2),(7,1)]⟩,
    ⟨"J3",    [(2,7),(3,5),(5,1),(17,1),(19,1)]⟩,
    ⟨"J4",    [(2,21),(3,3),(5,1),(7,1),(11,3),(23,1),(29,1),(31,1),(37,1),(43,1)]⟩,
    ⟨"HS",    [(2,9),(3,2),(5,3),(7,1),(11,1)]⟩,
    ⟨"McL",   [(2,7),(3,6),(5,3),(7,1),(11,1)]⟩,
    ⟨"He",    [(2,10),(3,3),(5,2),(7,3),(17,1)]⟩,
    ⟨"Ru",    [(2,14),(3,3),(5,3),(7,1),(13,1),(29,1)]⟩,
    ⟨"Suz",   [(2,13),(3,7),(5,2),(7,1),(11,1),(13,1)]⟩,
    ⟨"ON",    [(2,9),(3,4),(5,1),(7,3),(11,1),(19,1),(31,1)]⟩,
    ⟨"Co1",   [(2,21),(3,9),(5,4),(7,2),(11,1),(13,1),(23,1)]⟩,
    ⟨"Co2",   [(2,18),(3,6),(5,3),(7,1),(11,1),(23,1)]⟩,
    ⟨"Co3",   [(2,10),(3,7),(5,3),(7,1),(11,1),(23,1)]⟩,
    ⟨"Fi22",  [(2,17),(3,9),(5,2),(7,1),(11,1),(13,1)]⟩,
    ⟨"Fi23",  [(2,18),(3,13),(5,2),(7,1),(11,1),(13,1),(17,1),(23,1)]⟩,
    ⟨"Fi24'", [(2,21),(3,16),(5,2),(7,3),(11,1),(13,1),(17,1),(23,1),(29,1)]⟩,
    ⟨"HN",    [(2,14),(3,6),(5,6),(7,1),(11,1),(19,1)]⟩,
    ⟨"Ly",    [(2,8),(3,7),(5,6),(7,1),(11,1),(31,1),(37,1),(67,1)]⟩,
    ⟨"Th",    [(2,15),(3,10),(5,3),(7,2),(13,1),(19,1),(31,1)]⟩,
    ⟨"B",     [(2,41),(3,13),(5,6),(7,2),(11,1),(13,1),(17,1),(19,1),(23,1),(31,1),(47,1)]⟩,
    ⟨"M",     [(2,46),(3,20),(5,9),(7,6),(11,2),(13,3),(17,1),(19,1),(23,1),(29,1),(31,1),
               (41,1),(47,1),(59,1),(71,1)]⟩ ]

/-- There are twenty-six sporadic groups. -/
theorem length_groups : groups.length = 26 := rfl

/-- The twenty-six entries carry twenty-six distinct names. -/
theorem nodup_names : (groups.map Group.name).Nodup := by decide

/-- Every entry of the table is a genuine factorization: primes, positive exponents, no
repetitions. -/
theorem wf_groups : ∀ G ∈ groups, WF G.factors := by decide

/-- The recorded exponents are exactly the `p`-adic valuations of the orders. -/
theorem exponent_eq_factorization {G : Group} (hG : G ∈ groups) (p : ℕ) :
    G.order.factorization p = G.exponent p :=
  factorization_factProd G.factors (wf_groups G hG) p

theorem order_ne_zero {G : Group} (hG : G ∈ groups) : G.order ≠ 0 :=
  factProd_ne_zero G.factors (wf_groups G hG)

/-! ## The Monster -/

/-- The Monster. -/
def monster : Group := ⟨"M", [(2,46),(3,20),(5,9),(7,6),(11,2),(13,3),(17,1),(19,1),(23,1),
  (29,1),(31,1),(41,1),(47,1),(59,1),(71,1)]⟩

theorem monster_mem : monster ∈ groups := by decide

/-- The order of the Monster group. -/
def monsterOrder : ℕ := monster.order

theorem monsterOrder_ne_zero : monsterOrder ≠ 0 := order_ne_zero monster_mem

theorem monster_order_value :
    monsterOrder = 808017424794512875886459904961710757005754368000000000 := by
  norm_num [monsterOrder, Group.order, monster, factProd]

/-! ## Exponents -/

/-- **Forty-six exponents of 2.** The `2`-adic valuation of `|M|` is `46`. -/
theorem monster_factorization_two : monsterOrder.factorization 2 = 46 :=
  exponent_eq_factorization monster_mem 2

theorem monster_factorization_three : monsterOrder.factorization 3 = 20 :=
  exponent_eq_factorization monster_mem 3

theorem monster_factorization_five : monsterOrder.factorization 5 = 9 :=
  exponent_eq_factorization monster_mem 5

theorem monster_factorization_seven : monsterOrder.factorization 7 = 6 :=
  exponent_eq_factorization monster_mem 7

theorem monster_factorization_eleven : monsterOrder.factorization 11 = 2 :=
  exponent_eq_factorization monster_mem 11

theorem monster_factorization_thirteen : monsterOrder.factorization 13 = 3 :=
  exponent_eq_factorization monster_mem 13

theorem monster_factorization_seventyone : monsterOrder.factorization 71 = 1 :=
  exponent_eq_factorization monster_mem 71

/-- `2 ^ 46` divides `|M|`. -/
theorem two_pow_46_dvd_monster : 2 ^ 46 ∣ monsterOrder :=
  (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two monsterOrder_ne_zero).mpr
    (by rw [monster_factorization_two])

/-- `2 ^ 47` does not divide `|M|`: the power of two is exactly `46`. -/
theorem two_pow_47_not_dvd_monster : ¬ (2 ^ 47 ∣ monsterOrder) := by
  intro h
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two monsterOrder_ne_zero).mp h
  rw [monster_factorization_two] at this
  omega

/-- Among all twenty-six sporadic groups, the Monster has the largest power of `2`, namely
`2 ^ 46`. -/
theorem exponent_two_le_46 : ∀ G ∈ groups, G.exponent 2 ≤ 46 := by decide

theorem monster_exponent_two : monster.exponent 2 = 46 := by decide

/-- Equivalently, in terms of valuations: no sporadic group order is divisible by a larger
power of `2` than the Monster's. -/
theorem factorization_two_le_monster {G : Group} (hG : G ∈ groups) :
    G.order.factorization 2 ≤ monsterOrder.factorization 2 := by
  rw [exponent_eq_factorization hG, monster_factorization_two]
  exact exponent_two_le_46 G hG

/-! ## The primes occurring in the sporadic groups -/

/-- The fifteen primes dividing the order of the Monster: the supersingular primes. -/
def monsterPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71}

theorem card_monsterPrimes : monsterPrimes.card = 15 := by decide

/-- The primes dividing `|M|` are exactly the fifteen supersingular primes. -/
theorem primeFactors_monsterOrder : monsterOrder.primeFactors = monsterPrimes := by
  rw [monsterOrder, Group.order, primeFactors_factProd _ (wf_groups _ monster_mem)]
  decide

/-- The set of primes dividing the order of at least one sporadic group. -/
def sporadicPrimes : Finset ℕ :=
  (groups.map fun G => (G.factors.map Prod.fst)).flatten.toFinset

theorem card_sporadicPrimes : sporadicPrimes.card = 18 := by decide

/-- The eighteen primes occurring in the twenty-six sporadic groups. -/
theorem sporadicPrimes_eq :
    sporadicPrimes = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 59, 67, 71} := by
  decide

/-- A prime divides some sporadic group order iff it lies in `sporadicPrimes`. -/
theorem mem_sporadicPrimes_iff (p : ℕ) :
    p ∈ sporadicPrimes ↔ ∃ G ∈ groups, p ∈ G.order.primeFactors := by
  constructor
  · intro hp
    simp only [sporadicPrimes, List.mem_toFinset, List.mem_flatten, List.mem_map] at hp
    obtain ⟨l, ⟨G, hG, rfl⟩, hpl⟩ := hp
    refine ⟨G, hG, ?_⟩
    rw [Group.order, primeFactors_factProd _ (wf_groups G hG), List.mem_toFinset]
    exact hpl
  · rintro ⟨G, hG, hp⟩
    rw [Group.order, primeFactors_factProd _ (wf_groups G hG), List.mem_toFinset] at hp
    simp only [sporadicPrimes, List.mem_toFinset, List.mem_flatten, List.mem_map]
    exact ⟨_, ⟨G, hG, rfl⟩, hp⟩

/-- Every element of `sporadicPrimes` is prime (a sanity check on the table). -/
theorem prime_of_mem_sporadicPrimes : ∀ p ∈ sporadicPrimes, Nat.Prime p := by decide

/-- The Monster's primes are among the eighteen sporadic primes. -/
theorem monsterPrimes_subset : monsterPrimes ⊆ sporadicPrimes := by decide

/-- All eighteen sporadic primes are among the first twenty primes `2, …, 71`, so the
sporadic groups live inside the twenty fibers already drawn in this project. -/
theorem sporadicPrimes_subset_first20 : sporadicPrimes ⊆ first20Primes := by decide

/-- Exactly two of the first twenty primes, `53` and `61`, divide no sporadic group. -/
theorem first20Primes_sdiff_sporadicPrimes : first20Primes \ sporadicPrimes = {53, 61} := by
  decide

/-- The three primes occurring in a sporadic group but not in the Monster are `37`, `43`
and `67` (they occur in the pariahs `Ly` and `J4`). -/
theorem sporadicPrimes_sdiff_monsterPrimes : sporadicPrimes \ monsterPrimes = {37, 43, 67} := by
  decide

/-! ## The fiber of `2`, extended to `2 ^ 46` -/

/-- The forty-six exponents of `2`: the fiber of `2` up to `2 ^ 46` has exactly `46`
elements, namely `2^1, 2^2, …, 2^46`. -/
theorem card_primePowerFiber_two_46 : (primePowerFiber 2 (2 ^ 46)).card = 46 := by
  rw [card_primePowerFiber (by norm_num) (by positivity), Nat.log_pow (by norm_num : 1 < 2)]

/-- More precisely, the fiber of `2` up to `2 ^ 46` is the set of the forty-six powers
`2 ^ k`, `1 ≤ k ≤ 46`. -/
theorem primePowerFiber_two_46 :
    primePowerFiber 2 (2 ^ 46) = (Finset.Icc 1 46).image (fun k => 2 ^ k) := by
  rw [primePowerFiber_eq_image (by norm_num) (by positivity), Nat.log_pow (by norm_num : 1 < 2)]

end Sporadic
