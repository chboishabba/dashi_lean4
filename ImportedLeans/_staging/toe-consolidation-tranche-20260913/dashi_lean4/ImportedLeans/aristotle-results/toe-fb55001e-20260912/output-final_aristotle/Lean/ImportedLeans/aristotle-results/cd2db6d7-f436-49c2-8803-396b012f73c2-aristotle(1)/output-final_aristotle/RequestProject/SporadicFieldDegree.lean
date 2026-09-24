import Mathlib
import RequestProject.ExtensionTowerTree
import RequestProject.SporadicAtlas

/-!
# Where each sporadic group sits in the characteristic-two tower

`RequestProject/SporadicTower.lean` places each sporadic group on a floor of the tower by matrix
size.  This file places it on a *node of the degree tree*, by field size.

For an odd prime `r`, the field `GF(2ᵏ)` contains an element of multiplicative order `r` exactly
when `r ∣ 2ᵏ - 1`, i.e. exactly when the order of `2` modulo `r` divides `k`
(`SporadicFieldDegree.two_pow_mod_eq_one_iff`).  So for a finite group `G` the smallest field of
the char-`2` tower whose multiplicative group can realise *every* odd prime element order allowed
by `|G|` is `GF(2^D)`, where `D` is the least common multiple of those orders of `2`.

* `SporadicFieldDegree.ordTwo` — the order of `2` modulo each prime of the sporadic atlas, checked
  by the kernel (`SporadicFieldDegree.isOrderTwoMod_ordTwo`).
* `SporadicFieldDegree.towerDegree` — the resulting degree `D` for each of the 26 groups; e.g.
  `M₁₁ ↦ 20`, `J₂ ↦ 12`, `Co₁ ↦ 660`, `B ↦ 91080`, `M ↦ 18489240`
  (`SporadicFieldDegree.towerDegree_values`).
* `SporadicFieldDegree.dvd_iff_towerDegree_dvd` — `GF(2ᵏ)` realises all those orders iff
  `D ∣ k`, and `SporadicFieldDegree.isLeast_towerDegree` — `D` is therefore the least such
  positive degree, i.e. a well-defined node of the degree tree of
  `RequestProject/ExtensionTowerTree.lean`.
* `SporadicFieldDegree.exists_unit_orderOf` and `SporadicFieldDegree.towerDegree_dvd_of_orders` —
  the two directions stated inside the fields themselves: `GF(2^D)ˣ` really does contain an
  element of order `r` for every odd prime `r` dividing the group order, and no smaller floor of
  the tower does.
-/

namespace SporadicFieldDegree

open Sporadic

/-! ## The order of `2` modulo a prime -/

/-- `d` is the multiplicative order of `2` modulo `r`. -/
def IsOrderTwoMod (r d : Nat) : Prop :=
  0 < d ∧ 2 ^ d % r = 1 ∧ ∀ e < d, 0 < e → 2 ^ e % r ≠ 1

instance (r d : Nat) : Decidable (IsOrderTwoMod r d) := by
  unfold IsOrderTwoMod; infer_instance

/-- `2ᵏ ≡ 1 (mod r)` exactly when the order of `2` divides `k`. -/
theorem two_pow_mod_eq_one_iff {r d k : Nat} (hr : 2 ≤ r) (hd : IsOrderTwoMod r d) :
    2 ^ k % r = 1 ↔ d ∣ k := by
  obtain ⟨hdpos, hd1, hdmin⟩ := hd
  have h1 : (1 : Nat) % r = 1 := Nat.mod_eq_of_lt (by omega)
  have key : ∀ m : Nat, 2 ^ (d * m) % r = 1 := by
    intro m
    induction m with
    | zero => simpa using h1
    | succ m ih =>
      have : 2 ^ (d * (m + 1)) = 2 ^ (d * m) * 2 ^ d := by rw [← pow_add]; ring_nf
      rw [this, Nat.mul_mod, ih, hd1]
      simpa using h1
  constructor
  · intro hk
    by_contra hnd
    have hmod : k % d ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    have hsplit : 2 ^ k = 2 ^ (d * (k / d)) * 2 ^ (k % d) := by
      rw [← pow_add]
      congr 1
      exact (Nat.div_add_mod k d).symm.trans (by rw [Nat.mul_comm])
    have : 2 ^ (k % d) % r = 1 := by
      have h2 := hk
      rw [hsplit, Nat.mul_mod, key (k / d), one_mul, Nat.mod_mod_of_dvd _ dvd_rfl] at h2
      exact h2
    exact hdmin (k % d) (Nat.mod_lt _ hdpos) (Nat.pos_of_ne_zero hmod) this
  · rintro ⟨m, rfl⟩
    exact key m

/-- For `r ≥ 2`, `r` divides `2ᵏ - 1` exactly when `2ᵏ ≡ 1 (mod r)`. -/
theorem dvd_two_pow_sub_one_iff {r k : Nat} (hr : 2 ≤ r) :
    r ∣ 2 ^ k - 1 ↔ 2 ^ k % r = 1 := by
  have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [← Nat.modEq_iff_dvd' hpos]
  unfold Nat.ModEq
  rw [Nat.mod_eq_of_lt (show 1 < r by omega)]
  exact eq_comm

/-- The order of `2` modulo each prime occurring in the sporadic atlas. -/
def ordTwo : Nat → Nat
  | 3 => 2 | 5 => 4 | 7 => 3 | 11 => 10 | 13 => 12 | 17 => 8 | 19 => 18 | 23 => 11
  | 29 => 28 | 31 => 5 | 37 => 36 | 41 => 20 | 43 => 14 | 47 => 23 | 59 => 58 | 67 => 66
  | 71 => 35 | _ => 1

/-- The table of orders is correct, kernel-checked prime by prime. -/
theorem isOrderTwoMod_ordTwo : ∀ r ∈ Group.allPrimes, r ≠ 2 → IsOrderTwoMod r (ordTwo r) := by
  decide

theorem ordTwo_pos (r : Nat) : 0 < ordTwo r := by
  unfold ordTwo
  split <;> norm_num

/-! ## The degree of the smallest field of the tower for a sporadic group -/

/-- The odd primes dividing the order of a sporadic group. -/
def oddPrimes (S : Group) : List Nat := S.primes.filter (fun r => r ≠ 2)

/-- The degree of the node of the tree at which a sporadic group is realised in the
characteristic-two tower: the least common multiple of the orders of `2` modulo the odd primes
dividing its order. -/
def towerDegree (S : Group) : Nat :=
  (oddPrimes S).foldr (fun r acc => Nat.lcm (ordTwo r) acc) 1

theorem towerDegree_pos (S : Group) : 0 < towerDegree S := by
  unfold towerDegree
  induction oddPrimes S with
  | nil => norm_num
  | cons r l ih =>
    simp only [List.foldr_cons]
    have hr := ordTwo_pos r
    exact Nat.pos_of_ne_zero fun h => by
      rcases Nat.lcm_eq_zero_iff.mp h with h' | h' <;> omega

/-- A list-level version: `GF(2ᵏ)` realises the orders of all primes in a list iff the
corresponding lcm divides `k`. -/
theorem list_dvd_iff (L : List Nat) (hL : ∀ r ∈ L, 2 ≤ r ∧ IsOrderTwoMod r (ordTwo r)) (k : Nat) :
    (∀ r ∈ L, r ∣ 2 ^ k - 1) ↔ (L.foldr (fun r acc => Nat.lcm (ordTwo r) acc) 1) ∣ k := by
  induction L with
  | nil => simp
  | cons r l ih =>
    have hr := hL r (by simp)
    have hl : ∀ s ∈ l, 2 ≤ s ∧ IsOrderTwoMod s (ordTwo s) := fun s hs => hL s (by simp [hs])
    rw [List.foldr_cons, Nat.lcm_dvd_iff]
    constructor
    · intro h
      refine ⟨?_, (ih hl).mp fun s hs => h s (by simp [hs])⟩
      have := h r (by simp)
      rw [dvd_two_pow_sub_one_iff hr.1, two_pow_mod_eq_one_iff hr.1 hr.2] at this
      exact this
    · rintro ⟨h1, h2⟩ s hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · rw [dvd_two_pow_sub_one_iff hr.1, two_pow_mod_eq_one_iff hr.1 hr.2]
        exact h1
      · exact (ih hl).mpr h2 s hs'

theorem oddPrimes_spec (S : Group) :
    ∀ r ∈ oddPrimes S, 2 ≤ r ∧ IsOrderTwoMod r (ordTwo r) := by
  intro r hr
  have hmem : r ∈ S.primes := List.mem_of_mem_filter hr
  have hne : r ≠ 2 := by
    have := List.of_mem_filter hr
    simpa using this
  refine ⟨(Group.prime_of_mem_primes S r hmem).two_le, ?_⟩
  exact isOrderTwoMod_ordTwo r (Group.primes_subset_allPrimes S r hmem) hne

/-- The characteristic-two field `GF(2ᵏ)` has elements of every odd prime order dividing the
group order exactly when the tower degree of the group divides `k`. -/
theorem dvd_iff_towerDegree_dvd (S : Group) (k : Nat) :
    (∀ r ∈ S.primes, r ≠ 2 → r ∣ 2 ^ k - 1) ↔ towerDegree S ∣ k := by
  rw [towerDegree, ← list_dvd_iff (oddPrimes S) (oddPrimes_spec S) k]
  constructor
  · intro h r hr
    exact h r (List.mem_of_mem_filter hr) (by simpa using List.of_mem_filter hr)
  · intro h r hr hne
    exact h r (List.mem_filter.mpr ⟨hr, by simpa using hne⟩)

/-- The tower degree is the least positive degree that works. -/
theorem isLeast_towerDegree (S : Group) :
    IsLeast {k | 0 < k ∧ ∀ r ∈ S.primes, r ≠ 2 → r ∣ 2 ^ k - 1} (towerDegree S) := by
  constructor
  · exact ⟨towerDegree_pos S, (dvd_iff_towerDegree_dvd S _).mpr dvd_rfl⟩
  · rintro k ⟨hk, hks⟩
    exact Nat.le_of_dvd hk ((dvd_iff_towerDegree_dvd S k).mp hks)

/-- The 26 tower degrees. -/
theorem towerDegree_values :
    (Group.all.map towerDegree) =
      [20, 20, 180, 60, 12, 660, 60, 72, 660, 60, 24, 84, 60, 180, 660, 660, 60, 180, 1980, 180,
        1320, 660, 13860, 9240, 91080, 18489240] := by
  decide

/-! ## Inside the fields of the tower -/

/-- `2` is prime; needed to speak about `GF(2ᵏ)`. -/
local instance factPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- In the field `GF(2ᵏ)` with `towerDegree S ∣ k`, every odd prime dividing the order of `S`
occurs as the order of a unit. -/
theorem exists_unit_orderOf (S : Group) {k : Nat} (hk : 0 < k) (hdvd : towerDegree S ∣ k)
    {r : Nat} (hr : r ∈ S.primes) (hr2 : r ≠ 2) :
    ∃ x : (GaloisField 2 k)ˣ, orderOf x = r := by
  haveI : Fact (Nat.Prime r) := ⟨Group.prime_of_mem_primes S r hr⟩
  haveI : Fintype (GaloisField 2 k)ˣ := Fintype.ofFinite _
  have hunits : Nat.card (GaloisField 2 k)ˣ = 2 ^ k - 1 := by
    rw [Nat.card_units, GaloisField.card 2 k (by omega)]
  have hrdvd : r ∣ Fintype.card (GaloisField 2 k)ˣ := by
    rw [← Nat.card_eq_fintype_card, hunits]
    exact (dvd_iff_towerDegree_dvd S k).mpr hdvd r hr hr2
  exact exists_prime_orderOf_dvd_card r hrdvd

/-- Conversely, a floor of the tower realising all those orders has degree divisible by the tower
degree; in particular no smaller floor works. -/
theorem towerDegree_dvd_of_orders (S : Group) {k : Nat} (hk : 0 < k)
    (h : ∀ r ∈ S.primes, r ≠ 2 → ∃ x : (GaloisField 2 k)ˣ, orderOf x = r) :
    towerDegree S ∣ k := by
  refine (dvd_iff_towerDegree_dvd S k).mp fun r hr hr2 => ?_
  obtain ⟨x, hx⟩ := h r hr hr2
  have hd := orderOf_dvd_natCard x
  rw [hx, Nat.card_units, GaloisField.card 2 k (by omega)] at hd
  exact hd

/-- The path in the degree tree from the root down to the node of a sporadic group: the chain of
subfields of `GF(2^{towerDegree S})` that it passes through. -/
def treePath (S : Group) : List Nat := ExtensionTower.chain (towerDegree S)

theorem treePath_isChain_dvd (S : Group) : List.IsChain (· ∣ ·) (treePath S) :=
  ExtensionTower.chain_isChain_dvd _

theorem treePath_getLast (S : Group) :
    (treePath S).getLast (ExtensionTower.chain_ne_nil _) = towerDegree S :=
  ExtensionTower.chain_getLast (towerDegree_pos S)

theorem treePath_head (S : Group) : (treePath S).head? = some 1 :=
  ExtensionTower.chain_head _

end SporadicFieldDegree
