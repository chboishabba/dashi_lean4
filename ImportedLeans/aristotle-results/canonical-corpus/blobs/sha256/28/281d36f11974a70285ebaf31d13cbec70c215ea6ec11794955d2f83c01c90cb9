import RequestProject.Holograms
import RequestProject.Moonshine

/-!
# MonsterAddress: the 15-prime address → 194-irrep → q-expansion pipeline

This module makes the requested pipeline precise and proves the headline claim
("they will be in different locations").

Given a list of complex objects, each represented by an invariant
`h : ℕ` (e.g. a reflected declaration hash), the pipeline is:

1. **15-d address (all prime residuals).** The Monster order `|𝕄|` is divisible
   by exactly fifteen primes
   `2,3,5,7,11,13,17,19,23,29,31,41,47,59,71`.  The address of `h` is the
   15-tuple of its residues modulo each of these primes,
   `addr h i = h % pᵢ`.

2. **Move into each of the 194 Monster irreps.** The Monster has `194`
   irreducible representations.  Object `h` is spread across all of them: in
   irrep `i` its multiplicity `mult h i` is the prime-residue channel
   `addr h (i mod 15)`.

3. **Select / expand by the first 104 q-coefficients.** Klein's `j`-invariant has
   the q-expansion `q⁻¹ + 744 + 196884 q + …` (computed in `Moonshine`).  The
   first `104` coefficients `qexp k = jCoeff (k+1)` weight the irrep multiplicities.
   `selectedIrreps` records the subset of irreps that the first 104 coefficients
   pick out (via their residues mod 194).

4. **Assemble ("add the samples together").** The location of `h` is the
   assembled moonshine-lattice point
   `embed h : Fin 194 → Fin 104 → ℤ`, `embed h i k = (mult h i) * (qexp k)`.

## Main results

* `addr_inj` — the 15-prime address is **injective** on `[0, radical)` where
  `radical = 2·3·…·71`.  This is the Chinese Remainder Theorem: distinct objects
  (below the radical) have distinct addresses, i.e. *different locations* already
  at stage 1.
* `location_inj` — the full assembled embedding `embed` is injective on
  `[0, radical)`: distinct objects land at distinct points of the moonshine
  lattice.  This is the precise form of "they will be in different locations".
* `objects_locations_distinct` — a concrete sample list of objects is verified to
  occupy pairwise-distinct locations.
-/

namespace MonsterAddress

open Moonshine

/-! ## Stage 1: the 15-prime address -/

/-- The fifteen prime divisors of `|𝕄|`, in ascending order. -/
def mprimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

/-- The `i`-th Monster prime (`i : Fin 15`). -/
def mprime (i : Fin 15) : ℕ := mprimes.getD i.val 1

/-- The radical of `|𝕄|`: the product of its fifteen prime divisors. -/
def radical : ℕ := 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71

/-- Each Monster prime is genuinely prime. -/
theorem mprime_prime (i : Fin 15) : Nat.Prime (mprime i) := by
  fin_cases i <;> decide

/-- Each Monster prime divides the Monster order. -/
theorem mprime_dvd_order (i : Fin 15) : mprime i ∣ Holograms.monsterOrder := by
  fin_cases i <;> native_decide

/-- The 15-dimensional address of `h`: its residues modulo each Monster prime. -/
def addr (h : ℕ) (i : Fin 15) : ℕ := h % mprime i

/-- A scalar fingerprint of the address (the list of all prime residuals). -/
def fingerprint (h : ℕ) : List ℕ := (List.finRange 15).map (fun i => addr h i)

/-
**Chinese Remainder Theorem for the Monster primes.** If `h` and `h'` agree
modulo every one of the fifteen Monster primes, they agree modulo the radical.
-/
theorem modEq_radical {h h' : ℕ}
    (H : ∀ i : Fin 15, h ≡ h' [MOD mprime i]) : h ≡ h' [MOD radical] := by
  rw [ Nat.modEq_iff_dvd ];
  convert Finset.lcm_dvd fun i ( hi : i ∈ Finset.univ ) => Nat.modEq_iff_dvd.mp ( H i ) using 1

/-
**Stage-1 separation (different addresses).** The 15-prime address is
injective on `[0, radical)`: two objects below the radical with the same address
are equal.
-/
theorem addr_inj {h h' : ℕ} (hh : h < radical) (hh' : h' < radical)
    (he : ∀ i : Fin 15, addr h i = addr h' i) : h = h' := by
  -- By the Chinese Remainder Theorem, since h ≡ h' [MOD mprime i] for all i : Fin 15, we have h ≡ h' [MOD radical].
  have h_mod_radical : h ≡ h' [MOD radical] := by
    exact modEq_radical fun i => he i;
  exact Nat.mod_eq_of_lt hh ▸ Nat.mod_eq_of_lt hh' ▸ h_mod_radical

/-! ## Stage 2: move into each of the 194 irreps -/

/-- The multiplicity of object `h` in irrep `i`: its prime-residue channel
`addr h (i mod 15)`, spreading the 15-d address across all 194 irreps. -/
def mult (h : ℕ) (i : Fin 194) : ℕ := addr h ⟨i.val % 15, Nat.mod_lt _ (by decide)⟩

/-! ## Stage 3: the first 104 q-expansion coefficients -/

/-- The first 104 q-expansion coefficients of `j` (`qexp k = [qᵏ] j`,
i.e. `744, 196884, 21493760, …`). -/
def qexp (k : Fin 104) : ℤ := Moonshine.jCoeff (k.val + 1)

/-- The leading q-coefficient `qexp 0 = 744` is nonzero. -/
theorem qexp_zero : qexp ⟨0, by decide⟩ = 744 := by native_decide

/-- The subset of the 194 irreps selected by the first 104 q-coefficients
(through their residues modulo 194). -/
def selectedIrreps : List (Fin 194) :=
  (List.finRange 194).filter
    (fun i => decide (i.val ∈
      (List.range 104).map (fun k => ((Moonshine.jCoeff (k + 1)).emod 194).toNat)))

/-- The q-expansion selects a nonempty set of irreps. -/
theorem selectedIrreps_nonempty : selectedIrreps ≠ [] := by native_decide

/-! ## Stage 4: assemble the samples ("add them together") -/

/-- The location of object `h`: the assembled moonshine-lattice point, with the
`(i,k)` coordinate the irrep-`i` multiplicity weighted by the `k`-th q-coefficient. -/
def embed (h : ℕ) (i : Fin 194) (k : Fin 104) : ℤ := (mult h i : ℤ) * qexp k

/-
**Headline separation theorem (different locations).** The assembled
embedding is injective on `[0, radical)`: distinct objects below the radical land
at distinct points of the moonshine lattice.
-/
theorem location_inj {h h' : ℕ} (hh : h < radical) (hh' : h' < radical)
    (he : embed h = embed h') : h = h' := by
  apply addr_inj hh hh';
  intro i; have := congrFun ( congrFun he ( ⟨ i.val, by fin_cases i <;> trivial ⟩ : Fin 194 ) ) ⟨ 0, by decide ⟩ ; simp_all +decide [ embed, mult, addr ] ;
  fin_cases i <;> exact mod_cast this.resolve_right ( by native_decide )

/-! ## A concrete list of complex objects -/

/-- A sample list of "complex objects" (each given by an invariant `h : ℕ`). -/
def objects : List ℕ :=
  [17, 42, 196884, 1000003, 271828, 314159, 161803, 999999937]

/-- Every sample object lies below the radical. -/
theorem objects_lt_radical : ∀ h ∈ objects, h < radical := by native_decide

/-- The sample objects have pairwise-distinct 15-prime addresses. -/
theorem objects_fingerprints_nodup : (objects.map fingerprint).Nodup := by native_decide

/-- **The sample objects occupy pairwise-distinct locations.** -/
theorem objects_locations_distinct :
    ∀ x ∈ objects, ∀ y ∈ objects, embed x = embed y → x = y := by
  intro x hx y hy he
  exact location_inj (objects_lt_radical x hx) (objects_lt_radical y hy) he

end MonsterAddress