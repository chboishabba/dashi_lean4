import Mathlib
import RequestProject.CenterRetraction
import RequestProject.CenterRetractionMore

/-!
# Retractions onto the center of the (generalized) quaternion / dicyclic family

This file completes the picture for the second classical family of small groups, the
generalized quaternion (dicyclic) groups `QuaternionGroup n` of order `4 * n`.

The key structural observation is `exists_pow_eq_of_hasCenterRetraction`: if `r : G →* Z(G)`
is a retraction, then a central element which happens to be a `k`-th power in `G` is already
a `k`-th power *inside the center* (namely of `r g`).

In `QuaternionGroup n` with `n ≠ 1` every central element squares to `1`, while the central
element `a n` is the square of `xa 0`.  Hence for `n ≠ 0, 1` there is no retraction onto the
center.  Combined with the two degenerate cases (`n = 0`, where the group is the infinite
dicyclic group and is centerless, and `n = 1`, where it is cyclic of order `4`) this gives the
complete classification

`HasCenterRetraction (QuaternionGroup n) ↔ n < 2`.

Note that this genuinely goes beyond the nilpotent obstruction proved elsewhere in this
project: for instance `QuaternionGroup 3`, the dicyclic group of order `12`, is not nilpotent.
-/

open Subgroup

variable {G : Type*} [Group G]

/-- If `G` retracts onto its center, then every central element that is a `k`-th power in `G`
is a `k`-th power of a *central* element. -/
theorem exists_pow_eq_of_hasCenterRetraction (h : HasCenterRetraction G) {z g : G} {k : ℕ}
    (hz : z ∈ center G) (hzg : z = g ^ k) :
    ∃ w ∈ center G, z = w ^ k := by
  obtain ⟨r, hr⟩ := h
  refine ⟨((r g : center G) : G), (r g).2, ?_⟩
  have h1 : r z = ⟨z, hz⟩ := hr ⟨z, hz⟩
  have h2 : r z = r g ^ k := by rw [hzg, map_pow]
  have h3 : (⟨z, hz⟩ : center G) = r g ^ k := by rw [← h1, h2]
  have := congrArg (Subtype.val) h3
  simpa using this

namespace QuaternionGroup

variable {n : ℕ}

/-- The element `a n` is central in `QuaternionGroup n`. -/
theorem a_n_mem_center :
    (a (n : ZMod (2 * n)) : QuaternionGroup n) ∈ center (QuaternionGroup n) := by
  rw [mem_center_iff]
  rintro (i | j)
  · rw [a_mul_a, a_mul_a, add_comm]
  · rw [a_mul_xa, xa_mul_a]
    congr 1
    have h : ((2 * n : ℕ) : ZMod (2 * n)) = 0 := ZMod.natCast_self _
    push_cast at h
    linear_combination h

/-- For `n ≠ 0` the central element `a n` is not the identity. -/
theorem a_n_ne_one (hn : n ≠ 0) : (a (n : ZMod (2 * n)) : QuaternionGroup n) ≠ 1 := by
  intro h
  rw [one_def, a.injEq] at h
  have hz : ((n : ℕ) : ZMod (2 * n)) = 0 := h
  rw [ZMod.natCast_eq_zero_iff] at hz
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hz
  omega

/-- If `n ≠ 1`, no element of the form `xa j` is central in `QuaternionGroup n`. -/
theorem xa_not_mem_center (hn : n ≠ 1) (j : ZMod (2 * n)) :
    (xa j : QuaternionGroup n) ∉ center (QuaternionGroup n) := by
  intro hj
  have h := mem_center_iff.1 hj (a 1)
  rw [a_mul_xa, xa_mul_a] at h
  have h2 : (j - 1 : ZMod (2 * n)) = j + 1 := by simpa using h
  have h3 : (2 : ZMod (2 * n)) = 0 := by linear_combination -h2
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · revert h3
    show (2 : ZMod 0) ≠ 0
    exact two_ne_zero
  · have h4 : ((2 : ℕ) : ZMod (2 * n)) = 0 := by push_cast; exact h3
    rw [ZMod.natCast_eq_zero_iff] at h4
    have := Nat.le_of_dvd (by norm_num) h4
    omega

/-- If `n ≠ 1`, every central element of `QuaternionGroup n` squares to `1`. -/
theorem sq_eq_one_of_mem_center (hn : n ≠ 1) {x : QuaternionGroup n}
    (hx : x ∈ center (QuaternionGroup n)) : x ^ 2 = 1 := by
  rcases x with i | j
  · have h := mem_center_iff.1 hx (xa 0)
    rw [a_mul_xa, xa_mul_a] at h
    have h2 : (0 - i : ZMod (2 * n)) = 0 + i := by simpa using h.symm
    have h3 : i + i = 0 := by linear_combination -h2
    rw [sq, a_mul_a, h3, a_zero]
  · exact absurd hx (xa_not_mem_center hn j)

/-- **The dicyclic obstruction**: for `n ≠ 0, 1` the group `QuaternionGroup n` (of order `4n`)
does not retract onto its center.  Indeed the central element `a n` is the square of `xa 0`,
but no central element squares to it. -/
theorem not_hasCenterRetraction (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    ¬ HasCenterRetraction (QuaternionGroup n) := by
  intro h
  obtain ⟨w, hw, hwn⟩ :=
    exists_pow_eq_of_hasCenterRetraction (k := 2) h a_n_mem_center (xa_sq (n := n) 0).symm
  rw [sq_eq_one_of_mem_center hn1 hw] at hwn
  exact a_n_ne_one hn0 hwn

private theorem zmod_add_self_eq_zero_zero : ∀ i : ZMod (2 * 0), i + i = 0 → i = 0 := by
  show ∀ i : ZMod 0, i + i = 0 → i = 0
  intro i h
  have h2 : (2 : ZMod 0) * i = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · exact h3

/-- The infinite dicyclic group `QuaternionGroup 0` is centerless. -/
theorem center_eq_bot_zero : center (QuaternionGroup 0) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rcases x with i | j
  · have h := mem_center_iff.1 hx (xa 0)
    rw [a_mul_xa, xa_mul_a] at h
    have h2 : (0 - i : ZMod (2 * 0)) = 0 + i := by simpa using h.symm
    have h3 : i + i = 0 := by linear_combination -h2
    rw [zmod_add_self_eq_zero_zero i h3, a_zero]
  · exact absurd hx (xa_not_mem_center (by norm_num) j)

/-- `QuaternionGroup 0` (the infinite dicyclic group) retracts onto its center, trivially. -/
theorem hasCenterRetraction_zero : HasCenterRetraction (QuaternionGroup 0) :=
  hasCenterRetraction_of_center_eq_bot center_eq_bot_zero

/-- `QuaternionGroup 1` is cyclic of order `4`, hence abelian, hence retracts onto its center. -/
theorem hasCenterRetraction_one : HasCenterRetraction (QuaternionGroup 1) := by
  obtain ⟨g, hg⟩ := quaternionGroup_one_isCyclic.exists_generator
  refine hasCenterRetraction_of_commute ?_
  intro x y
  obtain ⟨m, rfl⟩ := hg x
  obtain ⟨k, rfl⟩ := hg y
  rw [← zpow_add, ← zpow_add, add_comm]

/-- **Complete classification for the quaternion / dicyclic family**: `QuaternionGroup n`
retracts onto its center if and only if `n < 2`, i.e. exactly in the two degenerate cases
`n = 0` (infinite dicyclic, centerless) and `n = 1` (cyclic of order `4`). -/
theorem hasCenterRetraction_quaternion_iff (n : ℕ) :
    HasCenterRetraction (QuaternionGroup n) ↔ n < 2 := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    exact not_hasCenterRetraction (by omega) (by omega) h
  · intro h
    interval_cases n
    · exact hasCenterRetraction_zero
    · exact hasCenterRetraction_one

/-- The dicyclic group of order `12` does not retract onto its center. -/
theorem not_hasCenterRetraction_dicyclic_twelve :
    ¬ HasCenterRetraction (QuaternionGroup 3) :=
  not_hasCenterRetraction (by norm_num) (by norm_num)

/-- `QuaternionGroup 3` has order `12`. -/
theorem card_quaternion_three : Fintype.card (QuaternionGroup 3) = 12 := by
  rw [QuaternionGroup.card]

section NotNilpotent

set_option maxRecDepth 100000

/-- The center of the dicyclic group of order `12` is `{1, a 3}`. -/
theorem mem_center_three_iff (x : QuaternionGroup 3) :
    x ∈ center (QuaternionGroup 3) ↔ (x = a 0 ∨ x = a 3) := by
  rw [mem_center_iff]
  revert x
  decide

/-- In the dicyclic group of order `12` the second term of the upper central series already
equals the first: an element whose commutators are all central is itself central. -/
theorem mem_center_three_of_commutators (x : QuaternionGroup 3)
    (hx : ∀ y : QuaternionGroup 3, x * y * x⁻¹ * y⁻¹ ∈ center (QuaternionGroup 3)) :
    x ∈ center (QuaternionGroup 3) := by
  simp only [mem_center_three_iff] at hx ⊢
  revert x
  decide

/-- The dicyclic group of order `12` is **not nilpotent**: its upper central series is stuck at
the center `{1, a 3}`, which is not everything.  Consequently
`not_hasCenterRetraction_dicyclic_twelve` is not an instance of the obstruction for nonabelian
nilpotent groups. -/
theorem not_isNilpotent_three : ¬ Group.IsNilpotent (QuaternionGroup 3) := by
  intro h
  obtain ⟨k, hk⟩ := h.nilpotent
  have key : ∀ m, upperCentralSeries (QuaternionGroup 3) m ≤ center (QuaternionGroup 3) := by
    intro m
    induction m with
    | zero => rw [upperCentralSeries_zero]; exact bot_le
    | succ m ih =>
      intro x hx
      rw [mem_upperCentralSeries_succ_iff] at hx
      exact mem_center_three_of_commutators x fun y => ih (hx y)
  have htop : (⊤ : Subgroup (QuaternionGroup 3)) ≤ center (QuaternionGroup 3) := hk ▸ key k
  have hmem : (xa 0 : QuaternionGroup 3) ∈ center (QuaternionGroup 3) :=
    htop (Subgroup.mem_top _)
  rw [mem_center_three_iff] at hmem
  revert hmem
  decide

end NotNilpotent

end QuaternionGroup
