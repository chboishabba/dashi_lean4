/-
# The Ogg set: the affine grid, and two negative controls

The fifteen supersingular primes (Ogg's set) are

    {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71}.

Everything in this file is a finite decidable statement, checked by `decide` or
`norm_num`.  All interpretation is confined to these comments; no theorem name
claims more than the arithmetic it states.

## Positive content

* `Spine.Ogg.grid_subset` — the affine grid `(i, j) ↦ 5 + 12i + 42j` with
  `i < 3`, `j < 2` lands inside the Ogg set.  Stated as a grid predicate, not as
  a list of six equalities, so that it reads as an affine-geometry statement.
* `Spine.Ogg.grid_injective` — the six grid points are distinct.
* `Spine.Ogg.prod_row_one` — `47 · 59 · 71 = 196883`.

## Negative controls (the part that keeps this honest)

* `Spine.Ogg.translation_ne_pointed` — the vertical translation `p ↦ p + 42` is
  *not* the pointed-sign map `p ↦ 2p + 1` on the grid, so the two observers stay
  separated.
* `Spine.Ogg.mod_nine_not_uniform` — the mod-9 fibres of the Ogg set have sizes
  `(0,1,4,1,2,4,0,1,2)`, not five blocks of three.  So the nonary residue does
  not exhibit the Ogg set as `5 × 3`.
* `Spine.Ogg.cm_class_counts` — the discriminant `−7` splitting classification
  partitions the Ogg set as `5 + 9 + 1` (split / inert / ramified).
* `Spine.Ogg.no_free_order_three_cm_preserving` — **no fixed-point-free
  order-three permutation of the Ogg set preserves that classification**, because
  the ramified class is the singleton `{7}`.
* `Spine.Ogg.no_equivariant_labelling` — consequently there is no bijection from
  the internal `5 × 3` carrier `Fin 5 × Fin 3` (which *does* carry a free `C₃`
  action) onto the Ogg set intertwining that action with anything the CM observer
  can see.  Equal cardinality is not a map.

## Arithmetic identities kept deliberately inert

`196883 = 10 · 3⁹ + 53` and `53 = 5 · 9 + 8` are recorded as decidable arithmetic
(`Spine.Ogg.moonshine_nonary_decomposition`).  They carry no structural weight
here: nothing in this file acts on the pieces.
-/
import Mathlib

namespace Spine
namespace Ogg

/-- Ogg's set of supersingular primes. -/
def oggSet : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71}

theorem card_oggSet : oggSet.card = 15 := by decide

/-! ## The affine grid -/

/-- The affine grid map `(i, j) ↦ 5 + 12i + 42j`. -/
def gridMap (i j : ℕ) : ℕ := 5 + 12 * i + 42 * j

/-- The `3 × 2` affine grid lands inside the Ogg set. -/
theorem grid_subset : ∀ i < 3, ∀ j < 2, gridMap i j ∈ oggSet := by decide

/-- The six grid points are pairwise distinct. -/
theorem grid_injective : Function.Injective (fun x : Fin 3 × Fin 2 => gridMap x.1 x.2) := by
  decide

/-- The horizontal step is `+12` and the vertical step is `+42`. -/
theorem grid_steps (i j : ℕ) :
    gridMap (i + 1) j = gridMap i j + 12 ∧ gridMap i (j + 1) = gridMap i j + 42 := by
  constructor <;> simp [gridMap] <;> ring

/-- The second row multiplies to the first nontrivial moonshine dimension. -/
theorem prod_row_one : gridMap 0 1 * gridMap 1 1 * gridMap 2 1 = 196883 := by decide

/-- The two translations compose to `54`; this is the additive statement, and the
`C₃`-phase reading of it is not asserted here. -/
theorem steps_sum : 12 + 42 = 54 := by norm_num

/-! ## Negative control 1: translation is not the pointed-sign map -/

/-- On the first row, `p ↦ p + 42` and `p ↦ 2p + 1` disagree: the two observers
are different maps, so a coincidence of images may not be read as an
identification. -/
theorem translation_ne_pointed : ∀ i < 3, 2 * gridMap i 0 + 1 ≠ gridMap i 0 + 42 := by decide

/-- The pointed-sign preimage of `47` is `23`, which is in the Ogg set but is not
`5`: the two routes to `47` do not agree. -/
theorem pointed_preimage_47 : 2 * 23 + 1 = 47 ∧ (23 : ℕ) ∈ oggSet ∧ gridMap 0 0 = 5 := by decide

/-! ## Negative control 2: the nonary residue is not a `5 × 3` split -/

/-- Number of supersingular primes in a given residue class mod 9. -/
def modeCount (r : ℕ) : ℕ := (oggSet.filter (fun p => p % 9 = r)).card

/-- The nonary fibre sizes, computed. -/
theorem mode_counts :
    modeCount 0 = 0 ∧ modeCount 1 = 1 ∧ modeCount 2 = 4 ∧ modeCount 3 = 1 ∧ modeCount 4 = 2 ∧
      modeCount 5 = 4 ∧ modeCount 6 = 0 ∧ modeCount 7 = 1 ∧ modeCount 8 = 2 := by decide

/-- Hence the mod-9 observer does **not** cut the Ogg set into five blocks of
three: some fibre has size other than `0` or `3`. -/
theorem mod_nine_not_uniform : ¬ ∀ r < 9, modeCount r = 0 ∨ modeCount r = 3 := by decide

/-! ## Negative control 3: the CM observer and the `5 + 9 + 1` partition -/

/-- The splitting behaviour of `p` in `ℚ(√−7)`, read off the quadratic character
mod 7: `0` split, `1` inert, `2` ramified. -/
def cmClass (p : ℕ) : ℕ :=
  if p % 7 = 0 then 2 else if p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 then 0 else 1

/-- The CM observer partitions the Ogg set as `5 + 9 + 1`. -/
theorem cm_class_counts :
    (oggSet.filter (fun p => cmClass p = 0)).card = 5 ∧
      (oggSet.filter (fun p => cmClass p = 1)).card = 9 ∧
      (oggSet.filter (fun p => cmClass p = 2)).card = 1 := by decide

/-- The ramified class is the singleton `{7}`. -/
theorem cm_ramified_unique : ∀ p ∈ oggSet, cmClass p = 2 → p = 7 := by decide

theorem seven_mem : (7 : ℕ) ∈ oggSet := by decide

/-- **No free `C₃` action compatible with the CM observer.**  Any permutation of
the Ogg set that preserves the `ℚ(√−7)` splitting class must fix `7`, so it
cannot be fixed-point-free. -/
theorem no_free_order_three_cm_preserving
    (σ : ℕ → ℕ) (hmap : ∀ p ∈ oggSet, σ p ∈ oggSet)
    (hclass : ∀ p ∈ oggSet, cmClass (σ p) = cmClass p) :
    ¬ ∀ p ∈ oggSet, σ p ≠ p := by
  intro hfree
  have h7 : cmClass (σ 7) = 2 := by rw [hclass 7 seven_mem]; decide
  exact hfree 7 seven_mem (cm_ramified_unique _ (hmap 7 seven_mem) h7)

/-- The internal `5 × 3` carrier does have a free order-three action: shift the
ternary coordinate. -/
def internalShift (x : Fin 5 × Fin 3) : Fin 5 × Fin 3 := (x.1, x.2 + 1)

theorem internalShift_free (x : Fin 5 × Fin 3) : internalShift x ≠ x := by
  intro h
  have := congrArg Prod.snd h
  simp only [internalShift] at this
  revert this
  fin_cases x <;> decide

theorem internalShift_order_three (x : Fin 5 × Fin 3) :
    internalShift (internalShift (internalShift x)) = x := by
  simp only [internalShift]
  ext
  · rfl
  · have : x.2 + 1 + 1 + 1 = x.2 := by fin_cases x <;> decide
    simpa using congrArg Fin.val this

/-- **Equal cardinality is not a map.**  There is no bijection from the internal
`5 × 3` carrier onto the Ogg set that turns the free ternary shift into a
CM-class-preserving permutation.  The two fifteen-element sets are therefore not
canonically identified by this observer. -/
theorem no_equivariant_labelling (e : Fin 5 × Fin 3 ≃ {p : ℕ // p ∈ oggSet})
    (hclass : ∀ x, cmClass ((e (internalShift x)).1) = cmClass ((e x).1)) : False := by
  set σ : ℕ → ℕ := fun p =>
    if h : p ∈ oggSet then ((e (internalShift (e.symm ⟨p, h⟩))) : {p // p ∈ oggSet}).1 else p
    with hσ
  have hmap : ∀ p ∈ oggSet, σ p ∈ oggSet := by
    intro p hp; simp only [hσ, dif_pos hp]; exact (e (internalShift (e.symm ⟨p, hp⟩))).2
  have hcls : ∀ p ∈ oggSet, cmClass (σ p) = cmClass p := by
    intro p hp
    simp only [hσ, dif_pos hp]
    have := hclass (e.symm ⟨p, hp⟩)
    rw [this]
    simp
  refine no_free_order_three_cm_preserving σ hmap hcls ?_
  intro p hp hfix
  simp only [hσ, dif_pos hp] at hfix
  have hsub : e (internalShift (e.symm ⟨p, hp⟩)) = ⟨p, hp⟩ := Subtype.ext hfix
  have : internalShift (e.symm ⟨p, hp⟩) = e.symm ⟨p, hp⟩ := by
    have := congrArg e.symm hsub
    simpa using this
  exact internalShift_free _ this

/-! ## Inert arithmetic identities -/

/-- `196883 = 10 · 3⁹ + 53` and `53 = 5 · 9 + 8`.  Recorded as arithmetic; no
structure acts on the pieces here. -/
theorem moonshine_nonary_decomposition :
    (196883 : ℕ) = 10 * 3 ^ 9 + 53 ∧ (53 : ℕ) = 5 * 9 + 8 := by norm_num

end Ogg
end Spine
