import RequestProject.CenterRetraction
import RequestProject.CenterRetractionMore

/-!
# The general linear group `GL₂(R)` does not retract onto its center

All the negative examples obtained so far (`Q₈`, `D₄`, the dicyclic family, nonabelian nilpotent
groups) are finite.  This file gives an *infinite*, non-nilpotent family: for a commutative ring
`R` in which `2 ≠ 0`, the group `GL₂(R) = (Matrix (Fin 2) (Fin 2) R)ˣ` admits **no** retraction
onto its center.

The argument uses the elementwise form of the obstruction from `CenterRetractionMore.lean`:

* `not_hasCenterRetraction_of_mem_commutator_of_mem_center` : a group containing a nontrivial
  central element that is a commutator does not retract onto its center

together with the explicit identity `⁅rot, refl⁆ = -1` for the quarter turn
`rot = !![0,-1;1,0]` and the reflection `refl = !![1,0;0,-1]`, whose commutator is `-I`, a
nontrivial central element of `GL₂(R)`.

Instances: `GL₂(ℝ)` and `GL₂(ℚ)`.
-/

open Subgroup Matrix

/-- **Elementwise obstruction.**  If a group has a nontrivial central element that is also a
commutator, it does not retract onto its center. -/
theorem not_hasCenterRetraction_of_mem_commutator_of_mem_center {G : Type*} [Group G] {z : G}
    (hz1 : z ≠ 1) (hzc : z ∈ center G) (hzd : z ∈ commutator G) : ¬ HasCenterRetraction G := by
  rintro ⟨r, hr⟩
  have hd : commutator G ⊓ center G = ⊥ := disjoint_iff.1 (disjoint_commutator_center hr)
  have hz : z ∈ (⊥ : Subgroup G) := by
    rw [← hd]
    exact Subgroup.mem_inf.2 ⟨hzd, hzc⟩
  exact hz1 (by simpa using hz)

namespace GL2

variable (R : Type*) [CommRing R]

/-- The quarter turn `!![0,-1;1,0]`, an element of `GL₂(R)`. -/
def rot : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := !![0, -1; 1, 0]
  inv := !![0, 1; -1, 0]
  val_inv := by norm_num [Matrix.mul_fin_two, ← Matrix.one_fin_two]
  inv_val := by norm_num [Matrix.mul_fin_two, ← Matrix.one_fin_two]

/-- The reflection `!![1,0;0,-1]`, an element of `GL₂(R)`. -/
def refl : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := !![1, 0; 0, -1]
  inv := !![1, 0; 0, -1]
  val_inv := by norm_num [Matrix.mul_fin_two, ← Matrix.one_fin_two]
  inv_val := by norm_num [Matrix.mul_fin_two, ← Matrix.one_fin_two]

variable {R}

/-- `-1` (i.e. `-I`) is central in `GL₂(R)`. -/
theorem neg_one_mem_center : (-1 : (Matrix (Fin 2) (Fin 2) R)ˣ) ∈ center _ := by
  rw [mem_center_iff]
  intro g
  ext
  simp

/-- If `2 ≠ 0` in `R` then `-I ≠ I` in `GL₂(R)`. -/
theorem neg_one_ne_one (h2 : (2 : R) ≠ 0) : (-1 : (Matrix (Fin 2) (Fin 2) R)ˣ) ≠ 1 := by
  intro h
  have h' := congrArg (fun u : (Matrix (Fin 2) (Fin 2) R)ˣ =>
    (u : Matrix (Fin 2) (Fin 2) R) 0 0) h
  simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at h'
  exact h2 (by linear_combination -h')

/-- **The commutator of the quarter turn and the reflection is `-I`.** -/
theorem commutator_rot_refl : ⁅rot R, refl R⁆ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commutatorElement_def, rot, refl, Units.val_mul]

/-- **`GL₂(R)` does not retract onto its center** whenever `2 ≠ 0` in `R`: the central element
`-I` is the commutator of a quarter turn and a reflection. -/
theorem not_hasCenterRetraction (h2 : (2 : R) ≠ 0) :
    ¬ HasCenterRetraction (Matrix (Fin 2) (Fin 2) R)ˣ := by
  refine not_hasCenterRetraction_of_mem_commutator_of_mem_center (neg_one_ne_one h2)
    neg_one_mem_center ?_
  rw [← commutator_rot_refl]
  exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)

/-- `GL₂(ℝ)` does not retract onto its center. -/
theorem not_hasCenterRetraction_real :
    ¬ HasCenterRetraction (Matrix (Fin 2) (Fin 2) ℝ)ˣ :=
  not_hasCenterRetraction (by norm_num)

/-- `GL₂(ℚ)` does not retract onto its center. -/
theorem not_hasCenterRetraction_rat :
    ¬ HasCenterRetraction (Matrix (Fin 2) (Fin 2) ℚ)ˣ :=
  not_hasCenterRetraction (by norm_num)

/-- `GL₂(ℤ)` does not retract onto its center. -/
theorem not_hasCenterRetraction_int :
    ¬ HasCenterRetraction (Matrix (Fin 2) (Fin 2) ℤ)ˣ :=
  not_hasCenterRetraction (by norm_num)

/-- `GL₂(𝔽ₚ)` does not retract onto its center, for every odd prime `p`.  The obstruction is
the central involution `-I`, which is available precisely because `p` is odd. -/
theorem not_hasCenterRetraction_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ HasCenterRetraction (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ := by
  refine not_hasCenterRetraction (R := ZMod p) ?_
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hdvd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd)
  simpa using h2

end GL2
