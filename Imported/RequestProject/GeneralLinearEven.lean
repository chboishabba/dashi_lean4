import RequestProject.CenterRetraction
import RequestProject.GeneralLinearCenterRetraction
import RequestProject.CenterRetractionProd

/-!
# The `GL₂` obstruction in every even size

`GeneralLinearCenterRetraction.lean` proves that `GL₂(R)` has no retraction onto its center
when `2 ≠ 0` in `R`, because `-I` is the commutator of a quarter turn and a reflection, and
`GeneralLinearPositive.lean` shows that this fails in odd sizes (`GL₃(ℝ)` and `GL₃(𝔽₅)` do
retract).  Here the obstruction is carried to **every even size**: block-diagonal repetition

`M ↦ diag(M, …, M)`

is a homomorphism `GL₂(R) →* GL_{2m}(R)` carrying `-I₂` to `-I_{2m}`, so `-I` is again a
central commutator.

* `neg_one_mem_center_units` : `-1` is central in the unit group of any ring.
* `not_hasCenterRetraction_blockIndex` : no retraction for `GL` indexed by `Fin 2 × ι`.
* `not_hasCenterRetraction_even` : no retraction for `GL_{2m}(R)`, `m ≠ 0`, `2 ≠ 0` in `R`.
* `not_hasCenterRetraction_GL4_real`, `not_hasCenterRetraction_GL6_zmod_five` : samples.
-/

open Matrix Subgroup

namespace GLEven

/-- `-1` is central in the unit group of any ring. -/
theorem neg_one_mem_center_units (S : Type*) [Ring S] : (-1 : Sˣ) ∈ center Sˣ := by
  rw [mem_center_iff]
  intro u
  exact Units.ext (by simp)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- Block-diagonal repetition of a `2 × 2` matrix, as a monoid homomorphism. -/
def blockRepeat (ι : Type*) [Fintype ι] [DecidableEq ι] (R : Type*) [CommRing R] :
    Matrix (Fin 2) (Fin 2) R →* Matrix (Fin 2 × ι) (Fin 2 × ι) R where
  toFun M := Matrix.blockDiagonal fun _ : ι => M
  map_one' := Matrix.blockDiagonal_one
  map_mul' M N := Matrix.blockDiagonal_mul (fun _ => M) (fun _ => N)

/-- Block-diagonal repetition on units: `GL₂(R) →* GL_{Fin 2 × ι}(R)`. -/
def blockRepeatUnits (ι : Type*) [Fintype ι] [DecidableEq ι] (R : Type*) [CommRing R] :
    (Matrix (Fin 2) (Fin 2) R)ˣ →* (Matrix (Fin 2 × ι) (Fin 2 × ι) R)ˣ :=
  Units.map (blockRepeat ι R)

/-- Block-diagonal repetition carries `-I₂` to `-I`. -/
theorem blockRepeatUnits_neg_one :
    blockRepeatUnits ι R (-1) = -1 := by
  refine Units.ext ?_
  show Matrix.blockDiagonal (fun _ : ι => (-1 : Matrix (Fin 2) (Fin 2) R)) = -1
  have hconst : (fun _ : ι => (-1 : Matrix (Fin 2) (Fin 2) R))
      = -(1 : ι → Matrix (Fin 2) (Fin 2) R) := rfl
  rw [hconst, Matrix.blockDiagonal_neg, Matrix.blockDiagonal_one]

/-- If `2 ≠ 0` in `R` and the index type is nonempty, then `-I ≠ I`. -/
theorem neg_one_ne_one_units {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (h2 : (2 : R) ≠ 0) : (-1 : (Matrix n n R)ˣ) ≠ 1 := by
  intro h
  have hm : (-1 : Matrix n n R) = 1 := by simpa [Units.ext_iff] using h
  obtain ⟨i⟩ := ‹Nonempty n›
  have := congrArg (fun M : Matrix n n R => M i i) hm
  simp only [Matrix.neg_apply, Matrix.one_apply_eq] at this
  apply h2
  linear_combination -this

/-- **No retraction in size `2 × ι`.**  For any nonempty finite index type `ι` and any
commutative ring with `2 ≠ 0`, the group `GL_{Fin 2 × ι}(R)` has no retraction onto its
center. -/
theorem not_hasCenterRetraction_blockIndex [Nonempty ι] (h2 : (2 : R) ≠ 0) :
    ¬ HasCenterRetraction (Matrix (Fin 2 × ι) (Fin 2 × ι) R)ˣ := by
  refine not_hasCenterRetraction_of_mem_commutator_of_mem_center
    (z := (-1 : (Matrix (Fin 2 × ι) (Fin 2 × ι) R)ˣ)) (neg_one_ne_one_units h2)
    (neg_one_mem_center_units _) ?_
  have hcomm : ⁅blockRepeatUnits ι R (GL2.rot R), blockRepeatUnits ι R (GL2.refl R)⁆
      = (-1 : (Matrix (Fin 2 × ι) (Fin 2 × ι) R)ˣ) := by
    rw [← map_commutatorElement, GL2.commutator_rot_refl, blockRepeatUnits_neg_one]
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)

/-- The reindexing isomorphism `GL_{Fin 2 × Fin m}(R) ≃* GL_{Fin (2 * m)}(R)`. -/
noncomputable def reindexUnits (m : ℕ) (R : Type*) [CommRing R] :
    (Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) R)ˣ ≃* (Matrix (Fin (2 * m)) (Fin (2 * m)) R)ˣ :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R (finProdFinEquiv (m := 2) (n := m))).toMulEquiv

/-- **The `GL₂` obstruction holds in every even size**: for `m ≠ 0` and `2 ≠ 0` in `R`, the
group `GL_{2m}(R)` has no retraction onto its center. -/
theorem not_hasCenterRetraction_even {m : ℕ} (hm : m ≠ 0) (h2 : (2 : R) ≠ 0) :
    ¬ HasCenterRetraction (Matrix (Fin (2 * m)) (Fin (2 * m)) R)ˣ := by
  haveI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
  intro h
  exact not_hasCenterRetraction_blockIndex (ι := Fin m) h2
    (hasCenterRetraction_congr (reindexUnits m R).symm h)

/-- `GL₄(ℝ)` has no retraction onto its center. -/
theorem not_hasCenterRetraction_GL4_real :
    ¬ HasCenterRetraction (Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℝ)ˣ :=
  not_hasCenterRetraction_even (by norm_num) (by norm_num)

/-- `GL₆(𝔽₅)` has no retraction onto its center. -/
theorem not_hasCenterRetraction_GL6_zmod_five :
    ¬ HasCenterRetraction (Matrix (Fin (2 * 3)) (Fin (2 * 3)) (ZMod 5))ˣ :=
  not_hasCenterRetraction_even (by norm_num) (by decide)

end GLEven
