/-!
# Exact 27-grid ↔ depth-three pants-path graph adapter (Agda golden)

Downstream mirror of
`DASHI.Combinatorics.GraphColouring369PantsGridAdjacencyExact`.
Uses existing `AgdaMirror.Base369.TriTruth` rather than making a new
ternary truth ontology.  This is a *finite nearest-neighbour* graph:
the low-to-high jump is forbidden, although low→mid→high is allowed.

The finite path is not a smooth pants surface; colouring transport
does not prove a minimum chromatic number.  Source-written only:
exact-head Lean kernel validation is still outstanding.

Vocabulary: Atiyah (1988) TQFT/cobordism; finite adapter owned by DASHI.
-/
import Mathlib
import AgdaMirror.Base369

namespace AgdaMirror.Reasoning.GraphColouring369PantsGridAdjacency

open AgdaMirror.Base369

inductive BranchSlot where
  | slot3 | slot6 | slot9
  deriving DecidableEq, Repr

def toSlot : TriTruth → BranchSlot
  | .low => .slot3
  | .mid => .slot6
  | .high => .slot9

def toTruth : BranchSlot → TriTruth
  | .slot3 => .low
  | .slot6 => .mid
  | .slot9 => .high

theorem truth_slot_roundtrip (x : TriTruth) :
    toTruth (toSlot x) = x := by cases x <;> rfl

theorem slot_truth_roundtrip (s : BranchSlot) :
    toSlot (toTruth s) = s := by cases s <;> rfl

inductive TritGridStep : TriTruth → TriTruth → Prop where
  | lowMid : TritGridStep .low .mid
  | midLow : TritGridStep .mid .low
  | midHigh : TritGridStep .mid .high
  | highMid : TritGridStep .high .mid

abbrev SlotGridStep (s t : BranchSlot) : Prop :=
  TritGridStep (toTruth s) (toTruth t)

theorem no_direct_low_high : ¬ TritGridStep .low .high := by
  intro h
  cases h

theorem trit_step_to_slot {x y : TriTruth}
    (h : TritGridStep x y) :
    SlotGridStep (toSlot x) (toSlot y) := by
  cases h <;> constructor

abbrev Voxel := TriTruth × TriTruth × TriTruth
abbrev PantsPath3 := BranchSlot × BranchSlot × BranchSlot

def voxelToPants : Voxel → PantsPath3
  | (x, y, z) => (toSlot x, toSlot y, toSlot z)

def pantsToVoxel : PantsPath3 → Voxel
  | (a, b, c) => (toTruth a, toTruth b, toTruth c)

theorem voxel_pants_roundtrip (v : Voxel) :
    pantsToVoxel (voxelToPants v) = v := by
  rcases v with ⟨x, y, z⟩
  cases x <;> cases y <;> cases z <;> rfl

theorem pants_voxel_roundtrip (p : PantsPath3) :
    voxelToPants (pantsToVoxel p) = p := by
  rcases p with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> rfl

inductive VoxelAdjacent : Voxel → Voxel → Prop where
  | x {a b c d : TriTruth} :
      TritGridStep a b → VoxelAdjacent (a,c,d) (b,c,d)
  | y {a b c d : TriTruth} :
      TritGridStep b c → VoxelAdjacent (a,b,d) (a,c,d)
  | z {a b c d : TriTruth} :
      TritGridStep c d → VoxelAdjacent (a,b,c) (a,b,d)

inductive PantsAdjacent : PantsPath3 → PantsPath3 → Prop where
  | x {a b c d : BranchSlot} :
      SlotGridStep a b → PantsAdjacent (a,c,d) (b,c,d)
  | y {a b c d : BranchSlot} :
      SlotGridStep b c → PantsAdjacent (a,b,d) (a,c,d)
  | z {a b c d : BranchSlot} :
      SlotGridStep c d → PantsAdjacent (a,b,c) (a,b,d)

theorem voxel_to_pants_preserves {v w : Voxel}
    (h : VoxelAdjacent v w) :
    PantsAdjacent (voxelToPants v) (voxelToPants w) := by
  cases h with
  | x step => exact PantsAdjacent.x (trit_step_to_slot step)
  | y step => exact PantsAdjacent.y (trit_step_to_slot step)
  | z step => exact PantsAdjacent.z (trit_step_to_slot step)

theorem pants_to_voxel_preserves {p q : PantsPath3}
    (h : PantsAdjacent p q) :
    VoxelAdjacent (pantsToVoxel p) (pantsToVoxel q) := by
  cases h with
  | x step => exact VoxelAdjacent.x step
  | y step => exact VoxelAdjacent.y step
  | z step => exact VoxelAdjacent.z step

def rotatePants : PantsPath3 → PantsPath3
  | (a,b,c) => (b,c,a)

theorem rotate_pants_order_three (p : PantsPath3) :
    rotatePants (rotatePants (rotatePants p)) = p := by
  rcases p with ⟨a,b,c⟩
  rfl

theorem rotate_pants_preserves {p q : PantsPath3}
    (h : PantsAdjacent p q) :
    PantsAdjacent (rotatePants p) (rotatePants q) := by
  cases h with
  | x step => exact PantsAdjacent.z step
  | y step => exact PantsAdjacent.x step
  | z step => exact PantsAdjacent.y step

def flipSlot : BranchSlot → BranchSlot
  | .slot3 => .slot9
  | .slot6 => .slot6
  | .slot9 => .slot3

theorem flip_slot_involutive (s : BranchSlot) :
    flipSlot (flipSlot s) = s := by
  cases s <;> rfl

theorem flip_slot_step {a b : BranchSlot}
    (h : SlotGridStep a b) :
    SlotGridStep (flipSlot a) (flipSlot b) := by
  cases a <;> cases b <;> cases h <;> constructor

def flipSecond : PantsPath3 → PantsPath3
  | (a,b,c) => (a,flipSlot b,c)

theorem flip_second_involutive (p : PantsPath3) :
    flipSecond (flipSecond p) = p := by
  rcases p with ⟨a,b,c⟩
  simp [flipSecond, flip_slot_involutive]

theorem flip_second_preserves {p q : PantsPath3}
    (h : PantsAdjacent p q) :
    PantsAdjacent (flipSecond p) (flipSecond q) := by
  cases h with
  | x step => exact PantsAdjacent.x step
  | y step => exact PantsAdjacent.y (flip_slot_step step)
  | z step => exact PantsAdjacent.z step

/-- Directed graph homomorphism, i.e. a proper-colouring pullback interface. -/
abbrev GraphHom {V W : Type}
    (adjV : V → V → Prop) (adjW : W → W → Prop)
    (f : V → W) : Prop :=
  ∀ ⦃u v : V⦄, adjV u v → adjW (f u) (f v)

theorem voxel_to_pants_graph_hom :
    GraphHom VoxelAdjacent PantsAdjacent voxelToPants := by
  intro u v h
  exact voxel_to_pants_preserves h

theorem pants_to_voxel_graph_hom :
    GraphHom PantsAdjacent VoxelAdjacent pantsToVoxel := by
  intro u v h
  exact pants_to_voxel_preserves h

theorem rotation_graph_hom :
    GraphHom PantsAdjacent PantsAdjacent rotatePants := by
  intro u v h
  exact rotate_pants_preserves h

theorem seam_flip_graph_hom :
    GraphHom PantsAdjacent PantsAdjacent flipSecond := by
  intro u v h
  exact flip_second_preserves h

/-- Pull an arbitrary palette colouring back along any pants graph endomorphism. -/
def recolourByFlip {Colour : Type} {different : Colour → Colour → Prop}
    (colouring : PantsPath3 → Colour)
    (proper : ∀ ⦃u v⦄, PantsAdjacent u v →
      different (colouring u) (colouring v)) :
    ∀ ⦃u v⦄, PantsAdjacent u v →
      different ((colouring ∘ flipSecond) u)
                ((colouring ∘ flipSecond) v) := by
  intro u v h
  exact proper (flip_second_preserves h)


/-- The six distinct permutations of the three labelled coordinates. -/
def swapXY : PantsPath3 → PantsPath3
  | (a,b,c) => (b,a,c)

theorem swap_xy_preserves {p q : PantsPath3}
    (h : PantsAdjacent p q) :
    PantsAdjacent (swapXY p) (swapXY q) := by
  cases h with
  | x step => exact PantsAdjacent.y step
  | y step => exact PantsAdjacent.x step
  | z step => exact PantsAdjacent.z step

inductive S3Code where
  | abc | bca | cab | bac | cba | acb
  deriving DecidableEq, Repr

def actS3 : S3Code → PantsPath3 → PantsPath3
  | .abc, p => p
  | .bca, p => rotatePants p
  | .cab, p => rotatePants (rotatePants p)
  | .bac, p => swapXY p
  | .cba, p => swapXY (rotatePants p)
  | .acb, p => swapXY (rotatePants (rotatePants p))

theorem act_s3_preserves (code : S3Code) {p q : PantsPath3}
    (h : PantsAdjacent p q) :
    PantsAdjacent (actS3 code p) (actS3 code q) := by
  cases code with
  | abc => exact h
  | bca => exact rotate_pants_preserves h
  | cab => exact rotate_pants_preserves (rotate_pants_preserves h)
  | bac => exact swap_xy_preserves h
  | cba => exact swap_xy_preserves (rotate_pants_preserves h)
  | acb => exact swap_xy_preserves (rotate_pants_preserves (rotate_pants_preserves h))

def distinctAnchor : PantsPath3 :=
  (.slot3,.slot6,.slot9)

theorem six_anchor_images_distinct (a b : S3Code) :
    actS3 a distinctAnchor = actS3 b distinctAnchor → a = b := by
  cases a <;> cases b <;> decide

end AgdaMirror.Reasoning.GraphColouring369PantsGridAdjacency
