import Integration.E6F4ShortRootRecognition
import Integration.E6MinusculeWeightModule
import Integration.AlbertScalarTraceless
import Mathlib

/-!
# The finite W(F4) shadow of 27 = 1 + 26

The E6 minuscule 27 restricts under the folded Weyl action to 24 distinct F4
short-root weights plus three E6 weight lines whose folded weight is zero.  The
four folded generators act on those three zero-weight lines through the full S3
permutation image.  Hence their three-dimensional span splits canonically into
an invariant all-ones line and a two-dimensional sum-zero plane.

Together with the 24 short-root lines this gives the finite representation-level
shadow

  27 = 1 + (24 + 2) = 1 + 26.

This is precisely why the Albert unit should not be identified with any one E6
weight line: it is the invariant sum of the three folded-zero weight vectors.
The theorem still does not construct or preserve the Albert Jordan product or
cubic norm.
-/

namespace Integration.F4MinusculeOnePlus26

open Integration.E6Minuscule27LiteralRecognition
open Integration.E6Minuscule27SchlafliRecognition
open Integration.E6MinusculeWeightModule
open Integration.E6F4WeylFold
open Integration.E6F4ShortRootRecognition
open Integration.AlbertScalarTraceless

/-- Three explicit omega5 weights that restrict to folded weight zero. -/
def zeroWeight0 : Omega5Weight :=
  ⟨![1, 0, 0, 0, 0, -1], by native_decide⟩

def zeroWeight1 : Omega5Weight :=
  ⟨![-1, 0, 1, 0, -1, 1], by native_decide⟩

def zeroWeight2 : Omega5Weight :=
  ⟨![0, 0, -1, 0, 1, 0], by native_decide⟩

/-- They are exactly the three-element folded-zero orbit. -/
theorem explicit_zero_weights_are_folded_zero :
    zeroWeight0.1 ∈ foldedZero3 ∧ zeroWeight1.1 ∈ foldedZero3 ∧
      zeroWeight2.1 ∈ foldedZero3 := by
  native_decide

theorem explicit_zero_weights_pairwise_distinct :
    zeroWeight0 ≠ zeroWeight1 ∧ zeroWeight0 ≠ zeroWeight2 ∧
      zeroWeight1 ≠ zeroWeight2 := by
  native_decide

/-- Folded reflection on the finite omega5 carrier. -/
theorem foldOmega5_mem :
    ∀ g (w : Omega5Weight), foldReflect g w.1 ∈ minusculeOmega5Set := by
  native_decide

def foldOmega5 (g : FoldGenerator) (w : Omega5Weight) : Omega5Weight :=
  ⟨foldReflect g w.1, foldOmega5_mem g w⟩

@[simp] theorem foldOmega5_involutive :
    ∀ g w, foldOmega5 g (foldOmega5 g w) = w := by
  native_decide

/-- The folded action preserves membership in the three-weight zero orbit. -/
theorem fold_preserves_zero_membership :
    ∀ g (w : Omega5Weight),
      ((foldOmega5 g w).1 ∈ foldedZero3 ↔ w.1 ∈ foldedZero3) := by
  native_decide

/-- Reindex the minuscule coordinate module by the folded involution. -/
noncomputable def f4WeylLinearAction (g : FoldGenerator) :
    MinusculeModule ≃ₗ[ℝ] MinusculeModule where
  toFun f := fun w => f (foldOmega5 g w)
  invFun f := fun w => f (foldOmega5 g w)
  left_inv f := by
    funext w
    change f (foldOmega5 g (foldOmega5 g w)) = f w
    rw [foldOmega5_involutive]
  right_inv f := by
    funext w
    change f (foldOmega5 g (foldOmega5 g w)) = f w
    rw [foldOmega5_involutive]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Explicit action table on the three folded-zero weights. -/
def zeroIndexWeight : Fin 3 → Omega5Weight := ![zeroWeight0, zeroWeight1, zeroWeight2]

def zeroPerm : FoldGenerator → Fin 3 → Fin 3
  | .g1  => ![0,1,2]
  | .g3  => ![0,1,2]
  | .g05 => ![1,0,2]
  | .g24 => ![0,2,1]

theorem folded_action_on_zero3_matches_table :
    ∀ g i, foldOmega5 g (zeroIndexWeight i) = zeroIndexWeight (zeroPerm g i) := by
  native_decide

/-- The zero-weight permutation image is all S3 (six permutation tables). -/
abbrev Perm3Table := Fin 3 → Fin 3

def perm3Comp (p q : Perm3Table) : Perm3Table := fun i => p (q i)
def perm3Id : Perm3Table := fun i => i

def expandZeroPerms (S : Finset Perm3Table) : Finset Perm3Table :=
  S ∪ S.image (perm3Comp (zeroPerm .g1)) ∪
      S.image (perm3Comp (zeroPerm .g3)) ∪
      S.image (perm3Comp (zeroPerm .g05)) ∪
      S.image (perm3Comp (zeroPerm .g24))

def zeroPermOrbitN : Nat → Finset Perm3Table
  | 0 => {perm3Id}
  | n + 1 => expandZeroPerms (zeroPermOrbitN n)

def zeroPermutationImage : Finset Perm3Table := zeroPermOrbitN 3

theorem zero_permutation_image_card_6 : zeroPermutationImage.card = 6 := by
  native_decide

theorem zero_permutation_image_stable : zeroPermOrbitN 4 = zeroPermutationImage := by
  native_decide

/-- Coefficient sum on the three folded-zero coordinates. -/
noncomputable def foldedZeroTrace : MinusculeModule →ₗ[ℝ] ℝ where
  toFun f := f zeroWeight0 + f zeroWeight1 + f zeroWeight2
  map_add' f h := by simp; ring
  map_smul' r f := by simp; ring

/-- The finite-Weyl invariant unit candidate is the all-ones vector on the
three folded-zero coordinates and zero on the 24 short-root coordinates. -/
noncomputable def f4UnitCandidate : MinusculeModule :=
  fun w => if w.1 ∈ foldedZero3 then 1 else 0

theorem folded_zero_trace_unit : foldedZeroTrace f4UnitCandidate = 3 := by
  rcases explicit_zero_weights_are_folded_zero with ⟨h0,h1,h2⟩
  simp [foldedZeroTrace, f4UnitCandidate, h0, h1, h2]

/-- Rank-three-normalized trace/unit data on the canonical minuscule module. -/
noncomputable def f4TraceUnitData : TraceUnitData MinusculeModule where
  unit := f4UnitCandidate
  trace := foldedZeroTrace
  trace_unit := folded_zero_trace_unit

/-- Its canonical scalar/traceless split. -/
abbrev F4TracelessCandidate := Traceless f4TraceUnitData

/-- Exact dimension of the finite-Weyl traceless candidate. -/
theorem f4_traceless_candidate_finrank_26 :
    Module.finrank ℝ F4TracelessCandidate = 26 := by
  exact traceless_finrank_eq_26 f4TraceUnitData minuscule_module_finrank

/-- Folded generators fix the all-ones unit candidate. -/
theorem folded_action_fixes_unit :
    ∀ g, f4WeylLinearAction g f4UnitCandidate = f4UnitCandidate := by
  intro g
  funext w
  simp only [f4WeylLinearAction, LinearEquiv.coe_mk]
  unfold f4UnitCandidate
  rw [if_congr (fold_preserves_zero_membership g w) rfl rfl]

/-- The coefficient sum is invariant because the action permutes the three
folded-zero coordinates. -/
theorem folded_action_preserves_trace :
    ∀ g f, foldedZeroTrace (f4WeylLinearAction g f) = foldedZeroTrace f := by
  intro g f
  cases g
  · have h0 := folded_action_on_zero3_matches_table FoldGenerator.g1 0
    have h1 := folded_action_on_zero3_matches_table FoldGenerator.g1 1
    have h2 := folded_action_on_zero3_matches_table FoldGenerator.g1 2
    simp [foldedZeroTrace, f4WeylLinearAction, zeroPerm, zeroIndexWeight] at h0 h1 h2 ⊢
    rw [h0, h1, h2]
  · have h0 := folded_action_on_zero3_matches_table FoldGenerator.g3 0
    have h1 := folded_action_on_zero3_matches_table FoldGenerator.g3 1
    have h2 := folded_action_on_zero3_matches_table FoldGenerator.g3 2
    simp [foldedZeroTrace, f4WeylLinearAction, zeroPerm, zeroIndexWeight] at h0 h1 h2 ⊢
    rw [h0, h1, h2]
  · have h0 := folded_action_on_zero3_matches_table FoldGenerator.g05 0
    have h1 := folded_action_on_zero3_matches_table FoldGenerator.g05 1
    have h2 := folded_action_on_zero3_matches_table FoldGenerator.g05 2
    simp [foldedZeroTrace, f4WeylLinearAction, zeroPerm, zeroIndexWeight] at h0 h1 h2 ⊢
    rw [h0, h1, h2]
    ring
  · have h0 := folded_action_on_zero3_matches_table FoldGenerator.g24 0
    have h1 := folded_action_on_zero3_matches_table FoldGenerator.g24 1
    have h2 := folded_action_on_zero3_matches_table FoldGenerator.g24 2
    simp [foldedZeroTrace, f4WeylLinearAction, zeroPerm, zeroIndexWeight] at h0 h1 h2 ⊢
    rw [h0, h1, h2]
    ring

/-- Therefore every folded generator preserves the 26-dimensional trace-zero
carrier. -/
theorem folded_action_maps_traceless
    (g : FoldGenerator) (x : F4TracelessCandidate) :
    foldedZeroTrace (f4WeylLinearAction g x.1) = 0 := by
  rw [folded_action_preserves_trace]
  exact x.property

inductive FiniteOnePlus26CreatesAlbertProduct : Prop
inductive FiniteUnitCandidateIsAlreadyAlbertUnit : Prop

theorem finite_one_plus_26_does_not_create_albert_product :
    ¬ FiniteOnePlus26CreatesAlbertProduct := by
  intro h; cases h

theorem finite_unit_candidate_not_promoted_to_albert_unit :
    ¬ FiniteUnitCandidateIsAlreadyAlbertUnit := by
  intro h; cases h

structure Boundary where
  zeroWeightTripleExplicit : Bool
  zeroWeightPermutationImageS3Paid : Bool
  invariantAllOnesLinePaid : Bool
  traceKernelDimension26Paid : Bool
  foldedWeylPreservesTraceKernelPaid : Bool
  finiteRepresentationOnePlus26Paid : Bool
  actualAlbertProductCompatibilityPaidHere : Bool
  actualAlbertUnitIdentificationPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  zeroWeightTripleExplicit := true
  zeroWeightPermutationImageS3Paid := true
  invariantAllOnesLinePaid := true
  traceKernelDimension26Paid := true
  foldedWeylPreservesTraceKernelPaid := true
  finiteRepresentationOnePlus26Paid := true
  actualAlbertProductCompatibilityPaidHere := false
  actualAlbertUnitIdentificationPaidHere := false

end Integration.F4MinusculeOnePlus26
