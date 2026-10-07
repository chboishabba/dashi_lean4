import Integration.E6SeventyTwoChartAtlasActionCompletion
import Integration.Ternary27AlbertShapeE6ActionBoundary
import Integration.E8StructuredTernary240E6A2Action
import Integration.E8TernaryBranchingActionObstruction
import Mathlib

/-!
# Structured exceptional-lift final max-cut

This is the current fail-closed endpoint of the E6/ternary/E8 programme.

PAID / source-written upstream:

* exact E6 mod-3 F3^5 geometry and 1+80+90+72 strata;
* faithful generated E6 matrix image of order 51,840;
* selected root stabilizer same-object with the direct six-face S6 action;
* full 51,840 matrix <-> raw-ternary-27 permutation synchronized graph;
* E6 Coxeter coherence on the same raw ternary 27;
* gauge-free coherent E6 action on 72 root-selected charts x 27 states;
* exact raw ternary 27 Schlaefli/minuscule recognition;
* exact same-carrier origin+26 puncture, plus proof that it is not an E6-invariant
  representation splitting;
* the old affine 72+81+81+6 five-trit branching is action-obstructed;
* a replacement structured 240 = 72 + 6 + 6*27 carrier with commuting E6 and A2
  Coxeter actions and literal-root uniqueness on all six mixed 27 fibres and the
  six A2 roots.

Therefore the E6 x A2 branching is no longer an open recognition problem.

The remaining FULL-E8 datum is specifically a cross-branch Weyl/glue reflection
outside W(E6) x W(A2), together with its relations.  Such a reflection must mix
branch types, so it cannot be obtained from the old block-preserving action.
Deriving it intrinsically from the ternary/hyperfabric carrier is the next
mathematical promotion seam.

Separately, carrier-level 27=1+26 is NOT an Albert algebra.  Genuine Albert
recognition still requires unit/product/adjoint/cubic norm and compatible F4
automorphisms.  The current repository exceptional-algebra lane does not contain
those structures.
-/

namespace Integration.E8StructuredExceptionalLiftFinalMaxCut

open Integration.E6SeventyTwoChartAtlasActionCompletion
open Integration.Ternary27AlbertShapeE6ActionBoundary
open Integration.E8StructuredTernary240E6A2Action
open Integration.E8TernaryBranchingActionObstruction

/-- Finite E6/raw-ternary atlas is paid in the new gauge-free action-groupoid sense. -/
theorem full_finite_e6_ternary_atlas_paid :
    E6SeventyTwoChartAtlasActionCompletion.canonicalBoundary.fullFiniteE6RawTernaryAtlasPaid = true := rfl

/-- The replacement structured branching reaches exactly 240 states. -/
theorem structured_e8_candidate_card_paid : Fintype.card StructuredTernary240 = 240 :=
  structured_ternary_240_card

/-- Its maximal-rank E6 x A2 subgroup action is paid. -/
theorem structured_e6_a2_branching_paid :
    E8StructuredTernary240E6A2Action.canonicalBoundary.e6TimesA2BranchingSameObjectPaid = true := rfl

/-- The old 81+81 affine extension remains blocked and is not silently reused. -/
theorem old_affine_count_branching_blocked :
    E8TernaryBranchingActionObstruction.canonicalBoundary.countMatchedTernaryBranchingSameActionBlocked = true := rfl

/-- Same carrier has 1+26 anatomy, but this is explicitly not yet Jordan algebra structure. -/
theorem albert_shape_not_albert_algebra :
    Ternary27AlbertShapeE6ActionBoundary.canonicalBoundary.jordanProductPaid = false ∧
    Ternary27AlbertShapeE6ActionBoundary.canonicalBoundary.cubicNormPaid = false ∧
    Ternary27AlbertShapeE6ActionBoundary.canonicalBoundary.f4UnitStabilizerPaid = false := by
  decide

inductive IntrinsicCrossBranchE8GlueReflectionPaid : Prop
inductive AlbertJordanAlgebraPaid : Prop
inductive MonsterNormalizerPhysicalRealizationPaid : Prop
inductive OriginalRelativeT5SameObjectPaid : Prop

theorem no_intrinsic_cross_branch_glue_reflection_manufactured :
    ¬ IntrinsicCrossBranchE8GlueReflectionPaid := by intro h; cases h

theorem no_albert_algebra_manufactured : ¬ AlbertJordanAlgebraPaid := by intro h; cases h

theorem no_monster_physical_realization_manufactured :
    ¬ MonsterNormalizerPhysicalRealizationPaid := by intro h; cases h

theorem no_original_relative_t5_recognition_manufactured :
    ¬ OriginalRelativeT5SameObjectPaid := by intro h; cases h

structure Boundary where
  finiteE6RawTernaryAtlasPaid : Bool
  selectedStabilizerSameObjectPaid : Bool
  fullMatrixTernary27SameActionPaid : Bool
  typedTernary27SchlafliMinusculePaid : Bool
  sameCarrierOriginPlus26Paid : Bool
  originPlus26NotE6RepresentationSplitPaid : Bool
  oldAffine7281816Blocked : Bool
  structured240Paid : Bool
  structuredE6TimesA2ActionPaid : Bool
  allSixMixed27LiteralRecognitionPaid : Bool
  intrinsicCrossBranchE8GlueReflectionPaid : Bool
  fullWE8StructuredActionPaid : Bool
  albertJordanAlgebraPaid : Bool
  monsterNormalizerPhysicalRealizationPaid : Bool
  originalRelativeT5SameObjectPaid : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  finiteE6RawTernaryAtlasPaid := true
  selectedStabilizerSameObjectPaid := true
  fullMatrixTernary27SameActionPaid := true
  typedTernary27SchlafliMinusculePaid := true
  sameCarrierOriginPlus26Paid := true
  originPlus26NotE6RepresentationSplitPaid := true
  oldAffine7281816Blocked := true
  structured240Paid := true
  structuredE6TimesA2ActionPaid := true
  allSixMixed27LiteralRecognitionPaid := true
  intrinsicCrossBranchE8GlueReflectionPaid := false
  fullWE8StructuredActionPaid := false
  albertJordanAlgebraPaid := false
  monsterNormalizerPhysicalRealizationPaid := false
  originalRelativeT5SameObjectPaid := false

end Integration.E8StructuredExceptionalLiftFinalMaxCut
