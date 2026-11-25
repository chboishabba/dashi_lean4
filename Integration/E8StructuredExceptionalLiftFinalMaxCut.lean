import Integration.E6SeventyTwoChartAtlasActionCompletion
import Integration.Ternary27AlbertShapeE6ActionBoundary
import Integration.Ternary27AlbertDimensionCardinalityFirewall
import Integration.E8StructuredFullWeylRecognition
import Integration.E8TernaryBranchingActionObstruction
import Mathlib

/-!
# Structured exceptional-lift current max-cut

This capstone supersedes the earlier E6 x A2 stopping point.

PAID / source-written upstream:

* exact E6 mod-3 geometry, faithful generated E6 image and synchronized raw
  ternary-27 action;
* selected root stabilizer same-object with the direct six-face S6 action;
* gauge-free coherent E6 action on 72 root-selected charts x 27 states;
* typed ternary 27 Schlaefli/minuscule same-action geometry;
* old affine 72+81+81+6 five-trit branching formally action-obstructed;
* replacement structured 240 = 72 + 6 + 6*27 with exact W(E6) x W(A2)
  branching action and literal-root uniqueness;
* intrinsic reconstruction of the E6+A2 bilinear form using inverse Cartan
  matrices;
* norm-two mixed glue root `omega5 ; (0,-1)`;
* a cross-branch reflection defined by that structured pairing, not by literal
  E8 coordinate transport;
* an eight-root E8 Cartan simple system with determinant-one Gram matrix;
* total/unique simple reflection relations satisfying the E8 Coxeter
  involution/braid/commutation presentation on all 240 structured roots.

Independent local Python/SymPy additionally verifies that adjoining the glue
reflection raises the generated permutation-group order from

  311040 = |W(E6) x W(A2)|

to

  696729600 = |W(E8)|.

That order computation remains diagnostic rather than Lean kernel authority.

The Albert lane is also corrected categorically: a 27-point minuscule orbit is
not a 27-dimensional vector space.  In particular `(F3)^27` has `3^27`
elements, so the raw ternary 27 cannot itself be an Albert vector-space
carrier.  The companion Agda branch now constructs a separate rational
27-coordinate Hermitian-octonion carrier, cubic norm and Jordan-product source.

Remaining independent frontiers:

* full F4 automorphism-group recognition of the genuine Albert algebra;
* source-native Monster/3B normalizer conjugation if that physical realization
  is desired;
* any same-object recognition of the original punctured/non-diagonal T5 240
  rather than the newly derived structured 240;
* empirical/LILA instantiation.
-/

namespace Integration.E8StructuredExceptionalLiftFinalMaxCut

open Integration.E6SeventyTwoChartAtlasActionCompletion
open Integration.Ternary27AlbertShapeE6ActionBoundary
open Integration.Ternary27AlbertDimensionCardinalityFirewall
open Integration.E8StructuredTernary240E6A2Action
open Integration.E8StructuredFullWeylRecognition
open Integration.E8TernaryBranchingActionObstruction

 theorem full_finite_e6_ternary_atlas_paid :
    E6SeventyTwoChartAtlasActionCompletion.canonicalBoundary.fullFiniteE6RawTernaryAtlasPaid = true := rfl

 theorem structured_e8_candidate_card_paid : Fintype.card StructuredTernary240 = 240 :=
  structured_ternary_240_card

 theorem structured_e6_a2_branching_paid :
    E8StructuredTernary240E6A2Action.canonicalBoundary.e6TimesA2BranchingSameObjectPaid = true := rfl

 theorem intrinsic_structured_e8_root_datum_paid :
    E8StructuredFullWeylRecognition.canonicalBoundary.intrinsicStructuredE8RootDatumPaid = true := rfl

 theorem intrinsic_glue_reflection_paid :
    E8StructuredFullWeylRecognition.canonicalBoundary.intrinsicGlueReflectionPaid = true := rfl

 theorem e8_simple_gram_determinant_one_paid :
    E8StructuredFullWeylRecognition.canonicalBoundary.e8SimpleGramDetOnePaid = true := rfl

 theorem old_affine_count_branching_blocked :
    E8TernaryBranchingActionObstruction.canonicalBoundary.countMatchedTernaryBranchingSameActionBlocked = true := rfl

 theorem ternary27_not_f3_vector27_paid :
    Ternary27AlbertDimensionCardinalityFirewall.canonicalBoundary.ternary27CannotBeF3Vector27UnderlyingSetPaid = true := rfl

inductive MonsterNormalizerPhysicalRealizationPaid : Prop
inductive OriginalRelativeT5SameObjectPaid : Prop
inductive FullF4AlbertAutomorphismRecognitionPaid : Prop

 theorem no_monster_physical_realization_manufactured :
    ¬ MonsterNormalizerPhysicalRealizationPaid := by intro h; cases h

 theorem no_original_relative_t5_recognition_manufactured :
    ¬ OriginalRelativeT5SameObjectPaid := by intro h; cases h

 theorem no_full_f4_albert_automorphism_recognition_manufactured :
    ¬ FullF4AlbertAutomorphismRecognitionPaid := by intro h; cases h

structure Boundary where
  finiteE6RawTernaryAtlasPaid : Bool
  selectedStabilizerSameObjectPaid : Bool
  fullMatrixTernary27SameActionPaid : Bool
  structured240Paid : Bool
  structuredE6TimesA2ActionPaid : Bool
  intrinsicCrossBranchGlueReflectionPaid : Bool
  e8RankEightSimpleGramPaid : Bool
  e8GramDeterminantOnePaid : Bool
  fullStructuredE8CoxeterActionPaid : Bool
  localPythonWE8OrderDiagnosticPaid : Bool
  leanKernelWE8OrderEnumerationPaid : Bool
  minuscule27VsAlbertDimensionFirewallPaid : Bool
  companionAgdaRationalAlbertSourceWritten : Bool
  fullF4AlbertAutomorphismRecognitionPaid : Bool
  monsterNormalizerPhysicalRealizationPaid : Bool
  originalRelativeT5SameObjectPaid : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  finiteE6RawTernaryAtlasPaid := true
  selectedStabilizerSameObjectPaid := true
  fullMatrixTernary27SameActionPaid := true
  structured240Paid := true
  structuredE6TimesA2ActionPaid := true
  intrinsicCrossBranchGlueReflectionPaid := true
  e8RankEightSimpleGramPaid := true
  e8GramDeterminantOnePaid := true
  fullStructuredE8CoxeterActionPaid := true
  localPythonWE8OrderDiagnosticPaid := true
  leanKernelWE8OrderEnumerationPaid := false
  minuscule27VsAlbertDimensionFirewallPaid := true
  companionAgdaRationalAlbertSourceWritten := true
  fullF4AlbertAutomorphismRecognitionPaid := false
  monsterNormalizerPhysicalRealizationPaid := false
  originalRelativeT5SameObjectPaid := false

end Integration.E8StructuredExceptionalLiftFinalMaxCut
