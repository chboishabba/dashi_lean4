import Integration.E6SeventyTwoChartAtlasActionCompletion
import Integration.E8LiteralMixed27Fibres
import Integration.E6Minuscule27LiteralRecognition
import Mathlib

/-!
# Structured ternary 240 with the exact E6 x A2 branching action

The older five-trit `72+81+81+6` count partition is formally obstructed at the
action level.  The paid exceptional lift supplies the correct replacement:

  72 E6 roots + 6 A2 roots + 6 A2-weight tags * 27 E6-minuscule states.

This owner constructs that 240-state carrier directly from already recognized
pieces.  The raw ternary `Ternary27Point` is used as the 27-state fibre, with its
full E6 action.  The six mixed tags are the actual A2 weight pairs of the literal
E8 branching.  E6 acts on the Q2/27 coordinates and A2 acts on the A2 tags; the
two actions commute.

Exact finite uniqueness checks show that every tagged ternary-27 mixed state has
one and only one literal E8 mixed root with the same A2 weight and E6 Dynkin
label (using negative labels on the opposite minuscule triple).  Likewise every
A2-root tag has one and only one literal A2 root.  The 72-sector same-object map
was paid previously.  Hence the `E6 x A2` branching is now structurally welded.

This is deliberately weaker than a full W(E8) action: a generator outside the
E6 x A2 subgroup must mix the three branch types.  That cross-branch action is
not manufactured here.
-/

namespace Integration.E8StructuredTernary240E6A2Action

open Integration.E6Mod3QuadraticBridge
open Integration.E6Mod3WeylAction
open Integration.E6LiteralE8TernarySameObject
open Integration.E8LiteralE6A2Branching
open Integration.E8LiteralMixed27Fibres
open Integration.E6Minuscule27LiteralRecognition
open Integration.Ternary27HyperformSchlafliRecognition
open Integration.E6FullMatrixTernary27SameAction

inductive A2Simple
  | a | b
  deriving DecidableEq, Repr, Fintype

inductive A2RootTag
  | aPos | aNeg | bPos | bNeg | abPos | abNeg
  deriving DecidableEq, Repr, Fintype

inductive MixedWeightTag
  | plus0 | plus1 | plus2 | minus0 | minus1 | minus2
  deriving DecidableEq, Repr, Fintype

/-- Literal A2 weight pair attached to each mixed 27-fibre. -/
def mixedWeight : MixedWeightTag → Int × Int
  | .plus0 => (0,-4)
  | .plus1 => (4,0)
  | .plus2 => (-4,4)
  | .minus0 => (0,4)
  | .minus1 => (-4,0)
  | .minus2 => (4,-4)

/-- Literal A2 root weight pairs. -/
def a2RootWeight : A2RootTag → Int × Int
  | .aPos => (8,-4)
  | .aNeg => (-8,4)
  | .bPos => (-4,8)
  | .bNeg => (4,-8)
  | .abPos => (4,4)
  | .abNeg => (-4,-4)

/-- Weyl reflection formulas in A2 weight coordinates `(p,q)`. -/
def reflectA2Weight : A2Simple → (Int × Int) → Int × Int
  | .a, (p,q) => (-p,q+p)
  | .b, (p,q) => (p+q,-q)

/-- The six mixed weights and six roots are stable under both A2 reflections. -/
def actMixedTag : A2Simple → MixedWeightTag → MixedWeightTag
  | .a, .plus0 => .plus2
  | .a, .plus1 => .plus1
  | .a, .plus2 => .plus0
  | .a, .minus0 => .minus2
  | .a, .minus1 => .minus1
  | .a, .minus2 => .minus0
  | .b, .plus0 => .plus0
  | .b, .plus1 => .plus2
  | .b, .plus2 => .plus1
  | .b, .minus0 => .minus0
  | .b, .minus1 => .minus2
  | .b, .minus2 => .minus1


def actA2RootTag : A2Simple → A2RootTag → A2RootTag
  | .a, .aPos => .aNeg
  | .a, .aNeg => .aPos
  | .a, .bPos => .abPos
  | .a, .bNeg => .abNeg
  | .a, .abPos => .bPos
  | .a, .abNeg => .bNeg
  | .b, .aPos => .abPos
  | .b, .aNeg => .abNeg
  | .b, .bPos => .bNeg
  | .b, .bNeg => .bPos
  | .b, .abPos => .aPos
  | .b, .abNeg => .aNeg

 theorem mixed_tag_action_matches_weight_reflection :
    ∀ s t, mixedWeight (actMixedTag s t) = reflectA2Weight s (mixedWeight t) := by
  native_decide

 theorem a2_root_action_matches_weight_reflection :
    ∀ s t, a2RootWeight (actA2RootTag s t) = reflectA2Weight s (a2RootWeight t) := by
  native_decide

/-- Correct structured 240-state carrier. -/
def StructuredTernary240 :=
  QTwoShell ⊕ (A2RootTag ⊕ (MixedWeightTag × Ternary27Point))

instance : Fintype StructuredTernary240 := inferInstance

theorem structured_ternary_240_card : Fintype.card StructuredTernary240 = 240 := by
  native_decide

/-- E6 simple reflections: act on the 72 root sector and every 27 fibre, but
fix the A2 root/tag data. -/
def actE6 (s : E6SimpleReflection) : StructuredTernary240 → StructuredTernary240
  | .inl q => .inl ⟨reflectStandard s q.1, by
      rw [simple_reflections_preserve_quadratic s q.1, q.2]⟩
  | .inr (.inl a2) => .inr (.inl a2)
  | .inr (.inr (tag,p)) => .inr (.inr (tag, globalGeneratorActPoint s p))

/-- A2 simple reflections: fix E6 coordinates, act only on A2 roots/weight tags. -/
def actA2 (s : A2Simple) : StructuredTernary240 → StructuredTernary240
  | .inl q => .inl q
  | .inr (.inl r) => .inr (.inl (actA2RootTag s r))
  | .inr (.inr (tag,p)) => .inr (.inr (actMixedTag s tag,p))

/-- E6 and A2 actions commute literally on the structured branching carrier. -/
theorem e6_a2_actions_commute :
    ∀ e a x, actE6 e (actA2 a x) = actA2 a (actE6 e x) := by
  native_decide

/-- E6 Coxeter relations survive on the complete 240-state carrier. -/
theorem structured_e6_generators_involutive :
    ∀ s x, actE6 s (actE6 s x) = x := by native_decide

theorem structured_e6_adjacent_braid :
    ∀ i j, coxeterAdjacent i j = true → ∀ x,
      actE6 i (actE6 j (actE6 i x)) = actE6 j (actE6 i (actE6 j x)) := by
  native_decide

/-- A2 Coxeter relations (`S3`) on the complete carrier. -/
theorem structured_a2_generators_involutive :
    ∀ s x, actA2 s (actA2 s x) = x := by native_decide

theorem structured_a2_braid :
    ∀ x,
      actA2 .a (actA2 .b (actA2 .a x)) =
      actA2 .b (actA2 .a (actA2 .b x)) := by native_decide

/-! ## Literal-root uniqueness for the newly structured sectors -/

/-- Expected E6 Dynkin label on a mixed state.  The opposite triple carries the
opposite minuscule orbit. -/
def expectedMixedLabel (tag : MixedWeightTag) (p : Ternary27Point) : DynkinLabel :=
  match tag with
  | .plus0 | .plus1 | .plus2 => labelWeight (pointToLabel p)
  | .minus0 | .minus1 | .minus2 => fun i => -labelWeight (pointToLabel p) i

/-- Every structured mixed state names a unique literal E8 root by its two
independent coordinates: A2 weight and E6 Dynkin label. -/
theorem structured_mixed_has_unique_literal_root :
    ∀ tag p,
      ∃! r : E8ScaledRoot,
        a2Weight r = mixedWeight tag ∧ literalDynkinLabel r = expectedMixedLabel tag p := by
  native_decide

/-- Every structured A2 tag names a unique literal A2 root. -/
theorem structured_a2_tag_has_unique_literal_root :
    ∀ tag,
      ∃! r : E8ScaledRoot,
        a2Weight r = a2RootWeight tag ∧ isLiteralA2Sector r = true := by
  native_decide

/-- Converse mixed-sector coverage: every literal mixed root is uniquely
addressed by one tag and one raw ternary-27 state. -/
theorem literal_mixed_root_has_unique_structured_address :
    ∀ r : E8ScaledRoot,
      (isLiteralMixedPlus r = true ∨ isLiteralMixedMinus r = true) →
      ∃! tp : MixedWeightTag × Ternary27Point,
        a2Weight r = mixedWeight tp.1 ∧
        literalDynkinLabel r = expectedMixedLabel tp.1 tp.2 := by
  native_decide

/-- Converse A2-sector coverage. -/
theorem literal_a2_root_has_unique_structured_tag :
    ∀ r : E8ScaledRoot,
      isLiteralA2Sector r = true →
      ∃! tag : A2RootTag, a2Weight r = a2RootWeight tag := by
  native_decide

/-- The 72-sector remains the earlier concrete Q2 same-object theorem. -/
theorem e6_sector_same_object_already_paid :
    Nonempty (LiteralE6Sector ≃ QTwoShell) :=
  ⟨literalE6SectorEquivQTwoShell⟩

inductive CrossBranchWeylGeneratorPaid : Prop
inductive FullWE8StructuredTernaryActionPaid : Prop
inductive OriginalT5RelativeComplementIdentifiedHere : Prop

theorem subgroup_action_does_not_manufacture_cross_branch_generator :
    ¬ CrossBranchWeylGeneratorPaid := by intro h; cases h

theorem subgroup_action_does_not_manufacture_full_we8 :
    ¬ FullWE8StructuredTernaryActionPaid := by intro h; cases h

theorem derived_structured_240_does_not_identify_original_t5_cut :
    ¬ OriginalT5RelativeComplementIdentifiedHere := by intro h; cases h

structure Boundary where
  structuredCarrier240Paid : Bool
  e6Root72SameObjectConsumed : Bool
  a2Root6UniqueLiteralRecognitionPaid : Bool
  sixTernary27MixedFibresUniqueLiteralRecognitionPaid : Bool
  converseMixedCoveragePaid : Bool
  e6ActionOnStructured240Paid : Bool
  a2ActionOnStructured240Paid : Bool
  e6A2ActionsCommutePaid : Bool
  e6CoxeterOnStructured240Paid : Bool
  a2CoxeterOnStructured240Paid : Bool
  e6TimesA2BranchingSameObjectPaid : Bool
  crossBranchWeylGeneratorPaid : Bool
  fullWE8StructuredTernaryActionPaid : Bool
  originalT5RelativeComplementSameObjectPaid : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  structuredCarrier240Paid := true
  e6Root72SameObjectConsumed := true
  a2Root6UniqueLiteralRecognitionPaid := true
  sixTernary27MixedFibresUniqueLiteralRecognitionPaid := true
  converseMixedCoveragePaid := true
  e6ActionOnStructured240Paid := true
  a2ActionOnStructured240Paid := true
  e6A2ActionsCommutePaid := true
  e6CoxeterOnStructured240Paid := true
  a2CoxeterOnStructured240Paid := true
  e6TimesA2BranchingSameObjectPaid := true
  crossBranchWeylGeneratorPaid := false
  fullWE8StructuredTernaryActionPaid := false
  originalT5RelativeComplementSameObjectPaid := false

end Integration.E8StructuredTernary240E6A2Action
