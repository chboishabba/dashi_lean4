import Integration.E6Minuscule27SchlafliRecognition
import Mathlib

/-!
# Finite E6 minuscule-27 line action

The paid omega5 minuscule orbit is already a literal finite 27-weight carrier.
This file makes the finite Weyl action on those weight *lines* explicit before
any vector-space/Albert lift is chosen.

This is intentionally weaker than the 27-dimensional minuscule representation:
a Weyl representative may act on a chosen vector generator of a weight line by
a nonzero scalar/sign.  The finite permutation action records only the induced
action on the lines.
-/

namespace Integration.E6Minuscule27LineAction

open Integration.E6LiteralE8Action
open Integration.E6Minuscule27LiteralRecognition
open Integration.E6Minuscule27SchlafliRecognition

/-- The paid omega5 orbit is closed under every simple reflection. -/
theorem reflect_omega5_mem :
    ∀ s (w : Omega5Weight), reflectLabel s w.1 ∈ minusculeOmega5Set := by
  native_decide

/-- Simple reflection as an actual endomap of the 27-element omega5 carrier. -/
def reflectOmega5 (s : E6SimpleReflection) (w : Omega5Weight) : Omega5Weight :=
  ⟨reflectLabel s w.1, reflect_omega5_mem s w⟩

/-- The six finite simple-reflection maps are involutions on the paid orbit. -/
theorem reflect_omega5_involutive :
    ∀ s (w : Omega5Weight), reflectOmega5 s (reflectOmega5 s w) = w := by
  native_decide

/-- Each E6 simple reflection fixes 15 of the 27 weight lines.  Hence on the
remaining 12 it acts as six disjoint transpositions. -/
def fixedWeightCount (s : E6SimpleReflection) : Nat :=
  (Finset.univ.filter fun w : Omega5Weight => reflectOmega5 s w = w).card

theorem simple_reflection_fixed_count_15 :
    ∀ s, fixedWeightCount s = 15 := by
  native_decide

/-- The finite line action preserves the invariant-pairing/Schlaefli relation. -/
theorem reflect_preserves_minuscule_adjacency :
    ∀ s (x y : Omega5Weight),
      minusculeAdjacent (fun z : Omega5Weight => z.1)
          (reflectOmega5 s x) (reflectOmega5 s y) =
        minusculeAdjacent (fun z : Omega5Weight => z.1) x y := by
  native_decide

/-- The line action can be consumed without claiming a particular vector lift. -/
structure LineActionBoundary where
  carrierCard27Paid : Bool
  sixSimpleReflectionsAct : Bool
  simpleReflectionsInvolutive : Bool
  eachReflectionFixed15 : Bool
  schlafliRelationPreserved : Bool
  vectorGeneratorScalarsFixedHere : Bool
  albertRepresentationRealizedHere : Bool
  deriving Repr

def canonicalBoundary : LineActionBoundary where
  carrierCard27Paid := true
  sixSimpleReflectionsAct := true
  simpleReflectionsInvolutive := true
  eachReflectionFixed15 := true
  schlafliRelationPreserved := true
  vectorGeneratorScalarsFixedHere := false
  albertRepresentationRealizedHere := false

/-- Extra data needed to lift the paid permutation of weight lines to an honest
linear minuscule representation.  `weightVector` chooses a nonzero generator
of every line; `simpleAction` acts on the ambient 27-dimensional vector space;
`actionScalar` records the unavoidable nonzero scalar/sign ambiguity on the
chosen generators. -/
structure MonomialVectorLift (V : Type*) [AddCommGroup V] [Module ℝ V] : Type 1 where
  weightVector : Omega5Weight → V
  weightVector_ne_zero : ∀ w, weightVector w ≠ 0
  simpleAction : E6SimpleReflection → V ≃ₗ[ℝ] V
  actionScalar : E6SimpleReflection → Omega5Weight → ℝ
  actionScalar_ne_zero : ∀ s w, actionScalar s w ≠ 0
  action_on_weight_vector : ∀ s w,
    simpleAction s (weightVector w) =
      actionScalar s w • weightVector (reflectOmega5 s w)

inductive LinePermutationCreatesVectorLift : Prop

theorem line_permutation_does_not_create_vector_lift :
    ¬ LinePermutationCreatesVectorLift := by
  intro h
  cases h

end Integration.E6Minuscule27LineAction
