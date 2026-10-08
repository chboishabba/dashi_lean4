import Integration.E6Minuscule27SchlafliRecognition
import Mathlib

/-!
# Same-object recognition of a literal mixed E8 fibre with the E6 minuscule 27

The earlier owners established independently that:

* `Plus0` has 27 literal E8 roots;
* its Dynkin-label image is exactly the 27-weight `omega5` E6 minuscule orbit;
* literal E6 reflections update those labels by the E6 Weyl reflection law;
* the invariant minuscule weight-pairing relation is exactly the literal
  Schlaefli relation.

This file packages those facts into an actual carrier equivalence rather than a
cardinality match.  The resulting object is an E6 minuscule weight-orbit
recognition of the literal mixed fibre.  It is deliberately not an Albert
Jordan-algebra recognition: no product, unit, determinant/cubic norm, or F4
automorphism structure is constructed here.
-/

namespace Integration.E6Minuscule27SameObject

open Integration.E6LiteralE8Action
open Integration.E8LiteralMixed27Fibres
open Integration.E8LiteralMixed27Schlafli
open Integration.E6Minuscule27LiteralRecognition
open Integration.E6Minuscule27SchlafliRecognition

/-- Every literal root in the canonical plus fibre has a label in the paid
omega5 minuscule orbit. -/
theorem plus0_label_in_omega5 :
    ∀ r : Plus0, literalDynkinLabel r.1 ∈ minusculeOmega5Set := by
  native_decide

/-- Literal-root to minuscule-weight map. -/
def plus0ToOmega5 (r : Plus0) : Omega5Weight :=
  ⟨literalDynkinLabel r.1, plus0_label_in_omega5 r⟩

/-- The label map is bijective, not merely image-surjective. -/
theorem plus0_to_omega5_bijective : Function.Bijective plus0ToOmega5 := by
  native_decide

/-- Concrete same-object equivalence between one literal E8 mixed fibre and the
E6 omega5 minuscule weight orbit. -/
noncomputable def plus0EquivOmega5 : Plus0 ≃ Omega5Weight :=
  Equiv.ofBijective plus0ToOmega5 plus0_to_omega5_bijective

/-- The equivalence is literally the pre-existing Dynkin-label map. -/
theorem plus0_equiv_label_spec :
    ∀ r : Plus0, (plus0EquivOmega5 r).1 = literalDynkinLabel r.1 := by
  intro r
  rfl

/-- Same-object relation preservation: Schlaefli adjacency is exactly the
invariant pairing-one relation after the concrete equivalence. -/
theorem plus0_equiv_preserves_schlafli :
    ∀ x y : Plus0,
      schlafliAdjacent x y =
        minusculeAdjacent (fun w : Omega5Weight => w.1)
          (plus0EquivOmega5 x) (plus0EquivOmega5 y) := by
  intro x y
  simpa [plus0EquivOmega5, plus0ToOmega5] using
    plus0_schlafli_iff_minuscule_pairing x y

/-- Reflection relation on the minuscule orbit, stated without manufacturing a
new total action function. -/
def Omega5ReflectionRel
    (s : E6SimpleReflection) (x y : Omega5Weight) : Prop :=
  y.1 = reflectLabel s x.1

/-- The concrete equivalence intertwines the independently defined literal E8
reflection relation with the E6 minuscule weight reflection relation. -/
theorem plus0_equiv_intertwines_reflection_relation :
    ∀ s (r t : Plus0),
      (∀ k, e8Coord t.1 k = literalReflectCoord s r.1 k) →
      Omega5ReflectionRel s (plus0EquivOmega5 r) (plus0EquivOmega5 t) := by
  intro s r t hreflect
  unfold Omega5ReflectionRel
  rw [plus0_equiv_label_spec, plus0_equiv_label_spec]
  exact literal_reflection_updates_dynkin_labels s r.1 t.1 hreflect

inductive MinusculeSameObjectCreatesAlbertJordanAlgebra : Prop
inductive MinusculeSameObjectIdentifiesBareTernaryCube : Prop

theorem minuscule_same_object_does_not_create_albert_algebra :
    ¬ MinusculeSameObjectCreatesAlbertJordanAlgebra := by
  intro h
  cases h

theorem minuscule_same_object_does_not_identify_bare_ternary_cube :
    ¬ MinusculeSameObjectIdentifiesBareTernaryCube := by
  intro h
  cases h

structure Boundary where
  literalPlusFibreToOmega5EquivalencePaid : Bool
  equivalenceUsesLiteralDynkinLabelMap : Bool
  schlafliRelationPreservedPaid : Bool
  reflectionRelationIntertwiningPaid : Bool
  e6Minuscule27SameObjectPaid : Bool
  albertJordanAlgebraPaid : Bool
  bareTernary27SameObjectPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  literalPlusFibreToOmega5EquivalencePaid := true
  equivalenceUsesLiteralDynkinLabelMap := true
  schlafliRelationPreservedPaid := true
  reflectionRelationIntertwiningPaid := true
  e6Minuscule27SameObjectPaid := true
  albertJordanAlgebraPaid := false
  bareTernary27SameObjectPaid := false

end Integration.E6Minuscule27SameObject
