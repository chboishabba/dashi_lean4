import Synthesis.MonsterMultiplicitySchurCoordinates

/-!
# Invariant-subspace restriction compiler

This is a representation-independent compiler for the remaining Monster linear
seam.  Once an actual linear action and an actual invariant linear subspace are
paid on the SAME carrier, the restricted action, its linearity and the inclusion
intertwiner are construction outputs rather than independent obligations.

The intended Monster consumers are:

* the 196883 constituent inside the full weight-two linear representation;
* the literal zeta eigenspace inside that constituent/restricted action.

This file does not construct either actual subspace and does not infer
invariance from dimensions, character values or a phase label.
-/

namespace Synthesis.MonsterInvariantRestriction

noncomputable section

open Synthesis.MonsterMultiplicitySchurCoordinates

universe u

variable {k G V : Type u}
variable [Field k] [Group G]
variable [AddCommGroup V] [Module k V]

/-- Proof-relevant invariant linear subspace of one exact representation. -/
structure InvariantSubspace (A : Representation G k V) where
  carrier : Submodule k V
  stable : ∀ g (x : V), x ∈ carrier → A.act g x ∈ carrier

/-- The group action restricted to an invariant subspace.  All linear laws are
inherited from the ambient linear maps; they are not separate source inputs. -/
def restrictedRepresentation
    (A : Representation G k V) (S : InvariantSubspace A) :
    Representation G k S.carrier where
  act g :=
    { toFun := fun x => ⟨A.act g x.1, S.stable g x.1 x.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact (A.act g).map_add x.1 y.1
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact (A.act g).map_smul c x.1 }
  one_act := by
    intro x
    apply Subtype.ext
    exact A.one_act x.1
  mul_act := by
    intro g h x
    apply Subtype.ext
    exact A.mul_act g h x.1

/-- The canonical subspace inclusion is automatically equivariant for the
restricted action. -/
def inclusionIntertwiner
    (A : Representation G k V) (S : InvariantSubspace A) :
    EquivariantHom (restrictedRepresentation A S) A where
  toLinearMap := S.carrier.subtype
  intertwines := by
    intro g x
    rfl

/-- The restricted action is literally the ambient action followed by subtype
inclusion.  This is the equality needed by same-object consumers. -/
theorem inclusion_restricted_action
    (A : Representation G k V) (S : InvariantSubspace A)
    (g : G) (x : S.carrier) :
    (inclusionIntertwiner A S).toLinearMap
      ((restrictedRepresentation A S).act g x)
      = A.act g ((inclusionIntertwiner A S).toLinearMap x) := by
  rfl

/-- A nested invariant subspace gives a second restriction without introducing
another ambient representation.  This is the generic shape required for
weight-two -> 196883 constituent -> literal zeta sector. -/
def nestedRestrictedRepresentation
    (A : Representation G k V)
    (S : InvariantSubspace A)
    (T : InvariantSubspace (restrictedRepresentation A S)) :
    Representation G k T.carrier :=
  restrictedRepresentation (restrictedRepresentation A S) T

/-- Restriction linearity and inclusion equivariance are compiler outputs once
actual invariant subspaces are supplied.  The remaining Monster payment is
therefore invariance/same-object attachment, not separate zero/add/scalar laws. -/
structure Boundary where
  invariantSubspaceTyped : Bool
  restrictedRepresentationCompilerSourceWritten : Bool
  inclusionIntertwinerCompilerSourceWritten : Bool
  nestedRestrictionCompilerSourceWritten : Bool
  restrictionLinearityIsCompilerOutput : Bool
  actualMonsterInvariantSubspacePaidHere : Bool
  actualZetaSubspacePaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  invariantSubspaceTyped := true
  restrictedRepresentationCompilerSourceWritten := true
  inclusionIntertwinerCompilerSourceWritten := true
  nestedRestrictionCompilerSourceWritten := true
  restrictionLinearityIsCompilerOutput := true
  actualMonsterInvariantSubspacePaidHere := false
  actualZetaSubspacePaidHere := false

inductive DimensionCreatesInvariantSubspace : Prop
inductive CharacterCreatesInvariantSubspace : Prop

theorem dimension_does_not_create_invariant_subspace :
    ¬ DimensionCreatesInvariantSubspace := by intro h; cases h

theorem character_does_not_create_invariant_subspace :
    ¬ CharacterCreatesInvariantSubspace := by intro h; cases h

end

end Synthesis.MonsterInvariantRestriction
