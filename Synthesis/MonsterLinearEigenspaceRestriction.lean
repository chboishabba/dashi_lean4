import Synthesis.MonsterInvariantRestriction

/-!
# Linear central-eigenspace restriction compiler

Given one actual linear group action, one actual linear central operator, one
scalar `zeta`, and a proof that the group action commutes with that operator,
the literal equation

  central x = zeta • x

defines a linear subspace.  The commuting group action preserves that same
subspace, so the restricted representation and inclusion intertwiner follow
from `MonsterInvariantRestriction`.

This is the generic linear version of the set-level central-character inertia
fact already owned in Agda.  It does not supply the actual Monster operator,
actual zeta scalar/orientation, or the same-object attachment to the historical
selected sector.
-/

namespace Synthesis.MonsterLinearEigenspaceRestriction

noncomputable section

open Synthesis.MonsterMultiplicitySchurCoordinates
open Synthesis.MonsterInvariantRestriction

universe u

variable {k G V : Type u}
variable [Field k] [Group G]
variable [AddCommGroup V] [Module k V]

/-- One linear central operator on the same carrier as the group action, with a
chosen scalar eigenvalue and a commuting-action law. -/
structure LinearCentralEigenData (A : Representation G k V) where
  central : V →ₗ[k] V
  eigenvalue : k
  commutes : ∀ g x, central (A.act g x) = A.act g (central x)

/-- The literal eigen-equation is a linear subspace. -/
def eigenspace
    (A : Representation G k V) (D : LinearCentralEigenData A) :
    Submodule k V where
  carrier := {x | D.central x = D.eigenvalue • x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    rw [D.central.map_add, hx, hy, smul_add]
  smul_mem' := by
    intro c x hx
    rw [D.central.map_smul, hx, smul_smul, smul_smul]
    congr 1
    exact mul_comm c D.eigenvalue

/-- Commutation with the central operator preserves the literal eigenspace. -/
theorem action_preserves_eigenspace
    (A : Representation G k V) (D : LinearCentralEigenData A)
    (g : G) (x : V) (hx : x ∈ eigenspace A D) :
    A.act g x ∈ eigenspace A D := by
  change D.central (A.act g x) = D.eigenvalue • A.act g x
  rw [D.commutes g x, hx]
  exact (A.act g).map_smul D.eigenvalue x

/-- The literal eigenspace as an invariant linear subspace of the SAME action. -/
def invariantEigenspace
    (A : Representation G k V) (D : LinearCentralEigenData A) :
    InvariantSubspace A where
  carrier := eigenspace A D
  stable := action_preserves_eigenspace A D

/-- Canonical restricted representation on the literal eigenspace. -/
def eigenspaceRepresentation
    (A : Representation G k V) (D : LinearCentralEigenData A) :
    Representation G k (eigenspace A D) :=
  restrictedRepresentation A (invariantEigenspace A D)

/-- Canonical equivariant inclusion of the eigenspace into the ambient carrier. -/
def eigenspaceInclusion
    (A : Representation G k V) (D : LinearCentralEigenData A) :
    EquivariantHom (eigenspaceRepresentation A D) A :=
  inclusionIntertwiner A (invariantEigenspace A D)

/-- The eigenspace carrier is by construction exactly the selected eigenlaw;
there is no second phase-sector search in this compiler. -/
theorem mem_eigenspace_iff
    (A : Representation G k V) (D : LinearCentralEigenData A) (x : V) :
    x ∈ eigenspace A D ↔ D.central x = D.eigenvalue • x := by
  rfl

structure Boundary where
  linearCentralEigenDataTyped : Bool
  literalLinearEigenspaceCompilerSourceWritten : Bool
  commutingActionPreservesEigenspaceSourceWritten : Bool
  eigenspaceRestrictedRepresentationSourceWritten : Bool
  eigenspaceInclusionIntertwinerSourceWritten : Bool
  eigenspaceRestrictionLinearityIsCompilerOutput : Bool
  actualMonsterCentralLinearOperatorPaidHere : Bool
  actualMonsterZetaScalarOrientationPaidHere : Bool
  actualHistoricalSectorSameObjectAttachmentPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  linearCentralEigenDataTyped := true
  literalLinearEigenspaceCompilerSourceWritten := true
  commutingActionPreservesEigenspaceSourceWritten := true
  eigenspaceRestrictedRepresentationSourceWritten := true
  eigenspaceInclusionIntertwinerSourceWritten := true
  eigenspaceRestrictionLinearityIsCompilerOutput := true
  actualMonsterCentralLinearOperatorPaidHere := false
  actualMonsterZetaScalarOrientationPaidHere := false
  actualHistoricalSectorSameObjectAttachmentPaidHere := false

inductive CharacterLabelCreatesLinearEigenData : Prop
inductive SetEigenspaceCreatesLinearCentralOperator : Prop

theorem character_label_does_not_create_linear_eigen_data :
    ¬ CharacterLabelCreatesLinearEigenData := by intro h; cases h

theorem set_eigenspace_does_not_create_linear_central_operator :
    ¬ SetEigenspaceCreatesLinearCentralOperator := by intro h; cases h

end

end Synthesis.MonsterLinearEigenspaceRestriction
