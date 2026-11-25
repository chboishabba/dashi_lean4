import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RepresentationTheory.Irreducible

/-!
# Schur input from a simple finite-dimensional representation

The Monster multiplicity lane should not treat Schur's lemma as an independent
Monster datum once the actual `H_zeta` has been attached to Mathlib's same
finite-dimensional representation theory.

Mathlib already proves two forms needed by the downstream multiplicity compiler:

* `FDRep.simple_iff_end_is_rank_one`: a simple finite-dimensional
  representation of a finite group over an algebraically closed field has
  one-dimensional equivariant endomorphism space;
* `Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`:
  every self-intertwiner of an irreducible finite-dimensional representation is
  scalar.

This owner exposes those conclusions at the exact scope used by DASHI.  It does
not attach the literal Monster/Schrodinger carrier to an `FDRep`; that remains
the same-object representation payment.
-/

namespace Synthesis.MonsterSchurFromSimpleFDRep

open CategoryTheory

universe u

variable {k G : Type u}
variable [Field k] [IsAlgClosed k]
variable [Finite G] [Group G] [NeZero (Nat.card G : k)]

/-- Once an actual representation is already a simple `FDRep`, its equivariant
endomorphism space has rank one. -/
theorem simpleFDRep_end_finrank_one (V : FDRep k G) [Simple V] :
    Module.finrank k (V ⟶ V) = 1 :=
  (FDRep.simple_iff_end_is_rank_one V).mp inferInstance

section Representation

variable {V : Type u}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (ρ : Representation k G V)
variable [Representation.IsIrreducible ρ]

/-- Strong Schur form: the scalar algebra map onto self-intertwiners is
bijective.  Downstream coordinate packages may choose its inverse rather than
requesting a fresh Monster-specific scalar certificate. -/
theorem irreducible_self_intertwiners_are_scalars :
    Function.Bijective (algebraMap k (Representation.IntertwiningMap ρ ρ)) :=
  Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ) (f := 0)

end Representation

structure Boundary where
  mathlibSimpleEndRankOneConsumed : Bool
  irreducibleSelfIntertwinersScalarConsumed : Bool
  algebraicClosureRequiredForScalarSurjectivity : Bool
  schurIsMonsterSpecificInput : Bool
  actualMonsterFDRepAttachmentPaidHere : Bool
  actualMonsterIrreducibilityTransportPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  mathlibSimpleEndRankOneConsumed := true
  irreducibleSelfIntertwinersScalarConsumed := true
  algebraicClosureRequiredForScalarSurjectivity := true
  schurIsMonsterSpecificInput := false
  actualMonsterFDRepAttachmentPaidHere := false
  actualMonsterIrreducibilityTransportPaidHere := false

end Synthesis.MonsterSchurFromSimpleFDRep
