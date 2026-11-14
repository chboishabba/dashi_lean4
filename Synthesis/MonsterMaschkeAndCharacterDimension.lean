import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Character

/-!
# Generic Maschke and character-at-identity tail

Once the actual restricted Monster sector is attached to a finite-dimensional
representation of a finite group over a characteristic-zero/algebraically closed
field, semisimplicity is library mathematics, not an extra Monster-specific
witness.  Likewise a same-object whole-character identity already contains the
corresponding dimension ratio by evaluation at the identity.

This owner records those two deductions at the scope used by the live Monster
3B route.  It does not manufacture the actual FDRep attachment or actual
whole-character identity.
-/

namespace Synthesis.MonsterMaschkeAndCharacterDimension

open CategoryTheory

noncomputable section

universe u

variable {k G : Type u}
variable [Field k] [CharZero k] [Group G] [Fintype G]
variable [NeZero (Nat.card G : k)]

/-- Maschke: every representation is semisimple under the nonmodular finite
field/group hypotheses. -/
theorem representationSemisimple {V : Type u}
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) :
    Representation.IsSemisimpleRepresentation ρ := by
  infer_instance

/-- A scalar whole-character identity forces the corresponding finrank identity
by evaluation at the group identity. -/
theorem finrankEqScalarOfCharacterEq
    (V H : FDRep k G) (a : k)
    (hchar : V.character = a • H.character) :
    (Module.finrank k V : k) = a * Module.finrank k H := by
  have h := congrFun hchar (1 : G)
  simpa [FDRep.char_one, Pi.smul_apply, smul_eq_mul] using h

/-- In the Monster consumer, the literal coefficient 90 in the SAME whole
character identity supplies the finrank ratio; no separate 65610/729 premise is
needed to recover the ratio in the coefficient field. -/
theorem finrankRatioNinetyOfCharacterEq
    (V H : FDRep k G)
    (hchar : V.character = (90 : k) • H.character) :
    (Module.finrank k V : k) = (90 : k) * Module.finrank k H :=
  finrankEqScalarOfCharacterEq V H 90 hchar

structure Boundary where
  maschkeSemisimplicityConsumed : Bool
  characterAtIdentityGivesDimensionConsumed : Bool
  ninetyCharacterCoefficientGivesDimensionRatio : Bool
  semisimplicityStillMonsterSpecificInput : Bool
  separateFinrankRatioStillIndependentInput : Bool
  actualMonsterFDRepAttachmentPaidHere : Bool
  actualMonsterWholeCharacterIdentityPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  maschkeSemisimplicityConsumed := true
  characterAtIdentityGivesDimensionConsumed := true
  ninetyCharacterCoefficientGivesDimensionRatio := true
  semisimplicityStillMonsterSpecificInput := false
  separateFinrankRatioStillIndependentInput := false
  actualMonsterFDRepAttachmentPaidHere := false
  actualMonsterWholeCharacterIdentityPaidHere := false

end

end Synthesis.MonsterMaschkeAndCharacterDimension
