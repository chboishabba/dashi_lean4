import Mathlib.RepresentationTheory.Character

/-!
# Monster character-determination donor

Small cross-prover theorem used by the DASHI Monster 3B Stone--von Neumann lane.

The mathematical input is mathlib's `FDRep.char_orthonormal`.  We do not
re-prove Maschke's theorem or Schur's lemma here.  For simple finite-dimensional
representations over an algebraically closed field, equality of characters
forces the `Nonempty (V ≅ W)` branch of character orthogonality.

This theorem is generic representation theory.  It does not identify any
particular Monster, extraspecial, zeta-sector, or Base369 carrier.
-/

namespace Synthesis

open CategoryTheory

noncomputable section

universe u

variable {k G : Type u}
variable [Field k] [Group G] [Fintype G]
variable [Invertible (Fintype.card G : k)] [IsAlgClosed k]

/-- Equal characters of simple finite-group representations force an
    equivariant isomorphism. -/
theorem nonempty_iso_of_character_eq
    (V W : FDRep k G) [Simple V] [Simple W]
    (hchar : V.character = W.character) :
    Nonempty (V ≅ W) := by
  classical
  by_contra hno
  have hVW := FDRep.char_orthonormal V W
  have hVV := FDRep.char_orthonormal V V
  rw [if_neg hno] at hVW
  have hself : Nonempty (V ≅ V) := ⟨Iso.refl V⟩
  rw [if_pos hself] at hVV
  rw [← hchar] at hVW
  exact one_ne_zero (hVV.symm.trans hVW)

end

end Synthesis
