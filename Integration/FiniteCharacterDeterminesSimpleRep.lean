import Mathlib.RepresentationTheory.Character
import Mathlib.CategoryTheory.Preadditive.Schur

/-!
# Equal characters determine simple finite-group representations

This is the exact lower-level theorem needed by the Monster-3B finite
Stone--von Neumann lane.  It deliberately avoids algebraic closure.

For simple finite-dimensional representations of a finite group over a field
in which the group order is invertible:

1. `FDRep.scalar_product_char_eq_finrank_equivariant` identifies the character
   scalar product with the dimension of the equivariant Hom space;
2. equal characters identify the cross scalar product with the self scalar
   product;
3. the self Hom is nonzero because it contains the identity;
4. hence the cross Hom is nonzero;
5. Schur's lemma turns any nonzero morphism between simple objects into an
   isomorphism.

The theorem does not choose a basis and does not identify any particular DASHI
Monster representation.  Those are separate same-object transport obligations.
-/

namespace Integration.FiniteCharacterDeterminesSimpleRep

open CategoryTheory
open Module

universe u v

variable {k : Type u} [Field k]
variable {G : Type v} [Group G] [Fintype G] [Invertible (Nat.card G : k)]

/-- Equal characters determine isomorphism for simple finite-dimensional
representations of a finite group whenever the group order is invertible in the
coefficient field.  No algebraic-closure hypothesis is used. -/
theorem isoOfEqualCharacters (V W : FDRep k G) [Simple V] [Simple W]
    (hchar : V.character = W.character) : Nonempty (V ≅ W) := by
  have hself : 0 < Module.finrank k (V ⟶ V) := by
    exact Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨𝟙 V, CategoryTheory.id_nonzero V⟩

  have hcrossEqSelf :
      Module.finrank k (V ⟶ W) = Module.finrank k (V ⟶ V) := by
    rw [← FDRep.scalar_product_char_eq_finrank_equivariant V W]
    rw [← FDRep.scalar_product_char_eq_finrank_equivariant V V]
    rw [← hchar]

  have hcross : 0 < Module.finrank k (V ⟶ W) := by
    rw [hcrossEqSelf]
    exact hself

  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hcross
  haveI : IsIso f := CategoryTheory.isIso_of_hom_simple hf
  exact ⟨asIso f⟩

structure Boundary where
  scalarProductHomFinrankTheoremConsumed : Bool
  selfIdentityWitnessConsumed : Bool
  nonzeroCrossHomDerived : Bool
  schurNonzeroSimpleMorphismConsumed : Bool
  algebraicClosureRequired : Bool
  monsterSameObjectTransportPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  scalarProductHomFinrankTheoremConsumed := true
  selfIdentityWitnessConsumed := true
  nonzeroCrossHomDerived := true
  schurNonzeroSimpleMorphismConsumed := true
  algebraicClosureRequired := false
  monsterSameObjectTransportPaidHere := false

end Integration.FiniteCharacterDeterminesSimpleRep
