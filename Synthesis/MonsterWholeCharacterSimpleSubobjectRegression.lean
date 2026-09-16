import Synthesis.MonsterWholeCharacterSimpleSubobjectClassification

/-!
Regression surface for the whole-character simple-subobject bypass.

The desired theorem is deliberately narrower than a full isotypic decomposition:
if a simple representation `U` maps nontrivially into `V` and the whole character
of `V` is a nonzero scalar multiple of the simple character of `H`, then `U` must
be isomorphic to `H`.

This is generic finite-group representation theory only.  It does not identify
any Monster, zeta sector, extraspecial group, or concrete Weyl basis.
-/

namespace Synthesis

open CategoryTheory

noncomputable section

universe u

variable {k G : Type u}
variable [Field k] [CharZero k] [Group G] [Fintype G]
variable [Invertible (Fintype.card G : k)] [IsAlgClosed k]

example
    (V H U : FDRep k G) [Simple H] [Simple U]
    (a : k) (ha : a ≠ 0)
    (hchar : V.character = a • H.character)
    (f : U ⟶ V) (hf : f ≠ 0) :
    Nonempty (U ≅ H) :=
  simple_source_iso_of_nonzero_hom_and_character_eq_smul
    V H U a ha hchar f hf

end
end Synthesis
