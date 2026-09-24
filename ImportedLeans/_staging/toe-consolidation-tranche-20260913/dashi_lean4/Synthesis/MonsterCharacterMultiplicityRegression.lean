import Synthesis.MonsterCharacterDetermination

/-!
Regression surface for the two-simple character multiplicity compiler.

This file is intentionally a consumer of the generic donor.  It makes no
Monster-specific identification; it only checks that the donor exposes the
three multiplicity facts needed before isotypic-component assembly.
-/

namespace Synthesis

open CategoryTheory

noncomputable section

universe u

variable {k G : Type u}
variable [Field k] [Group G] [Fintype G]
variable [Invertible (Fintype.card G : k)] [IsAlgClosed k]

example
    (V T S : FDRep k G) [Simple T] [Simple S]
    (hTS : ¬ Nonempty (T ≅ S))
    (hchar : V.character = T.character + S.character) :
    (Module.finrank k (T ⟶ V) : k) = 1 :=
  cast_finrank_hom_left_eq_one_of_character_eq_add V T S hTS hchar

example
    (V T S : FDRep k G) [Simple T] [Simple S]
    (hTS : ¬ Nonempty (T ≅ S))
    (hchar : V.character = T.character + S.character) :
    (Module.finrank k (S ⟶ V) : k) = 1 :=
  cast_finrank_hom_right_eq_one_of_character_eq_add V T S hTS hchar

example
    (V T S U : FDRep k G) [Simple T] [Simple S] [Simple U]
    (hUT : ¬ Nonempty (U ≅ T))
    (hUS : ¬ Nonempty (U ≅ S))
    (hchar : V.character = T.character + S.character) :
    (Module.finrank k (U ⟶ V) : k) = 0 :=
  cast_finrank_hom_other_eq_zero_of_character_eq_add V T S U hUT hUS hchar

end

end Synthesis
