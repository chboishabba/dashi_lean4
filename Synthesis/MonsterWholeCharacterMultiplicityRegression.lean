import Synthesis.MonsterWholeCharacterModuleAdapter
import Synthesis.MonsterCharacterDetermination

namespace Synthesis

open CategoryTheory

noncomputable section

universe u

variable {k G : Type u}
variable [Field k] [Group G] [Fintype G]
variable [Invertible (Fintype.card G : k)] [IsAlgClosed k]

example (V H : FDRep k G) [Simple H] (n : ℕ)
    (hchar : V.character = n • H.character) :
    (Module.finrank k (H ⟶ V) : k) = n :=
  cast_finrank_hom_eq_nat_of_character_eq_nsmul V H n hchar

example (V H U : FDRep k G) [Simple H] [Simple U] (n : ℕ)
    (hUH : ¬ Nonempty (U ≅ H))
    (hchar : V.character = n • H.character) :
    (Module.finrank k (U ⟶ V) : k) = 0 :=
  cast_finrank_hom_other_eq_zero_of_character_eq_nsmul V H U n hUH hchar

end

end Synthesis
