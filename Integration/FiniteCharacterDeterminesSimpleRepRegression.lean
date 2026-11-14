import Integration.FiniteCharacterDeterminesSimpleRep
import Mathlib.RepresentationTheory.Character

namespace Integration.FiniteCharacterDeterminesSimpleRepRegression

open CategoryTheory

universe u v

variable {k : Type u} [Field k]
variable {G : Type v} [Group G] [Fintype G] [Invertible (Nat.card G : k)]

example (V W : FDRep k G) [Simple V] [Simple W]
    (hchar : V.character = W.character) : Nonempty (V ≅ W) :=
  Integration.FiniteCharacterDeterminesSimpleRep.isoOfEqualCharacters V W hchar

end Integration.FiniteCharacterDeterminesSimpleRepRegression
