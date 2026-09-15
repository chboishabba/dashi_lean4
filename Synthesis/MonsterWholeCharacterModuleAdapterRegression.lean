import Synthesis.MonsterWholeCharacterModuleAdapter

/-!
Regression surface for the FDRep -> group-algebra module action adapter used by
the Monster 3B whole-character/isotypic probe.
-/

namespace Synthesis

open scoped MonoidAlgebra

noncomputable section

universe u

variable {k G : Type u}
variable [Field k] [Group G]

example (V : FDRep k G) (g : G) (x : V) :
    V.ρ.asModuleEquiv.symm (V.ρ g x) =
      MonoidAlgebra.of k G g • V.ρ.asModuleEquiv.symm x :=
  fdrep_asModule_action_bridge V g x

end

end Synthesis
