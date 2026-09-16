import Synthesis.MonsterWholeCharacterModuleAdapter

/-!
Regression surface for the next Monster whole-character adapter.

A `k[G]`-submodule of the canonical `V.ρ.asModule` carrier must map, through
`asModuleEquiv`, to a `k`-submodule of the original FDRep carrier that is stable
under every `V.ρ g`.  This is the exact bridge needed before module-level simple
submodules can be compared with FDRep character multiplicities.
-/

namespace Synthesis

open scoped MonoidAlgebra

noncomputable section

universe u

variable {k G : Type u}
variable [Field k] [Group G]

example (V : FDRep k G) (S : Submodule k[G] V.ρ.asModule) :
    let W : Submodule k V := S.map V.ρ.asModuleEquiv.toLinearMap
    ∀ g : G, W ≤ W.comap (V.ρ g) :=
  fdrep_asModule_submodule_stable V S

end

end Synthesis
