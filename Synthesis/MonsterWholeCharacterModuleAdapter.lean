import Mathlib.RepresentationTheory.FDRep

/-!
# FDRep / group-algebra action adapter

Small execution seam for the Monster 3B whole-character probe.

For `V : FDRep k G`, mathlib exposes the unbundled action `V.ρ` and the
associated `k[G]`-module `V.ρ.asModule`.  The theorem below records the exact
same-object action equation needed before applying module-level isotypic APIs:
acting by `g` in the FDRep view is multiplication by the monoid-algebra basis
element `of k G g` in the module view.

This is only an adapter.  It does not prove that a whole character identity
makes `V` isotypic, and it makes no Monster-specific identification.
-/

namespace Synthesis

open scoped MonoidAlgebra

noncomputable section

universe u

variable {k G : Type u}
variable [Field k] [Group G]

/-- The FDRep action and the associated group-algebra module action are the
same action under mathlib's canonical `asModuleEquiv`. -/
theorem fdrep_asModule_action_bridge (V : FDRep k G) (g : G) (x : V) :
    V.ρ.asModuleEquiv.symm (V.ρ g x) =
      MonoidAlgebra.of k G g • V.ρ.asModuleEquiv.symm x := by
  exact Representation.asModuleEquiv_symm_map_rho V.ρ g x

end

end Synthesis
