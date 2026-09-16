import Mathlib.RepresentationTheory.FDRep

/-!
# FDRep / group-algebra action adapter

Small execution seam for the Monster 3B whole-character probe.

For `V : FDRep k G`, mathlib exposes the unbundled action `V.ρ` and the
associated `k[G]`-module `V.ρ.asModule`.  The theorems below record the exact
same-object action equations needed before applying module-level isotypic APIs:
acting by `g` in the FDRep view is multiplication by the monoid-algebra basis
element `of k G g` in the module view, and every `k[G]`-submodule maps back to
a genuinely `G`-stable `k`-submodule of the original FDRep carrier.

These are only adapters.  They do not prove that a whole character identity
makes `V` isotypic, and they make no Monster-specific identification.
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

/-- A submodule over the group algebra becomes a `G`-stable linear subspace of
the original FDRep carrier under the canonical `asModuleEquiv`.

This is the missing direction needed to turn module-level simple/isotypic
subobjects into representation-side subspaces before comparing characters. -/
theorem fdrep_asModule_submodule_stable (V : FDRep k G)
    (S : Submodule k[G] V.ρ.asModule) :
    let W : Submodule k V := S.map V.ρ.asModuleEquiv.toLinearMap
    ∀ g : G, W ≤ W.comap (V.ρ g) := by
  dsimp
  intro g x hx
  rcases hx with ⟨y, hy, rfl⟩
  refine ⟨MonoidAlgebra.of k G g • y, S.smul_mem _ hy, ?_⟩
  have h :
      V.ρ.asModuleEquiv.symm
          (V.ρ g (V.ρ.asModuleEquiv y)) =
        MonoidAlgebra.of k G g • y := by
    simpa using fdrep_asModule_action_bridge V g (V.ρ.asModuleEquiv y)
  simpa using (congrArg V.ρ.asModuleEquiv h).symm

end

end Synthesis
