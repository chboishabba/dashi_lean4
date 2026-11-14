import Mathlib.RepresentationTheory.FDRep

/-!
# Live FDRep / group-algebra adapter

Promoted from the earlier DASHI `agent/monster3b-fdrep-groupalgebra-adapter`
branch onto the current #47 representation tail.

For `V : FDRep k G`, mathlib's unbundled action `V.ρ` and its canonical
`k[G]`-module `V.ρ.asModule` are the SAME action under `asModuleEquiv`.
Moreover every group-algebra submodule transports back to a genuinely
G-stable k-linear subspace of the original FDRep carrier.

This retires the FDRep/module representation-ontology seam as a research leaf.
It does not attach the actual Monster W_zeta sector to an FDRep and does not
prove its whole-character identity.
-/

namespace Synthesis.MonsterWholeCharacterModuleAdapterLive

open scoped MonoidAlgebra

noncomputable section

universe u

variable {k G : Type u}
variable [Field k] [Group G]

/-- The FDRep and group-algebra module actions agree under the canonical carrier
linear equivalence. -/
theorem fdrepAsModuleActionBridge (V : FDRep k G) (g : G) (x : V) :
    V.ρ.asModuleEquiv.symm (V.ρ g x) =
      MonoidAlgebra.of k G g • V.ρ.asModuleEquiv.symm x := by
  exact Representation.asModuleEquiv_symm_map_rho V.ρ g x

/-- Every k[G]-submodule gives a genuinely G-stable linear subspace of the same
FDRep carrier. -/
theorem fdrepAsModuleSubmoduleStable (V : FDRep k G)
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
    simpa using fdrepAsModuleActionBridge V g (V.ρ.asModuleEquiv y)
  simpa using (congrArg V.ρ.asModuleEquiv h).symm

structure Boundary where
  fdrepModuleActionBridgeSourceWritten : Bool
  groupAlgebraSubmoduleStabilitySourceWritten : Bool
  fdrepModuleAdapterStillResearchLeaf : Bool
  actualMonsterFDRepAttachmentPaidHere : Bool
  actualMonsterWholeCharacterIdentityPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  fdrepModuleActionBridgeSourceWritten := true
  groupAlgebraSubmoduleStabilitySourceWritten := true
  fdrepModuleAdapterStillResearchLeaf := false
  actualMonsterFDRepAttachmentPaidHere := false
  actualMonsterWholeCharacterIdentityPaidHere := false

end

end Synthesis.MonsterWholeCharacterModuleAdapterLive
