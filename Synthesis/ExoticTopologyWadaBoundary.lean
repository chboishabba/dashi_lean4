import Mathlib.Topology.Constructions
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# The actual common-boundary test for Lakes of Wada

This is a concrete point-set topology ACCEPTANCE CONTRACT, not merely
a three-colour finite incidence table. The family is required to have
nonempty, open, connected, pairwise disjoint domains and one nonempty
common topological frontier. An instance would need to be provided
by a genuine Wada domain construction and geometric limit proof.

Historical sources: Yoneyama (1917), inspired by Wada's construction;
modern variants must be separately source-identified. Prior related
DASHI donor: ExoticWadaC3BoundaryNoGoExact.agda proves a C3 symmetry
does NOT force equal boundary incidences.
-/

namespace Synthesis.ExoticTopology

universe u

structure WadaThreeDomains (X : Type u) [TopologicalSpace X] where
  region : Fin 3 → Set X
  open_region : ∀ i, IsOpen (region i)
  connected_region : ∀ i, IsConnected (region i)
  nonempty_region : ∀ i, (region i).Nonempty
  disjoint_region : ∀ i j, i ≠ j → Disjoint (region i) (region j)
  common_frontier : ∀ i j, frontier (region i) = frontier (region j)
  frontier_nonempty : (frontier (region 0)).Nonempty

/-- A common-boundary point lies in each closure. This uses actual
    `frontier` and `closure` of the ambient topology. -/
theorem WadaThreeDomains.commonFrontier_in_all_closures
    {X : Type u} [TopologicalSpace X] (W : WadaThreeDomains X)
    {x : X} (hx : x ∈ frontier (W.region 0)) (i : Fin 3) :
    x ∈ closure (W.region i) := by
  have hi : x ∈ frontier (W.region i) := by
    rw [← W.common_frontier 0 i]
    exact hx
  change x ∈ closure (W.region i) \ interior (W.region i) at hi
  exact hi.1

/-- A shared frontier cannot contain a point in any of the open
    domains. Consequently, numerical C3 incidence alone could not
    certify the condition. -/
theorem WadaThreeDomains.commonFrontier_disjoint_all_regions
    {X : Type u} [TopologicalSpace X] (W : WadaThreeDomains X)
    {x : X} (hx : x ∈ frontier (W.region 0)) (i : Fin 3) :
    x ∉ W.region i := by
  intro hmem
  have hi : x ∈ frontier (W.region i) := by
    rw [← W.common_frontier 0 i]
    exact hx
  change x ∈ closure (W.region i) \ interior (W.region i) at hi
  have hint : x ∈ interior (W.region i) := by
    simpa [W.open_region i] using hmem
  exact hi.2 hint

/-- Local topological Wada recognizer, with an honest existential
    geometric input rather than an automatically inhabited field. -/
def HasWadaTriple (X : Type u) [TopologicalSpace X] : Prop :=
  Nonempty (WadaThreeDomains X)

end Synthesis.ExoticTopology
