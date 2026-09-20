import Synthesis.MillenniumHodgeTetrahedralBoundaryNative
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# The actual geometric-realization -> singular-set comparison map

Mathlib already provides the adjunction

  SSet.toTop ⊣ TopCat.toSSet.

For the literal tetrahedral sphere `∂Δ[3]`, its unit is therefore the canonical
simplicial map from the finite sphere to the singular simplicial set of its
geometric realization.  This is exactly the chain-level comparison map that
the Hodge CP¹ route needs before passing to homology.

This file exposes that map and its degree-two action on the four native faces.
The remaining unavailable theorem is that this unit induces an isomorphism on
normalized/singular homology in degree two (equivalently, the relevant
realization comparison theorem).
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory Opposite
open scoped Simplicial

noncomputable abbrev TetrahedralRealization : TopCat :=
  |TetrahedralSphereSSet|

noncomputable abbrev TetrahedralSingularSet : SSet :=
  TopCat.toSSet.obj TetrahedralRealization

/-- The actual unit of geometric realization / singular-set adjunction. -/
noncomputable def tetrahedralRealizationUnit :
    TetrahedralSphereSSet ⟶ TetrahedralSingularSet :=
  sSetTopAdj.unit.app TetrahedralSphereSSet

/-- The singular 2-simplex obtained from a native tetrahedral face. -/
noncomputable def tetrahedralFaceSingularSimplex (i : Fin 4) :
    TetrahedralSingularSet _⦋2⦌ :=
  (tetrahedralRealizationUnit).app (op ⦋2⦌)
    (tetrahedralFaceSimplex i)

/--
Under the explicit singular-simplex equivalence, the image of each native
tetrahedral face is exactly its geometric-realization map from the standard
topological 2-simplex.
-/
theorem tetrahedralFaceSingularSimplex_down (i : Fin 4) :
    (tetrahedralFaceSingularSimplex i).down =
      SSet.toTopSimplex.inv.app _ ≫
        SSet.toTop.map
          (SSet.yonedaEquiv.symm (tetrahedralFaceSimplex i)) := by
  exact sSetTopAdj_unit_app_app_down
    TetrahedralSphereSSet (op ⦋2⦌) (tetrahedralFaceSimplex i)

/--
The exact comparison theorem still missing from mathlib for this route.
It is stated at the correct native objects: normalized degree-two homology of
`∂Δ[3]` versus singular degree-two homology of its realization.
-/
structure TetrahedralRealizationHomologyComparison where
  simplicialH2 : Type
  realizationSingularH2 : Type
  simplicialH2EquivExplicit : simplicialH2 ≃ TetraH2Class
  unitInducedH2 : simplicialH2 → realizationSingularH2
  unitInducedH2Equiv : Nonempty (simplicialH2 ≃ realizationSingularH2)

theorem tetrahedral_realization_H2_equiv_Q
    (comparison : TetrahedralRealizationHomologyComparison) :
    Nonempty (comparison.realizationSingularH2 ≃ ℚ) := by
  rcases comparison.unitInducedH2Equiv with ⟨e⟩
  exact ⟨e.symm.trans
    (comparison.simplicialH2EquivExplicit.trans tetrahedralSphereH2EquivQ)⟩

end Synthesis.Millennium.Hodge
