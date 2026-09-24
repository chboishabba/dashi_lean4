import Synthesis.MillenniumHodgeSphereSimplicialBoundaryH2
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.Tactic

/-!
# Native simplicial facts for the tetrahedral boundary

This file ties the explicit tetrahedral H₂ calculation to mathlib's literal
simplicial object `∂Δ[3]` as far as the current API allows without a
geometric-realization/singular-homology comparison theorem.

* degree 3 has no nondegenerate simplices;
* every degree-2 simplex of Δ[3] belongs to the boundary;
* degree-2 nondegeneracy is exactly strict monotonicity of the underlying
  `Fin 3 -> Fin 4` map;
* the four codimension-one face maps `Δ[2] -> ∂Δ[3]` are literal morphisms.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory Opposite
open scoped Simplicial

theorem tetrahedralBoundary_nonDegenerate_three_empty :
    TetrahedralSphereSSet.nonDegenerate 3 = ∅ := by
  exact TetrahedralSphereSSet.nonDegenerate_eq_empty_of_hasDimensionLT 3 3

theorem tetrahedralBoundary_degreeTwo_obj_univ :
    (SSet.boundary 3).obj (op ⦋2⦌) = Set.univ := by
  exact SSet.boundary_obj_eq_univ 2 3 (by omega)

/-- The four literal triangular face inclusions of the tetrahedral boundary. -/
def tetrahedralFaceMap (i : Fin 4) :
    (Δ[2] : SSet) ⟶ TetrahedralSphereSSet :=
  SSet.boundary.ι i

/-- The corresponding literal degree-two simplex. -/
def tetrahedralFaceSimplex (i : Fin 4) :
    TetrahedralSphereSSet _⦋2⦌ :=
  SSet.yonedaEquiv (tetrahedralFaceMap i)

theorem tetrahedralFaceMap_then_boundary_inclusion (i : Fin 4) :
    tetrahedralFaceMap i ≫ (SSet.boundary 3).ι =
      SSet.stdSimplex.δ i := by
  exact SSet.boundary.ι_ι i

theorem tetrahedralBoundary_degreeTwo_val_mem_univ
    (x : TetrahedralSphereSSet _⦋2⦌) :
    x.val ∈ (SSet.boundary 3).obj (op ⦋2⦌) := by
  exact x.property

theorem tetrahedralBoundary_degreeTwo_val_nondegenerate_iff
    (x : TetrahedralSphereSSet _⦋2⦌) :
    x.val ∈ (Δ[3] : SSet).nonDegenerate 2 ↔
      StrictMono x.val := by
  exact SSet.stdSimplex.mem_nonDegenerate_iff_strictMono x.val

theorem tetrahedralBoundary_has_no_top_boundaries :
    TetrahedralSphereSSet.nonDegenerate 3 = ∅ :=
  tetrahedralBoundary_nonDegenerate_three_empty

end Synthesis.Millennium.Hodge
