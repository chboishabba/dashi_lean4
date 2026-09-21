import Synthesis.MillenniumHodgeTetrahedralNativeH2
import Synthesis.MillenniumHodgeTetrahedralNormalizedToSingular
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Tactic

/-!
# Prize-facing tetrahedral realization H2 bridge

The finite/native H2 computation is already complete:

  H2^norm(partial Delta[3]; Q) ~= Q.

The actual adjunction-unit chain map and its factorization through normalized
singular chains are also already in the repository.  This file specializes
the remaining known-math theorem to exactly the object Clay-facing CP1 needs:

  if the actual realization unit is a quasi-isomorphism, then
  H2^sing(|partial Delta[3]|; Q) ~= Q.

No generic geometric-realization theorem is developed here.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory
open AlgebraicTopology

/-- The single known-math theorem still missing on the tetrahedral realization route. -/
def TetrahedralRealizationUnitQuasiIso : Prop :=
  QuasiIso tetrahedralUnitNormalizedChainMap

/-- Under the one missing realization theorem, the actual H2 map is a linear equivalence. -/
noncomputable def tetrahedralNormalizedToSingularH2LinearEquiv
    (hunit : TetrahedralRealizationUnitQuasiIso) :
    tetrahedralNormalizedH2 ≃ₗ[ℚ] tetrahedralRealizationSingularH2Native := by
  letI : QuasiIso tetrahedralUnitNormalizedChainMap := hunit
  letI : IsIso tetrahedralNormalizedToSingularH2Map :=
    tetrahedralNormalizedToSingularH2_isIso_of_unit
  exact LinearEquiv.ofBijective
    tetrahedralNormalizedToSingularH2Map.hom
    (ConcreteCategory.bijective_of_isIso tetrahedralNormalizedToSingularH2Map)

/-- Prize-facing consequence: singular H2 of the literal realization is Q. -/
noncomputable def tetrahedralRealizationSingularH2LinearEquivQ
    (hunit : TetrahedralRealizationUnitQuasiIso) :
    tetrahedralRealizationSingularH2Native ≃ₗ[ℚ] ℚ :=
  (tetrahedralNormalizedToSingularH2LinearEquiv hunit).symm.trans
    tetrahedralNativeH2LinearEquivQ

theorem tetrahedralRealizationSingularH2_finrank
    (hunit : TetrahedralRealizationUnitQuasiIso) :
    Module.finrank ℚ tetrahedralRealizationSingularH2Native = 1 := by
  rw [(tetrahedralRealizationSingularH2LinearEquivQ hunit).finrank_eq,
    Module.finrank_self]

/--
Every finite simplicial calculation below the realization theorem is now gone
from the open frontier: supplying exactly this quasi-isomorphism produces the
desired one-dimensional singular H2 immediately.
-/
theorem tetrahedral_realization_H2_Q_of_unit_quasiIso
    (hunit : TetrahedralRealizationUnitQuasiIso) :
    Nonempty (tetrahedralRealizationSingularH2Native ≃ₗ[ℚ] ℚ) :=
  ⟨tetrahedralRealizationSingularH2LinearEquivQ hunit⟩

end Synthesis.Millennium.Hodge
