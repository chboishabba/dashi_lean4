import Synthesis.MillenniumHodgeTetrahedralNativeH2
import Synthesis.MillenniumHodgeTetrahedralNormalizedToSingular
import Synthesis.MillenniumHodgeCP1SingularTransport
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Tactic

/-!
# Prize-facing conditional closure of the literal CP¹ H₂ calculation

The finite simplicial calculation is already complete:

  H₂^norm(∂Δ³; Q) ≃ Q.

Only two known-math same-object bridges remain before the actual singular
homology of CP¹ is Q:

1. the geometric-realization unit induces a quasi-isomorphism on normalized
   chains for this literal tetrahedral boundary;
2. the realization |∂Δ³| is homeomorphic to the ordinary unit 2-sphere.

No general realization theorem or CW theory is formalized here.  Under exactly
those two bridges the existing native H₂ theorem transports to the already
constructed CP¹ ≃ₜ S² singular-homology carrier.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory AlgebraicTopology HomologicalComplex
open scoped Simplicial

structure TetrahedralCP1ComparisonBridges where
  unitQuasiIso : QuasiIso tetrahedralUnitNormalizedChainMap
  realizationSphere : TetrahedralRealization ≅ TopCat.of UnitSphere2

noncomputable def tetrahedralRealizationSphereSingularH2Iso
    (bridges : TetrahedralCP1ComparisonBridges) :
    tetrahedralRealizationSingularH2Native ≅ sphere2SingularH2 :=
  ((singularHomologyFunctor (ModuleCat ℚ) 2).obj
    rationalCoefficientObject).mapIso bridges.realizationSphere

noncomputable def cp1SingularH2LinearEquivQ_of_bridges
    (bridges : TetrahedralCP1ComparisonBridges) :
    cp1SingularH2 ≃ₗ[ℚ] ℚ := by
  letI : QuasiIso tetrahedralUnitNormalizedChainMap :=
    bridges.unitQuasiIso
  let h₂Iso : tetrahedralNormalizedH2 ≅
      tetrahedralRealizationSingularH2Native :=
    asIso tetrahedralNormalizedToSingularH2Map
  exact cp1SphereSingularH2Iso.toLinearEquiv.trans
    ((tetrahedralRealizationSphereSingularH2Iso bridges).toLinearEquiv.symm.trans
      (h₂Iso.toLinearEquiv.symm.trans tetrahedralNativeH2LinearEquivQ))

theorem cp1SingularH2_finrank_one_of_bridges
    (bridges : TetrahedralCP1ComparisonBridges) :
    Module.finrank ℚ cp1SingularH2 = 1 := by
  rw [(cp1SingularH2LinearEquivQ_of_bridges bridges).finrank_eq,
    Module.finrank_self]

theorem cp1_literal_H2_is_Q_of_realization_bridges
    (bridges : TetrahedralCP1ComparisonBridges) :
    Nonempty (cp1SingularH2 ≃ₗ[ℚ] ℚ) :=
  ⟨cp1SingularH2LinearEquivQ_of_bridges bridges⟩

end Synthesis.Millennium.Hodge
