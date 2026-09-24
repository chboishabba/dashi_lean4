import Synthesis.MillenniumHodgeTetrahedralRealizationUnit
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Native normalized-chain comparison for the tetrahedral sphere

The canonical map ∂Δ[3] → Sing |∂Δ[3]| now induces an actual morphism of
mathlib normalized chain complexes over Q.  Composing with
`fromNormalizedChainComplex` lands in the ordinary simplicial chain complex
of the singular simplicial set, which is definitionally the singular chain
complex of the geometric realization.

The second arrow is already a mathlib quasi-isomorphism.  Hence the only
remaining homological comparison theorem is that the unit-induced normalized
chain map itself is a quasi-isomorphism.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory
open AlgebraicTopology
open HomologicalComplex
open scoped Simplicial

noncomputable abbrev tetrahedralNormalizedChains :
    ChainComplex (ModuleCat ℚ) ℕ :=
  TetrahedralSphereSSet.normalizedChainComplex rationalCoefficientObject

noncomputable abbrev tetrahedralRealizationSingularNormalizedChains :
    ChainComplex (ModuleCat ℚ) ℕ :=
  TetrahedralSingularSet.normalizedChainComplex rationalCoefficientObject

noncomputable abbrev tetrahedralRealizationSingularChains :
    ChainComplex (ModuleCat ℚ) ℕ :=
  TetrahedralSingularSet.chainComplex rationalCoefficientObject

/-- The normalized chain map induced by the actual adjunction unit. -/
noncomputable def tetrahedralUnitNormalizedChainMap :
    tetrahedralNormalizedChains ⟶
      tetrahedralRealizationSingularNormalizedChains :=
  SSet.normalizedChainComplexMap
    tetrahedralRealizationUnit rationalCoefficientObject

/--
The actual chain map from normalized chains of the finite tetrahedral sphere
to singular chains of its geometric realization.
-/
noncomputable def tetrahedralNormalizedToSingularChainMap :
    tetrahedralNormalizedChains ⟶
      tetrahedralRealizationSingularChains :=
  tetrahedralUnitNormalizedChainMap ≫
    TetrahedralSingularSet.fromNormalizedChainComplex rationalCoefficientObject

theorem tetrahedralNormalizedToSingularChainMap_factorization :
    tetrahedralNormalizedToSingularChainMap =
      tetrahedralUnitNormalizedChainMap ≫
        TetrahedralSingularSet.fromNormalizedChainComplex rationalCoefficientObject :=
  rfl

/-- Mathlib already proves the normalized-singular to singular-chain arrow is a quasi-isomorphism. -/
example : QuasiIso
    (TetrahedralSingularSet.fromNormalizedChainComplex
      rationalCoefficientObject) := inferInstance

/--
If the unit-induced normalized-chain map is a quasi-isomorphism, then so is
the literal finite-to-singular comparison map.  The second factor is already
quasi-isomorphic in mathlib.
-/
theorem tetrahedralNormalizedToSingular_quasiIso_of_unit
    [QuasiIso tetrahedralUnitNormalizedChainMap] :
    QuasiIso tetrahedralNormalizedToSingularChainMap := by
  dsimp [tetrahedralNormalizedToSingularChainMap]
  infer_instance

noncomputable abbrev tetrahedralNormalizedH2 : ModuleCat ℚ :=
  tetrahedralNormalizedChains.homology 2

noncomputable abbrev tetrahedralRealizationSingularH2Native : ModuleCat ℚ :=
  tetrahedralRealizationSingularChains.homology 2

/-- The degree-two homology morphism induced by the literal comparison map. -/
noncomputable def tetrahedralNormalizedToSingularH2Map :
    tetrahedralNormalizedH2 ⟶ tetrahedralRealizationSingularH2Native :=
  HomologicalComplex.homologyMap
    tetrahedralNormalizedToSingularChainMap 2

/--
Under the one missing quasi-isomorphism instance, the degree-two comparison
map is automatically an isomorphism in the categorical sense.
-/
theorem tetrahedralNormalizedToSingularH2_isIso_of_unit
    [QuasiIso tetrahedralUnitNormalizedChainMap] :
    IsIso tetrahedralNormalizedToSingularH2Map := by
  letI : QuasiIso tetrahedralNormalizedToSingularChainMap :=
    tetrahedralNormalizedToSingular_quasiIso_of_unit
  infer_instance

end Synthesis.Millennium.Hodge
