import Synthesis.MillenniumHodgeCP1TopologicalSphere
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Actual singular-chain and singular-homology transport CP¹ ≃ S²

The topology tranche already proves an honest homeomorphism

  CP¹ ≃ₜ S².

Singular chains and singular homology are functorial in TopCat, so this file
pushes that actual homeomorphism through mathlib's singular chain complex and
degree-two singular homology functors with rational coefficients.

This pays the CP¹-to-sphere same-object transport completely.  It does not
postulate the homology of S²: the remaining theorem is now exactly the
calculation H₂(S²; Q) ≅ Q (or its cohomological dual).
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory
open AlgebraicTopology

noncomputable def cp1SphereTopIso :
    TopCat.of CP1 ≅ TopCat.of UnitSphere2 :=
  TopCat.isoOfHomeo cp1HomeomorphSphere

noncomputable def rationalCoefficientObject :
    ModuleCat ℚ :=
  ModuleCat.of ℚ ℚ

noncomputable def cp1SingularChainComplex :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficientObject).obj (TopCat.of CP1)

noncomputable def sphere2SingularChainComplex :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficientObject).obj (TopCat.of UnitSphere2)

noncomputable def cp1SphereSingularChainIso :
    cp1SingularChainComplex ≅ sphere2SingularChainComplex :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficientObject).mapIso cp1SphereTopIso

noncomputable def cp1SingularH2 : ModuleCat ℚ :=
  ((singularHomologyFunctor (ModuleCat ℚ) 2).obj
    rationalCoefficientObject).obj (TopCat.of CP1)

noncomputable def sphere2SingularH2 : ModuleCat ℚ :=
  ((singularHomologyFunctor (ModuleCat ℚ) 2).obj
    rationalCoefficientObject).obj (TopCat.of UnitSphere2)

noncomputable def cp1SphereSingularH2Iso :
    cp1SingularH2 ≅ sphere2SingularH2 :=
  ((singularHomologyFunctor (ModuleCat ℚ) 2).obj
    rationalCoefficientObject).mapIso cp1SphereTopIso

theorem cp1SphereSingularH2_hom_inv_id :
    cp1SphereSingularH2Iso.hom ≫
      cp1SphereSingularH2Iso.inv = 𝟙 cp1SingularH2 := by
  simp

theorem cp1SphereSingularH2_inv_hom_id :
    cp1SphereSingularH2Iso.inv ≫
      cp1SphereSingularH2Iso.hom = 𝟙 sphere2SingularH2 := by
  simp

end Synthesis.Millennium.Hodge
