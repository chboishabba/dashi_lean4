import Synthesis.MillenniumHodgeTetrahedralNativeCycle
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Tactic

/-!
# Only the ambient acyclicity needed for tetrahedral H₂

We do not formalize a theory of contractible simplicial sets.  We instantiate
mathlib's existing extra-degeneracy contraction once, for the standard
3-simplex with Q coefficients.  This proves the ordinary H₂ of Δ[3] is zero;
the normalized H₂ is then zero via the existing normalized→ordinary quasi-iso.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory Limits
open AlgebraicTopology HomologicalComplex
open scoped Simplicial

noncomputable def deltaThreeFreeExtraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy
      ((((SimplicialObject.Augmented.whiskering _ _).obj
          (sigmaConst.obj rationalCoefficientObject)).obj
        (SSet.Augmented.stdSimplex.obj ⦋3⦌))) :=
  (SSet.Augmented.StandardSimplex.extraDegeneracy ⦋3⦌).map
    (sigmaConst.obj rationalCoefficientObject)

noncomputable def deltaThreeOrdinaryHomotopyEquiv :=
  deltaThreeFreeExtraDegeneracy.homotopyEquiv

theorem deltaThreeOrdinaryH2_isZero :
    IsZero (((Δ[3] : SSet).chainComplex rationalCoefficientObject).homology 2) := by
  let e := deltaThreeOrdinaryHomotopyEquiv.toHomologyIso 2
  apply (Iso.isZero_iff e).2
  exact isZero_single_obj_homology _ 2 (by omega : 2 ≠ 0)

noncomputable def deltaThreeNormalizedToOrdinary :
    (Δ[3] : SSet).normalizedChainComplex rationalCoefficientObject ⟶
      (Δ[3] : SSet).chainComplex rationalCoefficientObject :=
  (Δ[3] : SSet).fromNormalizedChainComplex rationalCoefficientObject

instance : QuasiIso deltaThreeNormalizedToOrdinary := inferInstance

theorem deltaThreeNormalizedH2_isZero :
    IsZero (((Δ[3] : SSet).normalizedChainComplex
      rationalCoefficientObject).homology 2) := by
  let e :
      ((Δ[3] : SSet).normalizedChainComplex rationalCoefficientObject).homology 2 ≅
        ((Δ[3] : SSet).chainComplex rationalCoefficientObject).homology 2 :=
    asIso (HomologicalComplex.homologyMap deltaThreeNormalizedToOrdinary 2)
  exact (Iso.isZero_iff e).2 deltaThreeOrdinaryH2_isZero

end Synthesis.Millennium.Hodge
