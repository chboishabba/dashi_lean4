import Synthesis.MillenniumHodgeTetrahedralNativeDifferential
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

/-!
# Injective native-to-ambient chain comparison for ∂Δ[3] ⊂ Δ[3]

The native normalized complex embeds split-monomorphically into the ordinary
simplicial chain complex.  The ordinary chain map induced by the boundary
inclusion `∂Δ[3] ⟶ Δ[3]` is degreewise monic by mathlib's `SSetPair` relative
homology infrastructure.  Their composite is therefore monic in every degree.

This is the cancellation tool needed to prove the native fundamental chain is
a cycle by checking its image in the ambient standard 3-simplex.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory Opposite
open scoped Simplicial

noncomputable abbrev tetrahedralBoundaryPair : SSetPair :=
  (SSet.boundary 3).pair

noncomputable def tetrahedralNativeToAmbientOrdinary (n : ℕ) :
    tetrahedralNormalizedChains.X n ⟶
      ((Δ[3] : SSet).chainComplex rationalCoefficientObject).X n :=
  (TetrahedralSphereSSet.fromNormalizedChainComplex
      rationalCoefficientObject).f n ≫
    (SSet.chainComplexMap (SSet.boundary 3).ι
      rationalCoefficientObject).f n

instance tetrahedralNativeToAmbientOrdinary_mono (n : ℕ) :
    Mono (tetrahedralNativeToAmbientOrdinary n) := by
  unfold tetrahedralNativeToAmbientOrdinary
  apply mono_comp
  · infer_instance
  · change Mono ((SSet.chainComplexMap
      tetrahedralBoundaryPair.hom rationalCoefficientObject).f n)
    infer_instance

theorem tetrahedralNativeToAmbientOrdinary_cancel
    {n : ℕ} {T : ModuleCat ℚ}
    (f g : T ⟶ tetrahedralNormalizedChains.X n)
    (h : f ≫ tetrahedralNativeToAmbientOrdinary n =
      g ≫ tetrahedralNativeToAmbientOrdinary n) :
    f = g := by
  exact (cancel_mono (tetrahedralNativeToAmbientOrdinary n)).mp h

end Synthesis.Millennium.Hodge
