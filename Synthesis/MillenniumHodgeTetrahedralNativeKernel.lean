import Synthesis.MillenniumHodgeDeltaThreeExactAtTwo
import Synthesis.MillenniumHodgeTetrahedralNativeCycle
import Synthesis.MillenniumHodgeTetrahedralNativeAmbientMono
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Tactic

/-!
# H5: the native tetrahedral degree-two kernel is one-dimensional

This is the Clay-facing finite argument only.

* `N₂(∂Δ³;Q) → N₂(Δ³;Q)` is monic.
* `N_*(Δ³;Q)` is exact at degree 2.
* `N₃(Δ³;Q)` has one nondegenerate generator, the top simplex.
* the image of the tetrahedral fundamental chain is exactly the boundary of
  that top simplex.

Hence every native tetrahedral 2-cycle is a unique scalar multiple of the
native fundamental chain.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory Limits
open AlgebraicTopology HomologicalComplex
open scoped Simplicial

noncomputable def tetrahedralNativeToAmbientNormalized :
    tetrahedralNormalizedChains ⟶ deltaThreeNormalizedChains :=
  SSet.normalizedChainComplexMap (SSet.boundary 3).ι rationalCoefficientObject

theorem tetrahedralNativeToAmbientNormalized_comp_fromNormalized (n : ℕ) :
    (tetrahedralNativeToAmbientNormalized.f n) ≫
        ((Δ[3] : SSet).fromNormalizedChainComplex
          rationalCoefficientObject).f n
      = tetrahedralNativeToAmbientOrdinary n := by
  simp [tetrahedralNativeToAmbientNormalized,
    tetrahedralNativeToAmbientOrdinary, SSet.normalizedChainComplexMap,
    Category.assoc]

instance tetrahedralNativeToAmbientNormalized_mono (n : ℕ) :
    Mono (tetrahedralNativeToAmbientNormalized.f n) := by
  apply mono_of_mono_fac
    (tetrahedralNativeToAmbientNormalized_comp_fromNormalized n)

theorem tetrahedralFace_toAmbientNormalized_is_topFace (i : Fin 4) :
    tetrahedralNativeFaceChain i ≫
        tetrahedralNativeToAmbientNormalized.f 2 =
      (Δ[3] : SSet).ιNormalizedChainComplex
        ((Δ[3] : SSet).δ i deltaThreeTopSimplex) := by
  simp [tetrahedralNativeFaceChain, tetrahedralNativeToAmbientNormalized,
    tetrahedralFaceSimplex, tetrahedralFaceMap, deltaThreeTopSimplex,
    SSet.ι_normalizedChainComplexMap_f]

theorem tetrahedralNativeFundamental_to_ambient_normalized_boundary :
    tetrahedralNativeFundamentalChain ≫
        tetrahedralNativeToAmbientNormalized.f 2 =
      deltaThreeTopGenerator ≫ deltaThreeNormalizedChains.d 3 2 := by
  rw [show deltaThreeTopGenerator ≫ deltaThreeNormalizedChains.d 3 2 =
      ∑ i : Fin 4, ((-1 : ℚ) ^ i.val) •
        (Δ[3] : SSet).ιNormalizedChainComplex
          ((Δ[3] : SSet).δ i deltaThreeTopSimplex) by
        simpa [deltaThreeTopGenerator] using
          ((Δ[3] : SSet).ιNormalizedChainComplex_d
            (R := rationalCoefficientObject)
            (n := 2) deltaThreeTopSimplex)]
  simp only [tetrahedralNativeFundamentalChain, Preadditive.sum_comp,
    Preadditive.smul_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tetrahedralFace_toAmbientNormalized_is_topFace i]

instance deltaThreeTopGenerator_epi : Epi deltaThreeTopGenerator where
  left_cancellation f g h := by
    apply deltaThreeNormalized_degreeThree_hom_ext_top
    simpa [Category.assoc] using h

/-- Every native two-cycle factors through the tetrahedral fundamental chain. -/
theorem tetrahedralNative_cycle_factors_fundamental
    (c : rationalCoefficientObject ⟶ tetrahedralNormalizedChains.X 2)
    (hc : c ≫ tetrahedralNormalizedChains.d 2 1 = 0) :
    ∃ φ : rationalCoefficientObject ⟶ rationalCoefficientObject,
      c = φ ≫ tetrahedralNativeFundamentalChain := by
  let j₂ := tetrahedralNativeToAmbientNormalized.f 2
  let cA : rationalCoefficientObject ⟶ deltaThreeNormalizedChains.X 2 :=
    c ≫ j₂
  have hcA : cA ≫ deltaThreeNormalizedChains.d 2 1 = 0 := by
    dsimp [cA, j₂]
    rw [Category.assoc, ← tetrahedralNativeToAmbientNormalized.comm 2 1,
      ← Category.assoc, hc, zero_comp]
  have hExact : (deltaThreeNormalizedChains.sc 2).Exact := by
    exact deltaThreeNormalized_exactAt_two
  let b : rationalCoefficientObject ⟶ deltaThreeNormalizedChains.X 3 :=
    hExact.liftFromProjective cA hcA
  have hb : b ≫ deltaThreeNormalizedChains.d 3 2 = cA := by
    exact hExact.liftFromProjective_comp cA hcA
  let φ : rationalCoefficientObject ⟶ rationalCoefficientObject :=
    Projective.factorThru b deltaThreeTopGenerator
  have hφ : φ ≫ deltaThreeTopGenerator = b := by
    exact Projective.factorThru_comp b deltaThreeTopGenerator
  refine ⟨φ, ?_⟩
  apply (cancel_mono j₂).1
  calc
    c ≫ j₂ = cA := rfl
    _ = b ≫ deltaThreeNormalizedChains.d 3 2 := hb.symm
    _ = (φ ≫ deltaThreeTopGenerator) ≫
        deltaThreeNormalizedChains.d 3 2 := by rw [hφ]
    _ = φ ≫ (deltaThreeTopGenerator ≫
        deltaThreeNormalizedChains.d 3 2) := by simp [Category.assoc]
    _ = φ ≫ (tetrahedralNativeFundamentalChain ≫ j₂) := by
      rw [tetrahedralNativeFundamental_to_ambient_normalized_boundary]
    _ = (φ ≫ tetrahedralNativeFundamentalChain) ≫ j₂ := by
      simp [Category.assoc]

/-- Endomorphisms of the one-dimensional coefficient module are scalars. -/
theorem rationalCoefficient_endomorphism_is_scalar
    (φ : rationalCoefficientObject ⟶ rationalCoefficientObject) :
    ∃ q : ℚ, φ = q • 𝟙 rationalCoefficientObject := by
  refine ⟨φ (1 : ℚ), ?_⟩
  ext x
  change φ x = φ 1 * x
  calc
    φ x = φ (x • (1 : ℚ)) := by simp
    _ = x • φ 1 := by rw [map_smul]
    _ = φ 1 * x := by simp [mul_comm]

/-- H5 in scalar form: the full native kernel is the fundamental line. -/
theorem tetrahedralNative_cycle_eq_scalar_fundamental
    (c : rationalCoefficientObject ⟶ tetrahedralNormalizedChains.X 2)
    (hc : c ≫ tetrahedralNormalizedChains.d 2 1 = 0) :
    ∃ q : ℚ, c = q • tetrahedralNativeFundamentalChain := by
  rcases tetrahedralNative_cycle_factors_fundamental c hc with ⟨φ,hφ⟩
  rcases rationalCoefficient_endomorphism_is_scalar φ with ⟨q,rfl⟩
  refine ⟨q, ?_⟩
  rw [hφ]
  simp [Preadditive.smul_comp]

/-- The fundamental line really consists of cycles. -/
theorem tetrahedralNative_scalar_fundamental_isCycle (q : ℚ) :
    (q • tetrahedralNativeFundamentalChain) ≫
      tetrahedralNormalizedChains.d 2 1 = 0 := by
  rw [Preadditive.smul_comp, tetrahedralNativeFundamental_isCycle, smul_zero]

end Synthesis.Millennium.Hodge
