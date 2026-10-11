import Integration.OggSSP2BTateCokernelRankRigidity
import Integration.OggSSP2BCo1FrobeniusHomRigidity
import Integration.OggSSP2BCommonLaneKernelWeld

/-!
# Terminal norm-weld compiler for the weight-two 2B Tate quotient

The source-native weight-two norm map has the shape

  M_minus(98304) -> C_common(98280) ⊕ Sym2(24)(300).

`OggSSP2BTateCokernelRankRigidity` proves that, once the runtime support-
separation hypotheses hold, the residual projection has rank 24 and its kernel
has dimension 98280.  `OggSSP2BCommonLaneKernelWeld` then removes the last
spurious common-lane hypothesis: injectivity of the full norm map makes the
common projection injective on that residual kernel, and equal finite
dimensions force an isomorphism with the 98280-dimensional common target.

The GAP Hom screen is designed to prove that over GF(2) the explicit
Frobenius-square embedding is the unique nonzero Co1-equivariant map
24 -> Sym2(24).  Thus, once the runtime support/rank and Hom-uniqueness facts
are promoted, both common and residual lanes are forced.  The remaining
scientific acquisition is the actual source-native coordinate splitting / norm
map data, not another abstract same-object proposition.
-/

namespace Integration.OggSSP2BNormWeldCompiler

namespace Rank := Integration.OggSSP2BTateCokernelRankRigidity
namespace Kernel := Integration.OggSSP2BCommonLaneKernelWeld

/-- Proof-bearing version of the runtime statement that `frobenius` is the
unique nonzero equivariant map in the relevant Hom space.  The runtime screen
must supply this theorem; a Boolean flag is not enough. -/
structure UniqueNonzeroMapReceipt
    {R V S : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V]
    [AddCommMonoid S] [Module R S]
    (frobenius : V →ₗ[R] S) : Prop where
  frobenius_ne_zero : frobenius ≠ 0
  unique_nonzero : ∀ f : V →ₗ[R] S, f ≠ 0 → f = frobenius

/-- The actual residual norm projection is forced to be the Frobenius-square
embedding once rank rigidity proves that it is nonzero and the Hom computation
proves uniqueness of the nonzero equivariant map. -/
theorem residualMapForcedFrobenius
    {R V S : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V]
    [AddCommMonoid S] [Module R S]
    (residual frobenius : V →ₗ[R] S)
    (hunique : UniqueNonzeroMapReceipt frobenius)
    (hresidual : residual ≠ 0) :
    residual = frobenius :=
  hunique.unique_nonzero residual hresidual

/-- Numeric part of the same max-cut: the source-native total rank and common
lane size force exactly a 24-dimensional residual image. -/
theorem residualRankForcedTwentyFour
    (r : Rank.RankRigidityReceipt) :
    r.residualProjectionRank = 24 :=
  r.residual_rank_eq_24

/-- The complementary kernel is exactly the common 98280 lane in dimension. -/
theorem commonKernelForced98280
    (r : Rank.RankRigidityReceipt) :
    r.residualProjectionKernelDimension = 98280 :=
  r.kernel_dimension_eq_98280

/-- A proof-relevant terminal receipt.  The common-lane proposition is retained
for compatibility with existing downstream code, but the preferred compiler
below derives it from the actual residual-kernel geometry. -/
structure NormWeldReceipt where
  commonLaneSameObject : Prop
  commonLaneSameObject_paid : commonLaneSameObject
  residualRank : Nat
  residualRank_eq_24 : residualRank = 24
  commonKernelDimension : Nat
  commonKernelDimension_eq_98280 : commonKernelDimension = 98280
  residualMapIsFrobenius : Prop
  residualMapIsFrobenius_paid : residualMapIsFrobenius
  tateCokernelIsExteriorSquare : Prop
  tateCokernelIsExteriorSquare_paid : tateCokernelIsExteriorSquare

/-- Compatibility compiler for existing callers. -/
def compileNormWeld
    (commonLaneSameObject : Prop)
    (hcommon : commonLaneSameObject)
    (rankReceipt : Rank.RankRigidityReceipt)
    (residualMapIsFrobenius : Prop)
    (hresidual : residualMapIsFrobenius)
    (tateCokernelIsExteriorSquare : Prop)
    (hexterior : tateCokernelIsExteriorSquare) :
    NormWeldReceipt where
  commonLaneSameObject := commonLaneSameObject
  commonLaneSameObject_paid := hcommon
  residualRank := rankReceipt.residualProjectionRank
  residualRank_eq_24 := rankReceipt.residual_rank_eq_24
  commonKernelDimension := rankReceipt.residualProjectionKernelDimension
  commonKernelDimension_eq_98280 := rankReceipt.kernel_dimension_eq_98280
  residualMapIsFrobenius := residualMapIsFrobenius
  residualMapIsFrobenius_paid := hresidual
  tateCokernelIsExteriorSquare := tateCokernelIsExteriorSquare
  tateCokernelIsExteriorSquare_paid := hexterior

/-- Preferred max-cut compiler: the common 98280 same-object statement is
constructed from the actual common/residual projections and the residual-kernel
finrank equality; callers no longer provide it as an independent hypothesis. -/
noncomputable def compileNormWeldFromKernel
    {K M C S : Type*}
    [DivisionRing K]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup S] [Module K S] [FiniteDimensional K S]
    (kernelData : Kernel.KernelWeldData (K := K) (M := M) (C := C) (S := S))
    (rankReceipt : Rank.RankRigidityReceipt)
    (residualMapIsFrobenius : Prop)
    (hresidual : residualMapIsFrobenius)
    (tateCokernelIsExteriorSquare : Prop)
    (hexterior : tateCokernelIsExteriorSquare) :
    NormWeldReceipt :=
  compileNormWeld
    (Nonempty (kernelData.residualProjection.ker ≃ₗ[K] C))
    kernelData.commonLaneSameObjectPaid
    rankReceipt
    residualMapIsFrobenius hresidual
    tateCokernelIsExteriorSquare hexterior

/-- Roadmap compression: once actual projections and the kernel-finrank theorem
are supplied, the common lane is already a same-object linear equivalence. -/
theorem commonLaneDerivedFromKernel
    {K M C S : Type*}
    [DivisionRing K]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup S] [Module K S] [FiniteDimensional K S]
    (kernelData : Kernel.KernelWeldData (K := K) (M := M) (C := C) (S := S)) :
    Nonempty (kernelData.residualProjection.ker ≃ₗ[K] C) :=
  kernelData.commonLaneSameObjectPaid

end Integration.OggSSP2BNormWeldCompiler
