import Integration.OggSSP2BTateCokernelRankRigidity
import Integration.OggSSP2BCo1FrobeniusHomRigidity
import Integration.OggSSP2BCommonLaneKernelWeld
import Integration.OggSSP2BCokernelCancellation
import Integration.OggSSP2BResidualFrobeniusWeld

/-!
# Terminal norm-weld compiler for the weight-two 2B Tate quotient

The source-native weight-two norm map has the shape

  M_minus(98304) -> C_common(98280) ⊕ Sym2(24)(300).

The preferred proof path is fully map-coupled:

* actual common/residual projections plus injectivity of their paired norm map;
* a `LinearRankRigidityReceipt` attaching the 24/98280 squeeze to the actual
  residual map;
* the actual common target finrank 98280;
* a Co1-equivariant chart
      M / ker(residual) ≃ V24;
* uniqueness of the nonzero V24 -> Sym2(24) Hom line;
* the concrete quotient theorem
      Sym2(24) / range(Frobenius) ≃ Exterior276.

Crucial typing point: the original residual map has source dimension 98304 and
is NOT equated with Frobenius.  Only its induced map on the 24-dimensional
kernel quotient is forced to Frobenius.  This yields equality of image
submodules, which is precisely what cokernel identification requires.
-/

namespace Integration.OggSSP2BNormWeldCompiler

namespace Rank := Integration.OggSSP2BTateCokernelRankRigidity
namespace Kernel := Integration.OggSSP2BCommonLaneKernelWeld
namespace RF := Integration.OggSSP2BResidualFrobeniusWeld

/-- Numeric views retained for compatibility. -/
theorem residualRankForcedTwentyFour
    (r : Rank.RankRigidityReceipt) :
    r.residualProjectionRank = 24 :=
  r.residual_rank_eq_24

theorem commonKernelForced98280
    (r : Rank.RankRigidityReceipt) :
    r.residualProjectionKernelDimension = 98280 :=
  r.kernel_dimension_eq_98280

/-- Build the common-lane kernel weld directly from actual map coordinates and
the map-coupled rank receipt. -/
def kernelWeldDataFromActualMaps
    {K M C S : Type*}
    [DivisionRing K]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup S] [Module K S] [FiniteDimensional K S]
    (common : M →ₗ[K] C)
    (residual : M →ₗ[K] S)
    (paired_injective : Function.Injective (fun x : M => (common x, residual x)))
    (hrank : Rank.LinearRankRigidityReceipt residual)
    (hcommonFinrank : Module.finrank K C = 98280) :
    Kernel.KernelWeldData (K := K) (M := M) (C := C) (S := S) where
  commonProjection := common
  residualProjection := residual
  paired_injective := paired_injective
  kernel_finrank_eq_common := by
    calc
      Module.finrank K residual.ker = 98280 := hrank.kernel_finrank_eq_98280
      _ = Module.finrank K C := hcommonFinrank.symm

/-- A proof-relevant terminal receipt.  Proposition fields are retained for
compatibility; preferred compilers construct them from actual equivalences. -/
structure NormWeldReceipt where
  commonLaneSameObject : Prop
  commonLaneSameObject_paid : commonLaneSameObject
  residualRank : Nat
  residualRank_eq_24 : residualRank = 24
  commonKernelDimension : Nat
  commonKernelDimension_eq_98280 : commonKernelDimension = 98280
  inducedResidualMapIsFrobenius : Prop
  inducedResidualMapIsFrobenius_paid : inducedResidualMapIsFrobenius
  tateCokernelIsExteriorSquare : Prop
  tateCokernelIsExteriorSquare_paid : tateCokernelIsExteriorSquare

/-- Compatibility compiler for existing callers.  Note that the Frobenius
proposition now refers to the induced 24-dimensional quotient map. -/
def compileNormWeld
    (commonLaneSameObject : Prop)
    (hcommon : commonLaneSameObject)
    (rankReceipt : Rank.RankRigidityReceipt)
    (inducedResidualMapIsFrobenius : Prop)
    (hresidual : inducedResidualMapIsFrobenius)
    (tateCokernelIsExteriorSquare : Prop)
    (hexterior : tateCokernelIsExteriorSquare) :
    NormWeldReceipt where
  commonLaneSameObject := commonLaneSameObject
  commonLaneSameObject_paid := hcommon
  residualRank := rankReceipt.residualProjectionRank
  residualRank_eq_24 := rankReceipt.residual_rank_eq_24
  commonKernelDimension := rankReceipt.residualProjectionKernelDimension
  commonKernelDimension_eq_98280 := rankReceipt.kernel_dimension_eq_98280
  inducedResidualMapIsFrobenius := inducedResidualMapIsFrobenius
  inducedResidualMapIsFrobenius_paid := hresidual
  tateCokernelIsExteriorSquare := tateCokernelIsExteriorSquare
  tateCokernelIsExteriorSquare_paid := hexterior

/-- Compatibility first-stage compiler from an already assembled kernel weld. -/
noncomputable def compileNormWeldFromKernel
    {K M C S : Type*}
    [DivisionRing K]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup S] [Module K S] [FiniteDimensional K S]
    (kernelData : Kernel.KernelWeldData (K := K) (M := M) (C := C) (S := S))
    (rankReceipt : Rank.RankRigidityReceipt)
    (inducedResidualMapIsFrobenius : Prop)
    (hresidual : inducedResidualMapIsFrobenius)
    (tateCokernelIsExteriorSquare : Prop)
    (hexterior : tateCokernelIsExteriorSquare) :
    NormWeldReceipt :=
  compileNormWeld
    (Nonempty (kernelData.residualProjection.ker ≃ₗ[K] C))
    kernelData.commonLaneSameObjectPaid
    rankReceipt
    inducedResidualMapIsFrobenius hresidual
    tateCokernelIsExteriorSquare hexterior

/-- Literal full-Tate cokernel equivalence obtained by cancelling the common
lane and then applying a supplied equivalence for the residual cokernel. -/
noncomputable def tateCokernelEquivFromResidual
    {K M C S E : Type*}
    [DivisionRing K]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup S] [Module K S] [FiniteDimensional K S]
    [AddCommGroup E] [Module K E]
    (kernelData : Kernel.KernelWeldData (K := K) (M := M) (C := C) (S := S))
    (residualExterior : (S ⧸ kernelData.residualRange) ≃ₗ[K] E) :
    ((C × S) ⧸ kernelData.normRange) ≃ₗ[K] E :=
  kernelData.cokernelEquivResidualCokernel.trans residualExterior

/-- Turn the quotient-correct Frobenius weld into the actual residual cokernel
identification.  The original residual and Frobenius maps need only have equal
ranges, not equal domains. -/
noncomputable def residualCokernelEquivFromFrobenius
    {K M S V E : Type*}
    [DivisionRing K]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [AddCommGroup S] [Module K S] [FiniteDimensional K S]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup E] [Module K E]
    (residual : M →ₗ[K] S)
    (frobenius : V →ₗ[K] S)
    (hrank : Rank.LinearRankRigidityReceipt residual)
    (rf : RF.ResidualFrobeniusReceipt residual frobenius)
    (frobeniusExterior : (S ⧸ frobenius.range) ≃ₗ[K] E) :
    (S ⧸ residual.range) ≃ₗ[K] E := by
  let hRange : residual.range = frobenius.range :=
    rf.residual_range_eq_frobenius_range hrank
  exact (residual.range.quotEquivOfEq frobenius.range hRange).trans
    frobeniusExterior

/-- Compatibility compiler from a preassembled kernel weld and residual
quotient equivalence. -/
noncomputable def compileNormWeldFromResidualEquiv
    {K M C S E : Type*}
    [DivisionRing K]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup S] [Module K S] [FiniteDimensional K S]
    [AddCommGroup E] [Module K E]
    (kernelData : Kernel.KernelWeldData (K := K) (M := M) (C := C) (S := S))
    (rankReceipt : Rank.RankRigidityReceipt)
    (inducedResidualMapIsFrobenius : Prop)
    (hresidual : inducedResidualMapIsFrobenius)
    (residualExterior : (S ⧸ kernelData.residualRange) ≃ₗ[K] E) :
    NormWeldReceipt :=
  compileNormWeld
    (Nonempty (kernelData.residualProjection.ker ≃ₗ[K] C))
    kernelData.commonLaneSameObjectPaid
    rankReceipt
    inducedResidualMapIsFrobenius hresidual
    (Nonempty (((C × S) ⧸ kernelData.normRange) ≃ₗ[K] E))
    ⟨tateCokernelEquivFromResidual kernelData residualExterior⟩

/-- Correct strongest map-level compiler.  The Hom uniqueness theorem is used
only on the 24-dimensional kernel quotient. -/
noncomputable def compileNormWeldFromActualMaps
    {K M C S V E : Type*}
    [DivisionRing K]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup S] [Module K S] [FiniteDimensional K S]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup E] [Module K E]
    (common : M →ₗ[K] C)
    (residual : M →ₗ[K] S)
    (frobenius : V →ₗ[K] S)
    (paired_injective : Function.Injective (fun x : M => (common x, residual x)))
    (hrank : Rank.LinearRankRigidityReceipt residual)
    (hcommonFinrank : Module.finrank K C = 98280)
    (rf : RF.ResidualFrobeniusReceipt residual frobenius)
    (frobeniusExterior : (S ⧸ frobenius.range) ≃ₗ[K] E) :
    NormWeldReceipt := by
  let kd := kernelWeldDataFromActualMaps common residual paired_injective
    hrank hcommonFinrank
  have hFrob : rf.quotientNatural.onNatural = frobenius :=
    rf.onNatural_eq_frobenius hrank
  let residualExterior : (S ⧸ residual.range) ≃ₗ[K] E :=
    residualCokernelEquivFromFrobenius residual frobenius hrank rf
      frobeniusExterior
  exact compileNormWeldFromResidualEquiv
    kd hrank.numeric
    (rf.quotientNatural.onNatural = frobenius) hFrob residualExterior

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
