import Integration.OggSSP2BTateCokernelRankRigidity
import Integration.OggSSP2BCo1FrobeniusHomRigidity
import Integration.OggSSP2BCommonLaneKernelWeld
import Integration.OggSSP2BCokernelCancellation

/-!
# Terminal norm-weld compiler for the weight-two 2B Tate quotient

The source-native weight-two norm map has the shape

  M_minus(98304) -> C_common(98280) ⊕ Sym2(24)(300).

The preferred proof path is now fully map-coupled:

* actual common/residual projections plus injectivity of their paired norm map;
* a `LinearRankRigidityReceipt` attaching the 24/98280 squeeze to the actual
  residual map;
* the actual common target finrank 98280;
* uniqueness of the nonzero 24 -> Sym2(24) equivariant Hom line;
* a literal equivalence from the residual cokernel to the exterior model.

These data force the common kernel equivalence, force the actual residual map
to be Frobenius, cancel the common block on literal cokernels, and generate the
full Tate/exterior same-object equivalence.  No separate common-lane,
nonzeroness, or full-cokernel identity hypothesis remains.
-/

namespace Integration.OggSSP2BNormWeldCompiler

namespace Rank := Integration.OggSSP2BTateCokernelRankRigidity
namespace Kernel := Integration.OggSSP2BCommonLaneKernelWeld

/-- Proof-bearing version of the runtime statement that `frobenius` is the
unique nonzero equivariant map in the relevant Hom space. -/
structure UniqueNonzeroMapReceipt
    {R V S : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V]
    [AddCommMonoid S] [Module R S]
    (frobenius : V →ₗ[R] S) : Prop where
  frobenius_ne_zero : frobenius ≠ 0
  unique_nonzero : ∀ f : V →ₗ[R] S, f ≠ 0 → f = frobenius

/-- Compatibility theorem when nonzeroness is already supplied. -/
theorem residualMapForcedFrobenius
    {R V S : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V]
    [AddCommMonoid S] [Module R S]
    (residual frobenius : V →ₗ[R] S)
    (hunique : UniqueNonzeroMapReceipt frobenius)
    (hresidual : residual ≠ 0) :
    residual = frobenius :=
  hunique.unique_nonzero residual hresidual

/-- Preferred Frobenius compiler: rank 24 of the actual map already proves it
is nonzero, so no separate nonzeroness input is needed. -/
theorem residualMapForcedFrobeniusFromRank
    {K V S : Type*}
    [DivisionRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup S] [Module K S] [FiniteDimensional K S]
    (residual frobenius : V →ₗ[K] S)
    (hunique : UniqueNonzeroMapReceipt frobenius)
    (hrank : Rank.LinearRankRigidityReceipt residual) :
    residual = frobenius :=
  hunique.unique_nonzero residual hrank.residual_ne_zero

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

/-- Compatibility first-stage compiler from an already assembled kernel weld. -/
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
    (residualMapIsFrobenius : Prop)
    (hresidual : residualMapIsFrobenius)
    (residualExterior : (S ⧸ kernelData.residualRange) ≃ₗ[K] E) :
    NormWeldReceipt :=
  compileNormWeld
    (Nonempty (kernelData.residualProjection.ker ≃ₗ[K] C))
    kernelData.commonLaneSameObjectPaid
    rankReceipt
    residualMapIsFrobenius hresidual
    (Nonempty (((C × S) ⧸ kernelData.normRange) ≃ₗ[K] E))
    ⟨tateCokernelEquivFromResidual kernelData residualExterior⟩

/-- Strongest map-level compiler.  From actual projections, map-coupled rank,
Hom-line uniqueness and the residual quotient equivalence, it derives every
previous norm-weld proposition automatically. -/
noncomputable def compileNormWeldFromActualMaps
    {K M C S E : Type*}
    [DivisionRing K]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup S] [Module K S] [FiniteDimensional K S]
    [AddCommGroup E] [Module K E]
    (common : M →ₗ[K] C)
    (residual frobenius : M →ₗ[K] S)
    (paired_injective : Function.Injective (fun x : M => (common x, residual x)))
    (hrank : Rank.LinearRankRigidityReceipt residual)
    (hcommonFinrank : Module.finrank K C = 98280)
    (hunique : UniqueNonzeroMapReceipt frobenius)
    (residualExterior :
      (S ⧸ residual.range) ≃ₗ[K] E) :
    NormWeldReceipt := by
  let kd := kernelWeldDataFromActualMaps common residual paired_injective
    hrank hcommonFinrank
  have hresidual : residual = frobenius :=
    residualMapForcedFrobeniusFromRank residual frobenius hunique hrank
  exact compileNormWeldFromResidualEquiv
    kd hrank.numeric (residual = frobenius) hresidual residualExterior

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
