import Integration.OggSSP2BNormToStableCompletion

/-!
# Coordinate choice is not a same-object scientific gate

`ActualTate276` is the repository's fixed coordinate model `Fin 276 -> F2`.
Once the source-native Tate cokernel has been constructed as an abstract
276-dimensional vector space, choosing coordinates is mathematically arbitrary.
The outer action should therefore be transported by conjugation along any
linear equivalence rather than treated as an additional sourced recognition.

This file supplies exactly that adapter.  It does not produce the required
276-dimensional equivalence; it proves that any such coordinate choice carries
all operator data automatically and introduces no further equivariance theorem.
-/

namespace Integration.OggSSP2BTateCoordinateChoiceCompiler

namespace N := Integration.OggSSP2BNormToStableCompletion
namespace K := Integration.OggSSP2BCommonLaneKernelWeld

abbrev Scalar := N.Scalar
abbrev ActualTate276 := N.ActualTate276

variable {M C S : Type*}
  [AddCommGroup M] [Module Scalar M] [FiniteDimensional Scalar M]
  [AddCommGroup C] [Module Scalar C] [FiniteDimensional Scalar C]
  [AddCommGroup S] [Module Scalar S] [FiniteDimensional Scalar S]

/-- Conjugate a cokernel operator into the repository's fixed Tate coordinates. -/
noncomputable def conjugateToActualCoordinates
    {W : Type*} [AddCommGroup W] [Module Scalar W]
    (coord : ActualTate276 ≃ₗ[Scalar] W)
    (op : W →ₗ[Scalar] W) :
    ActualTate276 →ₗ[Scalar] ActualTate276 :=
  coord.symm.toLinearMap.comp (op.comp coord.toLinearMap)

/-- The chosen coordinate equivalence automatically intertwines the conjugated
operator with the original abstract operator. -/
theorem coordinate_intertwining
    {W : Type*} [AddCommGroup W] [Module Scalar W]
    (coord : ActualTate276 ≃ₗ[Scalar] W)
    (op : W →ₗ[Scalar] W)
    (x : ActualTate276) :
    coord (conjugateToActualCoordinates coord op x) = op (coord x) := by
  simp [conjugateToActualCoordinates]

/-- Build the exact coordinate receipt required by the vertical-weld compiler
from an arbitrary linear coordinate choice on the source-native cokernel. -/
noncomputable def coordinateReceiptOfEquiv
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := C) (S := S))
    (coord : ActualTate276 ≃ₗ[Scalar] ((C × S) ⧸ kernelData.normRange))
    (cokernelOuterOperator :
      ((C × S) ⧸ kernelData.normRange) →ₗ[Scalar]
        ((C × S) ⧸ kernelData.normRange))
    (actualOuterOperatorSourced : Bool)
    (sourceProvenance : String) :
    N.TateCokernelCoordinateReceipt kernelData where
  coordinateEquiv := coord
  actualOuterOperator :=
    conjugateToActualCoordinates coord cokernelOuterOperator
  cokernelOuterOperator := cokernelOuterOperator
  outer_intertwining := by
    intro x
    exact coordinate_intertwining coord cokernelOuterOperator x
  actualOuterOperatorSourced := actualOuterOperatorSourced
  sourceProvenance := sourceProvenance

/-- Nonconstructive convenience form: existence of a coordinate equivalence is
enough; no distinguished basis is needed. -/
noncomputable def coordinateReceiptOfNonemptyEquiv
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := C) (S := S))
    (hcoord : Nonempty
      (ActualTate276 ≃ₗ[Scalar] ((C × S) ⧸ kernelData.normRange)))
    (cokernelOuterOperator :
      ((C × S) ⧸ kernelData.normRange) →ₗ[Scalar]
        ((C × S) ⧸ kernelData.normRange))
    (actualOuterOperatorSourced : Bool)
    (sourceProvenance : String) :
    N.TateCokernelCoordinateReceipt kernelData :=
  coordinateReceiptOfEquiv kernelData (Classical.choice hcoord)
    cokernelOuterOperator actualOuterOperatorSourced sourceProvenance

end Integration.OggSSP2BTateCoordinateChoiceCompiler
