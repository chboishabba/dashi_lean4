import Mathlib.LinearAlgebra.Dimension.Free
import Integration.OggSSP2BNormToStableCompletion

/-!
# Coordinate choice is not a same-object scientific gate

`ActualTate276` is the repository's fixed coordinate model `Fin 276 -> F2`.
Once the source-native Tate cokernel has been constructed as an abstract
276-dimensional vector space, choosing coordinates is mathematically arbitrary.
The outer action should therefore be transported by conjugation along any
linear equivalence rather than treated as an additional sourced recognition.

This file supplies exactly that adapter.  Equal finite dimension is enough to
construct a noncanonical linear equivalence by `LinearEquiv.ofFinrankEq`; the
outer operator is then transported by conjugation.  No distinguished basis and
no extra same-object source claim are required.
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

/-- The repository's fixed Tate coordinate model really has dimension 276. -/
theorem actualTate276_finrank : Module.finrank Scalar ActualTate276 = 276 := by
  simp [ActualTate276]

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

/-- Equal dimension is already enough to choose coordinates.  This removes
coordinate existence itself from the same-object roadmap. -/
noncomputable def coordinateEquivOfFinrank
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := C) (S := S))
    (hfinrank :
      Module.finrank Scalar ((C × S) ⧸ kernelData.normRange) = 276) :
    ActualTate276 ≃ₗ[Scalar] ((C × S) ⧸ kernelData.normRange) :=
  LinearEquiv.ofFinrankEq ActualTate276
    ((C × S) ⧸ kernelData.normRange) <| by
      calc
        Module.finrank Scalar ActualTate276 = 276 := actualTate276_finrank
        _ = Module.finrank Scalar ((C × S) ⧸ kernelData.normRange) := hfinrank.symm

/-- Strongest coordinate adapter: a finrank-276 theorem plus the abstract
cokernel action automatically yields the exact receipt consumed downstream. -/
noncomputable def coordinateReceiptOfFinrank
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := C) (S := S))
    (hfinrank :
      Module.finrank Scalar ((C × S) ⧸ kernelData.normRange) = 276)
    (cokernelOuterOperator :
      ((C × S) ⧸ kernelData.normRange) →ₗ[Scalar]
        ((C × S) ⧸ kernelData.normRange))
    (actualOuterOperatorSourced : Bool)
    (sourceProvenance : String) :
    N.TateCokernelCoordinateReceipt kernelData :=
  coordinateReceiptOfEquiv kernelData
    (coordinateEquivOfFinrank kernelData hfinrank)
    cokernelOuterOperator actualOuterOperatorSourced sourceProvenance

end Integration.OggSSP2BTateCoordinateChoiceCompiler
