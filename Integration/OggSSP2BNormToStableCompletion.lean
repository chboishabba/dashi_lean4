import Integration.OggSSP2BResidualExteriorQuotient
import Integration.OggSSP2BStableCompletionModelTransport

/-!
# Terminal equivariant norm-cokernel -> actual Tate Completion10 compiler

The source-native vertical weld passes through three literal models:

  ActualTate276
      ≃  coker(actual plus/minus norm)
      ≃  residual/Frobenius quotient
      ≃  exterior-square / duad model.

A vector-space equivalence alone is insufficient: the sourced outer M22:2
action must commute with both model changes.  This owner therefore requires
both equivariance squares and composes them into the preferred
`EquivariantModelWeldReceipt`.  The already-built stable-model transporter then
constructs the actual Tate N<=S quotient and Completion10 action automatically.
-/

namespace Integration.OggSSP2BNormToStableCompletion

namespace A := Integration.OggSSP2BActualStableCompletionSubquotient
namespace K := Integration.OggSSP2BCommonLaneKernelWeld
namespace RQ := Integration.OggSSP2BResidualExteriorQuotient
namespace T := Integration.OggSSP2BStableCompletionModelTransport

abbrev Scalar := A.Scalar
abbrev ActualTate276 := A.ActualTate276

variable {M C S E Q : Type*}
  [AddCommGroup M] [Module Scalar M] [FiniteDimensional Scalar M]
  [AddCommGroup C] [Module Scalar C] [FiniteDimensional Scalar C]
  [AddCommGroup S] [Module Scalar S] [FiniteDimensional Scalar S]
  [AddCommGroup E] [Module Scalar E]
  [AddCommGroup Q] [Module Scalar Q]

/-- Same-object coordinate chart from the repo's actual Tate carrier to the
literal source-native norm cokernel, including the actual sourced outer action
and its action on the cokernel. -/
structure TateCokernelCoordinateReceipt
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := C) (S := S)) where
  coordinateEquiv :
    ActualTate276 ≃ₗ[Scalar] ((C × S) ⧸ kernelData.normRange)
  actualOuterOperator : ActualTate276 →ₗ[Scalar] ActualTate276
  cokernelOuterOperator :
    ((C × S) ⧸ kernelData.normRange) →ₗ[Scalar]
      ((C × S) ⧸ kernelData.normRange)
  outer_intertwining : ∀ x,
    coordinateEquiv (actualOuterOperator x) =
      cokernelOuterOperator (coordinateEquiv x)
  actualOuterOperatorSourced : Bool
  sourceProvenance : String

/-- Equivariance of the literal full-cokernel -> exterior/duad equivalence with
the concrete model outer operator. -/
structure ExteriorActionReceipt
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := C) (S := S))
    (residual : RQ.ResidualExteriorReceipt
      (E := E) kernelData)
    (modelOuter : E →ₗ[Scalar] E) where
  cokernelOuterOperator :
    ((C × S) ⧸ kernelData.normRange) →ₗ[Scalar]
      ((C × S) ⧸ kernelData.normRange)
  outer_intertwining : ∀ z,
    residual.fullCokernelEquiv kernelData (cokernelOuterOperator z) =
      modelOuter (residual.fullCokernelEquiv kernelData z)
  sourceProvenance : String

/-- Complete vertical weld data.  It contains no arbitrary same-object Boolean:
every model transition is an actual linear equivalence and every outer-action
transition is an explicit intertwining equation. -/
structure VerticalWeldReceipt
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := C) (S := S))
    (residual : RQ.ResidualExteriorReceipt
      (E := E) kernelData)
    (model : T.ModelStableCompletionReceipt E Q) where
  tateCoordinates : TateCokernelCoordinateReceipt kernelData
  exteriorAction : ExteriorActionReceipt kernelData residual model.outerOperator
  sameCokernelOuter :
    tateCoordinates.cokernelOuterOperator = exteriorAction.cokernelOuterOperator
  sourceProvenance : String

namespace VerticalWeldReceipt

variable
  (kernelData : K.KernelWeldData
    (K := Scalar) (M := M) (C := C) (S := S))
  (residual : RQ.ResidualExteriorReceipt (E := E) kernelData)
  (model : T.ModelStableCompletionReceipt E Q)
  (w : VerticalWeldReceipt kernelData residual model)

/-- Compose the two literal model equivalences. -/
noncomputable def tateToModel : ActualTate276 ≃ₗ[Scalar] E :=
  w.tateCoordinates.coordinateEquiv.trans
    (residual.fullCokernelEquiv kernelData)

/-- The composed equivalence intertwines the sourced actual Tate outer action
with the concrete exterior/duad model action. -/
theorem tateToModel_outer_intertwining (x : ActualTate276) :
    w.tateToModel kernelData residual model
        (w.tateCoordinates.actualOuterOperator x)
      = model.outerOperator (w.tateToModel kernelData residual model x) := by
  change residual.fullCokernelEquiv kernelData
      (w.tateCoordinates.coordinateEquiv
        (w.tateCoordinates.actualOuterOperator x))
    = model.outerOperator
        (residual.fullCokernelEquiv kernelData
          (w.tateCoordinates.coordinateEquiv x))
  rw [w.tateCoordinates.outer_intertwining]
  rw [w.sameCokernelOuter]
  exact w.exteriorAction.outer_intertwining
    (w.tateCoordinates.coordinateEquiv x)

/-- Package the composed map as the preferred equivariant stable-model weld. -/
noncomputable def toEquivariantModelWeld :
    T.EquivariantModelWeldReceipt E model.outerOperator where
  equivalence := w.tateToModel kernelData residual model
  actualOuterOperator := w.tateCoordinates.actualOuterOperator
  outer_intertwining := w.tateToModel_outer_intertwining kernelData residual model
  actualOuterOperatorSourced := w.tateCoordinates.actualOuterOperatorSourced
  sourceProvenance :=
    w.tateCoordinates.sourceProvenance ++ "; " ++
    residual.sourceProvenance ++ "; " ++
    w.exteriorAction.sourceProvenance ++ "; " ++
    w.sourceProvenance

/-- Terminal B'+C' acquisition: the actual Tate stable ten-dimensional quotient
and Completion10 outer action are generated from the norm-cokernel weld. -/
noncomputable def toActualStableCompletion :
    A.StableCompletionSubquotientReceipt Q :=
  model.transportEquivariantlyToActualTate
    (w.toEquivariantModelWeld kernelData residual model)

/-- B' is now a theorem of the vertical-weld receipt. -/
theorem actual_selected_finrank_ten :
    Module.finrank Scalar Q = 10 :=
  (w.toActualStableCompletion kernelData residual model).target_finrank

/-- C' is on the same quotient and intertwines the repo-native Completion flip. -/
theorem actual_outer_action_is_completion (q : Q) :
    let r := w.toActualStableCompletion kernelData residual model
    r.completionChart (r.quotientOuterOperator q) =
      Integration.OggSSP2BRevisedCompletionRecognition.completionFlipLinear
        (r.completionChart q) := by
  simpa using model.completion_intertwining q

end VerticalWeldReceipt

end Integration.OggSSP2BNormToStableCompletion
