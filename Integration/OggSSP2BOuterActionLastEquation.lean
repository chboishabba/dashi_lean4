import Integration.OggSSP2BNormToStableCompletion
import Integration.OggSSP2BTateCoordinateChoiceCompiler

/-!
# The terminal outer-action same-object equation

After the source-action norm weld identifies the actual Tate cokernel with the
exterior/duad model, there is no need to discover a second exterior action.
Transport the already-paid finite-model outer operator back through the literal
cokernel equivalence.  The only remaining C' statement is then equality of
that transported operator with the actual operator induced by the sourced
Monster-centralizer element on the same cokernel.

Thus the final same-object action leaf is one equation

  g_actual_cokernel = e.symm * g_model * e.

Once this equation is supplied, the existing vertical-weld and stable-model
compilers produce the actual Tate Q10 and Completion10 action automatically.
No arbitrary coordinate choice is involved: repository coordinates are chosen
noncanonically from finrank 276 and the operator is transported by conjugation.
-/

namespace Integration.OggSSP2BOuterActionLastEquation

namespace N := Integration.OggSSP2BNormToStableCompletion
namespace C := Integration.OggSSP2BTateCoordinateChoiceCompiler
namespace K := Integration.OggSSP2BCommonLaneKernelWeld
namespace RQ := Integration.OggSSP2BResidualExteriorQuotient
namespace T := Integration.OggSSP2BStableCompletionModelTransport

abbrev Scalar := N.Scalar
abbrev ActualTate276 := N.ActualTate276

variable {M Cmn S E Q : Type*}
  [AddCommGroup M] [Module Scalar M] [FiniteDimensional Scalar M]
  [AddCommGroup Cmn] [Module Scalar Cmn] [FiniteDimensional Scalar Cmn]
  [AddCommGroup S] [Module Scalar S] [FiniteDimensional Scalar S]
  [AddCommGroup E] [Module Scalar E]
  [AddCommGroup Q] [Module Scalar Q]

/-- Pull the concrete exterior/duad model operator back to the actual
source-native Tate cokernel. -/
noncomputable def transportedModelOuterOnCokernel
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := Cmn) (S := S))
    (residual : RQ.ResidualExteriorReceipt (E := E) kernelData)
    (modelOuter : E →ₗ[Scalar] E) :
    ((Cmn × S) ⧸ kernelData.normRange) →ₗ[Scalar]
      ((Cmn × S) ⧸ kernelData.normRange) :=
  (residual.fullCokernelEquiv kernelData).symm.toLinearMap.comp
    (modelOuter.comp (residual.fullCokernelEquiv kernelData).toLinearMap)

/-- By construction, the full cokernel equivalence intertwines the transported
operator with the model operator. -/
theorem transportedModelOuter_intertwines
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := Cmn) (S := S))
    (residual : RQ.ResidualExteriorReceipt (E := E) kernelData)
    (modelOuter : E →ₗ[Scalar] E)
    (z : ((Cmn × S) ⧸ kernelData.normRange)) :
    residual.fullCokernelEquiv kernelData
      (transportedModelOuterOnCokernel kernelData residual modelOuter z)
      = modelOuter (residual.fullCokernelEquiv kernelData z) := by
  simp [transportedModelOuterOnCokernel]

/-- The exterior-action receipt is therefore compiler data, not a new source
acquisition. -/
noncomputable def exteriorActionFromModel
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := Cmn) (S := S))
    (residual : RQ.ResidualExteriorReceipt (E := E) kernelData)
    (modelOuter : E →ₗ[Scalar] E)
    (sourceProvenance : String) :
    N.ExteriorActionReceipt kernelData residual modelOuter where
  cokernelOuterOperator :=
    transportedModelOuterOnCokernel kernelData residual modelOuter
  outer_intertwining :=
    transportedModelOuter_intertwines kernelData residual modelOuter
  sourceProvenance := sourceProvenance

/-- Exact terminal same-object datum: the actual cokernel operator from the
sourced Monster-centralizer action equals the operator transported from the
finite exterior/duad model. -/
structure ActualCokernelOuterMatchesModelReceipt
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := Cmn) (S := S))
    (residual : RQ.ResidualExteriorReceipt (E := E) kernelData)
    (model : T.ModelStableCompletionReceipt E Q) where
  actualCokernelOuterOperator :
    ((Cmn × S) ⧸ kernelData.normRange) →ₗ[Scalar]
      ((Cmn × S) ⧸ kernelData.normRange)
  action_eq_transported_model :
    actualCokernelOuterOperator =
      transportedModelOuterOnCokernel kernelData residual model.outerOperator
  actualOuterOperatorSourced : Bool
  sourceProvenance : String

/-- Coordinate choice and exterior-action packaging are automatic once the
single cokernel action equation is known. -/
noncomputable def verticalWeldFromLastEquation
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := Cmn) (S := S))
    (residual : RQ.ResidualExteriorReceipt (E := E) kernelData)
    (model : T.ModelStableCompletionReceipt E Q)
    (hfinrank :
      Module.finrank Scalar ((Cmn × S) ⧸ kernelData.normRange) = 276)
    (last : ActualCokernelOuterMatchesModelReceipt kernelData residual model)
    (sourceProvenance : String) :
    N.VerticalWeldReceipt kernelData residual model := by
  let tateCoordinates :=
    C.coordinateReceiptOfFinrank kernelData hfinrank
      last.actualCokernelOuterOperator last.actualOuterOperatorSourced
      last.sourceProvenance
  let exteriorAction :=
    exteriorActionFromModel kernelData residual model.outerOperator
      sourceProvenance
  refine
    { tateCoordinates := tateCoordinates
      exteriorAction := exteriorAction
      sameCokernelOuter := ?_
      sourceProvenance := sourceProvenance }
  exact last.action_eq_transported_model

/-- Consequently the single action equality already generates the actual
stable Tate Q10 with the Completion10 outer action. -/
noncomputable def actualStableCompletionFromLastEquation
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := Cmn) (S := S))
    (residual : RQ.ResidualExteriorReceipt (E := E) kernelData)
    (model : T.ModelStableCompletionReceipt E Q)
    (hfinrank :
      Module.finrank Scalar ((Cmn × S) ⧸ kernelData.normRange) = 276)
    (last : ActualCokernelOuterMatchesModelReceipt kernelData residual model)
    (sourceProvenance : String) :
    Integration.OggSSP2BActualStableCompletionSubquotient.StableCompletionSubquotientReceipt Q :=
  (verticalWeldFromLastEquation kernelData residual model hfinrank last
    sourceProvenance).toActualStableCompletion kernelData residual model

end Integration.OggSSP2BOuterActionLastEquation
