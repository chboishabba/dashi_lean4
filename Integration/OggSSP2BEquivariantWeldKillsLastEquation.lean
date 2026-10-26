import Integration.OggSSP2BOuterActionLastEquation

/-!
# Equivariance kills the terminal outer-action equation

The previous max-cut exposed one literal equality on the source-native Tate
cokernel,

  g_actual = e⁻¹ ∘ g_model ∘ e.

That equality is not an independent scientific datum once the Tate/exterior
weld `e` is known to be equivariant for the same centralizer element.  This
owner makes that reduction explicit and packages the resulting receipt for the
existing terminal compiler.

Attribution boundary:
* the external Monster/centralizer action remains source-owned;
* the finite M22:2/duad outer operator remains ATLAS/AtlasRep-owned;
* DASHI owns the generic conjugation-from-intertwining compiler below.
-/

namespace Integration.OggSSP2BEquivariantWeldKillsLastEquation

namespace O := Integration.OggSSP2BOuterActionLastEquation
namespace K := Integration.OggSSP2BCommonLaneKernelWeld
namespace RQ := Integration.OggSSP2BResidualExteriorQuotient
namespace T := Integration.OggSSP2BStableCompletionModelTransport

/-- A linear equivalence that intertwines two operators automatically identifies
the source operator with conjugation of the target operator. -/
theorem operator_eq_conjugate_of_intertwining
    {K X Y : Type*}
    [DivisionRing K]
    [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    (e : X ≃ₗ[K] Y)
    (gx : X →ₗ[K] X)
    (gy : Y →ₗ[K] Y)
    (h : ∀ x, e (gx x) = gy (e x)) :
    gx = e.symm.toLinearMap.comp (gy.comp e.toLinearMap) := by
  ext x
  apply e.injective
  change e (gx x) = e (e.symm (gy (e x)))
  rw [h x]
  exact (e.apply_symm_apply (gy (e x))).symm

variable {M C S E Q : Type*}
  [AddCommGroup M] [Module O.Scalar M] [FiniteDimensional O.Scalar M]
  [AddCommGroup C] [Module O.Scalar C] [FiniteDimensional O.Scalar C]
  [AddCommGroup S] [Module O.Scalar S] [FiniteDimensional O.Scalar S]
  [AddCommGroup E] [Module O.Scalar E]
  [AddCommGroup Q] [Module O.Scalar Q]

/-- Compiler from an equivariant Tate/exterior weld to the exact receipt
consumed by `OggSSP2BOuterActionLastEquation`.  The literal action equality is
therefore downstream proof data, not a separate acquisition. -/
noncomputable def lastEquationFromEquivariance
    (kernelData : K.KernelWeldData
      (K := O.Scalar) (M := M) (C := C) (S := S))
    (residual : RQ.ResidualExteriorReceipt (E := E) kernelData)
    (model : T.ModelStableCompletionReceipt E Q)
    (actualOuter :
      ((C × S) ⧸ kernelData.normRange) →ₗ[O.Scalar]
        ((C × S) ⧸ kernelData.normRange))
    (hintertwines : ∀ z,
      residual.fullCokernelEquiv kernelData (actualOuter z) =
        model.outerOperator (residual.fullCokernelEquiv kernelData z))
    (actualOuterOperatorSourced : Bool)
    (sourceProvenance : String) :
    O.ActualCokernelOuterMatchesModelReceipt kernelData residual model where
  actualCokernelOuterOperator := actualOuter
  action_eq_transported_model :=
    operator_eq_conjugate_of_intertwining
      (residual.fullCokernelEquiv kernelData)
      actualOuter model.outerOperator hintertwines
  actualOuterOperatorSourced := actualOuterOperatorSourced
  sourceProvenance := sourceProvenance

/-- Public max-cut theorem: after an equivariant same-object weld, there is no
independent terminal operator-equality leaf. -/
theorem last_equation_is_not_independent
    (kernelData : K.KernelWeldData
      (K := O.Scalar) (M := M) (C := C) (S := S))
    (residual : RQ.ResidualExteriorReceipt (E := E) kernelData)
    (model : T.ModelStableCompletionReceipt E Q)
    (actualOuter :
      ((C × S) ⧸ kernelData.normRange) →ₗ[O.Scalar]
        ((C × S) ⧸ kernelData.normRange))
    (hintertwines : ∀ z,
      residual.fullCokernelEquiv kernelData (actualOuter z) =
        model.outerOperator (residual.fullCokernelEquiv kernelData z)) :
    actualOuter = O.transportedModelOuterOnCokernel
      kernelData residual model.outerOperator :=
  operator_eq_conjugate_of_intertwining
    (residual.fullCokernelEquiv kernelData)
    actualOuter model.outerOperator hintertwines

end Integration.OggSSP2BEquivariantWeldKillsLastEquation
