import Integration.OggSSP2BCokernelCancellation
import Integration.OggSSP2BEquivariantRangeInvariant

/-!
# Common-lane cokernel cancellation is automatically equivariant

The literal cancellation

  (C × S) / range(norm)  ≃  S / range(residual)

is induced by the projection `snd : C × S → S`.  Therefore no independent
"equivariance of cancellation" theorem needs to be sourced.  If the full norm
and residual maps are equivariant and the residual projection `snd` intertwines
the target actions, their image submodules are invariant, the quotient actions
are canonically defined by `Submodule.mapQ`, and the cancellation equivalence
intertwines those quotient actions automatically.

This leaves equivariance of the residual model quotient
`Sym²(24)/Frob(24) ≃ Λ²(24)` as the only model-side component of full weld
equivariance.  The finite Co1 construction already tests that quotient action
generator-by-generator; this file owns only the generic compiler.
-/

namespace Integration.OggSSP2BEquivariantCokernelCancellation

namespace K := Integration.OggSSP2BCommonLaneKernelWeld
namespace Eqv := Integration.OggSSP2BEquivariantRangeInvariant

/-- Machine-readable status bit for downstream frontier owners. -/
def commonLaneCancellationEquivarianceIsCompilerOutput : Bool := true

variable {𝕜 G M C S : Type*}
  [DivisionRing 𝕜]
  [AddCommGroup M] [Module 𝕜 M] [FiniteDimensional 𝕜 M]
  [AddCommGroup C] [Module 𝕜 C] [FiniteDimensional 𝕜 C]
  [AddCommGroup S] [Module 𝕜 S] [FiniteDimensional 𝕜 S]

namespace K.KernelWeldData

variable (d : K.KernelWeldData (K := 𝕜) (M := M) (C := C) (S := S))

/-- Equivariance of the full norm map makes its range invariant. -/
theorem normRange_stable_of_equivariant
    (actM : G → M →ₗ[𝕜] M)
    (actCS : G → (C × S) →ₗ[𝕜] (C × S))
    (hnorm : Eqv.LinearEquivariant actM actCS d.normMap) :
    ∀ g, d.normRange ≤ d.normRange.comap (actCS g) := by
  intro g y hy
  exact Eqv.range_invariant_of_equivariant actM actCS d.normMap hnorm g y hy

/-- Equivariance of the residual coordinate makes its image invariant. -/
theorem residualRange_stable_of_equivariant
    (actM : G → M →ₗ[𝕜] M)
    (actS : G → S →ₗ[𝕜] S)
    (hresidual : Eqv.LinearEquivariant actM actS d.residualProjection) :
    ∀ g, d.residualRange ≤ d.residualRange.comap (actS g) := by
  intro g y hy
  exact Eqv.range_invariant_of_equivariant actM actS d.residualProjection
    hresidual g y hy

/-- Canonical action of one group element on the full norm cokernel. -/
def fullQuotientAction
    (actCS : G → (C × S) →ₗ[𝕜] (C × S))
    (hstable : ∀ g, d.normRange ≤ d.normRange.comap (actCS g))
    (g : G) :
    ((C × S) ⧸ d.normRange) →ₗ[𝕜] ((C × S) ⧸ d.normRange) :=
  d.normRange.mapQ d.normRange (actCS g) (hstable g)

/-- Canonical action of one group element on the residual cokernel. -/
def residualQuotientAction
    (actS : G → S →ₗ[𝕜] S)
    (hstable : ∀ g, d.residualRange ≤ d.residualRange.comap (actS g))
    (g : G) :
    (S ⧸ d.residualRange) →ₗ[𝕜] (S ⧸ d.residualRange) :=
  d.residualRange.mapQ d.residualRange (actS g) (hstable g)

/-- Projection-induced common-lane cancellation intertwines the canonical
quotient actions. -/
theorem cokernelToResidualCokernel_equivariant
    (actCS : G → (C × S) →ₗ[𝕜] (C × S))
    (actS : G → S →ₗ[𝕜] S)
    (hfull : ∀ g, d.normRange ≤ d.normRange.comap (actCS g))
    (hres : ∀ g, d.residualRange ≤ d.residualRange.comap (actS g))
    (hsnd : Eqv.LinearEquivariant actCS actS (LinearMap.snd 𝕜 C S)) :
    ∀ g q,
      d.cokernelToResidualCokernel
          (d.fullQuotientAction actCS hfull g q) =
        d.residualQuotientAction actS hres g
          (d.cokernelToResidualCokernel q) := by
  intro g q
  refine Submodule.Quotient.induction_on d.normRange q ?_
  intro p
  change d.residualRange.mkQ ((LinearMap.snd 𝕜 C S) (actCS g p)) =
    d.residualRange.mkQ (actS g ((LinearMap.snd 𝕜 C S) p))
  exact congrArg d.residualRange.mkQ (hsnd g p)

/-- The literal cancellation equivalence has the same intertwining property as
its underlying quotient map. -/
theorem cokernelEquivResidualCokernel_equivariant
    (actCS : G → (C × S) →ₗ[𝕜] (C × S))
    (actS : G → S →ₗ[𝕜] S)
    (hfull : ∀ g, d.normRange ≤ d.normRange.comap (actCS g))
    (hres : ∀ g, d.residualRange ≤ d.residualRange.comap (actS g))
    (hsnd : Eqv.LinearEquivariant actCS actS (LinearMap.snd 𝕜 C S)) :
    ∀ g q,
      d.cokernelEquivResidualCokernel
          (d.fullQuotientAction actCS hfull g q) =
        d.residualQuotientAction actS hres g
          (d.cokernelEquivResidualCokernel q) := by
  intro g q
  exact d.cokernelToResidualCokernel_equivariant actCS actS hfull hres hsnd g q

end K.KernelWeldData

end Integration.OggSSP2BEquivariantCokernelCancellation
