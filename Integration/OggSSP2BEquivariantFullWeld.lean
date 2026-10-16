import Integration.OggSSP2BEquivariantCokernelCancellation
import Integration.OggSSP2BResidualExteriorQuotient

/-!
# Full Tate/exterior weld equivariance from its canonical components

The literal full weld is the composition

  full Tate cokernel
    -- common-lane cancellation --> residual cokernel
    -- residual model quotient --> exterior/duad 276.

The first arrow is automatically equivariant by
`OggSSP2BEquivariantCokernelCancellation`.  Consequently full-weld
equivariance is compiler output once the canonical residual quotient
`Sym²(24)/Frob(24) ≃ Λ²(24)` intertwines the chosen model action.

This is the exact factorization used by the finite Co1 screen: the quotient
matrices on off-diagonal monomials are checked generator-by-generator to equal
the exterior-square matrices.  This owner does not promote a runtime result by
itself; it owns only the generic composition theorem.
-/

namespace Integration.OggSSP2BEquivariantFullWeld

namespace K := Integration.OggSSP2BCommonLaneKernelWeld
namespace Eqv := Integration.OggSSP2BEquivariantRangeInvariant
namespace Cancel := Integration.OggSSP2BEquivariantCokernelCancellation
namespace RQ := Integration.OggSSP2BResidualExteriorQuotient

/-- Machine-readable frontier bit. -/
def fullWeldEquivarianceIsCompilerOutput : Bool := true

variable {𝕜 G M C S E : Type*}
  [DivisionRing 𝕜]
  [AddCommGroup M] [Module 𝕜 M] [FiniteDimensional 𝕜 M]
  [AddCommGroup C] [Module 𝕜 C] [FiniteDimensional 𝕜 C]
  [AddCommGroup S] [Module 𝕜 S] [FiniteDimensional 𝕜 S]
  [AddCommGroup E] [Module 𝕜 E]

/-- Proof-relevant model-side statement that the residual quotient equivalence
intertwines the residual quotient action with the exterior action. -/
structure ResidualExteriorEquivariantReceipt
    (d : K.KernelWeldData (K := 𝕜) (M := M) (C := C) (S := S))
    (r : RQ.ResidualExteriorReceipt (E := E) d)
    (actResidual : G → (S ⧸ d.residualRange) →ₗ[𝕜] (S ⧸ d.residualRange))
    (actE : G → E →ₗ[𝕜] E) : Prop where
  intertwines : ∀ g q,
    r.residualQuotientEquiv (actResidual g q) =
      actE g (r.residualQuotientEquiv q)

namespace K.KernelWeldData

variable (d : K.KernelWeldData (K := 𝕜) (M := M) (C := C) (S := S))

/-- The composite full Tate/exterior equivalence is equivariant whenever the
source norm/residual coordinates are equivariant, `snd` intertwines the split
target actions, and the canonical residual exterior quotient intertwines its
model action. -/
theorem fullCokernelEquiv_equivariant
    (r : RQ.ResidualExteriorReceipt (E := E) d)
    (actM : G → M →ₗ[𝕜] M)
    (actCS : G → (C × S) →ₗ[𝕜] (C × S))
    (actS : G → S →ₗ[𝕜] S)
    (actE : G → E →ₗ[𝕜] E)
    (hnorm : Eqv.LinearEquivariant actM actCS d.normMap)
    (hresidual : Eqv.LinearEquivariant actM actS d.residualProjection)
    (hsnd : Eqv.LinearEquivariant actCS actS (LinearMap.snd 𝕜 C S))
    (hmodel : ResidualExteriorEquivariantReceipt d r
      (fun g => d.residualQuotientAction actS
        (d.residualRange_stable_of_equivariant actM actS hresidual) g)
      actE) :
    ∀ g z,
      r.fullCokernelEquiv d
        (d.fullQuotientAction actCS
          (d.normRange_stable_of_equivariant actM actCS hnorm) g z) =
      actE g (r.fullCokernelEquiv d z) := by
  intro g z
  change r.residualQuotientEquiv
      (d.cokernelEquivResidualCokernel
        (d.fullQuotientAction actCS
          (d.normRange_stable_of_equivariant actM actCS hnorm) g z)) =
    actE g
      (r.residualQuotientEquiv (d.cokernelEquivResidualCokernel z))
  rw [d.cokernelEquivResidualCokernel_equivariant actCS actS
    (d.normRange_stable_of_equivariant actM actCS hnorm)
    (d.residualRange_stable_of_equivariant actM actS hresidual) hsnd g z]
  exact hmodel.intertwines g (d.cokernelEquivResidualCokernel z)

end K.KernelWeldData

end Integration.OggSSP2BEquivariantFullWeld
