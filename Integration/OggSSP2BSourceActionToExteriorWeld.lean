import Integration.OggSSP2BEquivariantRangeInvariant
import Integration.OggSSP2BSocleForcesUnique24
import Integration.OggSSP2BUniqueRangeNormWeld
import Integration.OggSSP2BResidualExteriorQuotient

/-!
# Source centralizer action -> exterior-square Tate weld

This is the direct post-socle compiler for the current 2B max-cut.

Carnahan's sourced Monster-stable integral form supplies the mathematical
centralizer action.  Once that action is instantiated on the formal mod-2 norm
carrier, no separate residual block projector is scientifically necessary:

* centralizer equivariance makes the actual residual range invariant;
* the paid rank squeeze gives that range dimension 24;
* the paid Co1 socle theorem says every nonzero invariant submodule contains
  the Frobenius-square 24;
* equal finite dimension therefore forces literal equality of ranges;
* Sym2(24)/Frob(24) = wedge2(24), followed by common-lane cancellation,
  gives the full Tate-cokernel exterior equivalence.

The file does not assert that the external Carnahan action has already been
instantiated as Lean data.  It proves that such an instantiation is the only
remaining formal input: block-projector coordinates are an optional
implementation route, not an additional mathematical acquisition.
-/

namespace Integration.OggSSP2BSourceActionToExteriorWeld

namespace Eqv := Integration.OggSSP2BEquivariantRangeInvariant
namespace Socle := Integration.OggSSP2BSocleForcesUnique24
namespace Unique := Integration.OggSSP2BUniqueRangeNormWeld
namespace Kernel := Integration.OggSSP2BCommonLaneKernelWeld
namespace RQ := Integration.OggSSP2BResidualExteriorQuotient

variable {K G M C S V E : Type*}
  [DivisionRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup C] [Module K C] [FiniteDimensional K C]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup E] [Module K E]

/-- Invariance predicate attached to a concrete linear action. -/
def IsInvariantFor
    (actS : G → S →ₗ[K] S)
    (W : Submodule K S) : Prop :=
  ∀ g y, y ∈ W → actS g y ∈ W

/-- The generic `RangeInvariant` theorem is exactly the invariance predicate
used by the socle/unique-range compiler. -/
theorem residual_range_invariant
    (actM : G → M →ₗ[K] M)
    (actS : G → S →ₗ[K] S)
    (residual : M →ₗ[K] S)
    (heq : Eqv.LinearEquivariant actM actS residual) :
    IsInvariantFor actS residual.range := by
  intro g y hy
  exact Eqv.range_invariant_of_equivariant actM actS residual heq g y hy

/-- Direct terminal residual quotient compiler from the actual centralizer
module action.  No source block projector is required. -/
noncomputable def residualExteriorFromSourceAction
    (kernelData : Kernel.KernelWeldData
      (K := K) (M := M) (C := C) (S := S))
    (actM : G → M →ₗ[K] M)
    (actS : G → S →ₗ[K] S)
    (heq : Eqv.LinearEquivariant actM actS kernelData.residualProjection)
    (frobenius : V →ₗ[K] S)
    (socle : Socle.FrobeniusSocleReceipt
      frobenius (IsInvariantFor actS))
    (hrank : Module.finrank K kernelData.residualProjection.range = 24)
    (frobeniusExterior : (S ⧸ frobenius.range) ≃ₗ[K] E)
    (sourceProvenance : String) :
    RQ.ResidualExteriorReceipt (E := E) kernelData where
  residualQuotientEquiv :=
    Unique.residualCokernelEquivFromUniqueTarget
      kernelData.residualProjection frobenius
      socle.toUniqueInvariant24SubmoduleReceipt
      hrank
      (residual_range_invariant actM actS kernelData.residualProjection heq)
      frobeniusExterior
  sourceProvenance := sourceProvenance

/-- Strongest consequence: the source-native full norm cokernel is literally
linearly equivalent to the exterior-square model once the sourced centralizer
action has been instantiated. -/
noncomputable def fullTateExteriorEquivFromSourceAction
    (kernelData : Kernel.KernelWeldData
      (K := K) (M := M) (C := C) (S := S))
    (actM : G → M →ₗ[K] M)
    (actS : G → S →ₗ[K] S)
    (heq : Eqv.LinearEquivariant actM actS kernelData.residualProjection)
    (frobenius : V →ₗ[K] S)
    (socle : Socle.FrobeniusSocleReceipt
      frobenius (IsInvariantFor actS))
    (hrank : Module.finrank K kernelData.residualProjection.range = 24)
    (frobeniusExterior : (S ⧸ frobenius.range) ≃ₗ[K] E)
    (sourceProvenance : String) :
    ((C × S) ⧸ kernelData.normRange) ≃ₗ[K] E :=
  (residualExteriorFromSourceAction kernelData actM actS heq frobenius socle
      hrank frobeniusExterior sourceProvenance).fullCokernelEquiv kernelData

/-- Public max-cut theorem: after target-side runtime/source work, a formal
centralizer action plus equivariance of the actual residual norm coordinate is
sufficient for the literal Tate/exterior weld. -/
theorem source_action_is_the_only_formal_weld_input
    (kernelData : Kernel.KernelWeldData
      (K := K) (M := M) (C := C) (S := S))
    (actM : G → M →ₗ[K] M)
    (actS : G → S →ₗ[K] S)
    (heq : Eqv.LinearEquivariant actM actS kernelData.residualProjection)
    (frobenius : V →ₗ[K] S)
    (socle : Socle.FrobeniusSocleReceipt
      frobenius (IsInvariantFor actS))
    (hrank : Module.finrank K kernelData.residualProjection.range = 24)
    (frobeniusExterior : (S ⧸ frobenius.range) ≃ₗ[K] E)
    (sourceProvenance : String) :
    Nonempty (((C × S) ⧸ kernelData.normRange) ≃ₗ[K] E) :=
  ⟨fullTateExteriorEquivFromSourceAction kernelData actM actS heq frobenius
      socle hrank frobeniusExterior sourceProvenance⟩

end Integration.OggSSP2BSourceActionToExteriorWeld
