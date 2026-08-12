import Mathlib
import AgdaMirror.KernelMonoid
import AgdaMirror.OperatorTypes
import AgdaMirror.LensKernel

/-!
# Lean mirror of `DASHI/Core/UniversalOperatorBasis.agda` (genuine, fully proved)

Now assemblable since the kernel-monoid / operator / lens parts are mirrored.
The universal operator basis bundles a collapse (projection) kernel, a refinement
(regularizer) kernel, a coordinate-transport kernel with a lens invariant, and a
`T = C ∘ P ∘ R` operator scaffold whose components agree with those kernels.

The genuine content is the *generated kernel*
`collapse ∘ (coordinateTransport ∘ refinement)` together with the inherited
composition monoid laws and the proof that the scaffold's `T` agrees with the
generated kernel (`generated_agrees_with_stack`).
-/

namespace AgdaMirror.OperatorBasis

open AgdaMirror.KernelMonoid
open AgdaMirror.OperatorTypes
open AgdaMirror.LensKernel

variable {S : Type}

/-- The `T = C ∘ P ∘ R` operator scaffold (mirror of `DASHI.Physics.TOperator`). -/
structure TOperator (S : Type) where
  C : S → S
  P : S → S
  R : S → S

/-- The composite `T = C ∘ (P ∘ R)`. -/
def TOperator.T (op : TOperator S) : S → S := fun x => op.C (op.P (op.R x))

/-- The universal operator basis. -/
structure UniversalOperatorBasis (S : Type) where
  collapse : Kernel S
  collapseProjection : Projection collapse.K
  refinement : Kernel S
  refinementRegularizer : Regularizer refinement.K
  coordinateTransport : Kernel S
  observable : Type
  observation : Lens S observable
  transportInvariant : LensInvariant observation coordinateTransport.K
  stack : TOperator S
  stack_collapse : ∀ x, stack.C x = collapse.K x
  stack_projection : ∀ x, stack.P x = coordinateTransport.K x
  stack_refinement : ∀ x, stack.R x = refinement.K x

/-- The generated kernel `collapse ∘ (coordinateTransport ∘ refinement)`. -/
def generatedKernel (B : UniversalOperatorBasis S) : Kernel S :=
  comp B.collapse (comp B.coordinateTransport B.refinement)

/-- The scaffold's `T` agrees with the generated kernel. -/
theorem generated_agrees_with_stack (B : UniversalOperatorBasis S) (x : S) :
    B.stack.T x = (generatedKernel B).K x := by
  simp [TOperator.T, generatedKernel, comp, B.stack_collapse, B.stack_projection,
    B.stack_refinement]

/-! ### Inherited composition monoid laws -/

/-- Kernel composition. -/
def compose : Kernel S → Kernel S → Kernel S := comp

/-- The identity kernel. -/
def identityK : Kernel S := idK

theorem composition_assoc (A B C : Kernel S) :
    KernelEq (compose (compose A B) C) (compose A (compose B C)) :=
  compose_assoc A B C

theorem composition_left_id (A : Kernel S) : KernelEq (compose identityK A) A :=
  left_id A

theorem composition_right_id (A : Kernel S) : KernelEq (compose A identityK) A :=
  right_id A

end AgdaMirror.OperatorBasis
