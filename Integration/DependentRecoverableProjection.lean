import Mathlib

/-!
# Dependent recoverable projection

Lean mirror of the Agda dependent recoverable projection core.

A coarse projection may require a residual type that depends on the coarse
state. The exact code is the dependent sum Sigma y, Residual y, and exact
reopening implies the code is separating.
-/

namespace Integration.DependentRecoverableProjection

structure Projection (X Y : Type) where
  Residual : Y → Type
  project : X → Y
  residual : (x : X) → Residual (project x)
  reopen : (y : Y) → Residual y → X
  reopen_exact :
    ∀ x, reopen (project x) (residual x) = x

abbrev Code {X Y : Type} (P : Projection X Y) :=
  Sigma P.Residual

def encode {X Y : Type} (P : Projection X Y) (x : X) : Code P :=
  ⟨P.project x, P.residual x⟩

def decode {X Y : Type} (P : Projection X Y) : Code P → X
  | ⟨y, r⟩ => P.reopen y r

theorem decode_encode {X Y : Type} (P : Projection X Y) (x : X) :
    decode P (encode P x) = x :=
  P.reopen_exact x

theorem encode_injective {X Y : Type} (P : Projection X Y) :
    Function.Injective (encode P) := by
  intro x y h
  have h' := congrArg (decode P) h
  rw [decode_encode, decode_encode] at h'
  exact h'

structure UniformProjection (X Y : Type) where
  Residual : Type
  project : X → Y
  residual : X → Residual
  reopen : Y → Residual → X
  reopen_exact :
    ∀ x, reopen (project x) (residual x) = x

def UniformProjection.asDependent
    {X Y : Type} (P : UniformProjection X Y) :
    Projection X Y where
  Residual := fun _ => P.Residual
  project := P.project
  residual := P.residual
  reopen := P.reopen
  reopen_exact := P.reopen_exact

structure Boundary where
  residualMayDependOnCoarseState : Bool
  exactReconstructionAvailable : Bool
  dependentCodeSeparating : Bool
  uniformResidualIsSpecialCase : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  residualMayDependOnCoarseState := true
  exactReconstructionAvailable := true
  dependentCodeSeparating := true
  uniformResidualIsSpecialCase := true

end Integration.DependentRecoverableProjection
