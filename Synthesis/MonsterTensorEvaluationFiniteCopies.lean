import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Tensor evaluation after finite-copy recognition

For a field `k`, module `H`, and finite index `Fin n`, mathlib's
`TensorProduct.piScalarRight` gives the canonical linear equivalence

  H ⊗[k] (Fin n -> k) ~= (Fin n -> H).

Therefore once an actual sector `W` has already been recognized as `n` copies of
`H`, the historical tensor-evaluation equivalence

  H ⊗[k] k^n ~= W

is generic finite-copy linear algebra.  It is not another Monster-specific
scientific input.  In the live H_zeta route the Schur compiler separately
identifies the multiplicity Hom carrier with `k^n`; transporting through that
coordinate equivalence yields the corresponding Hom-space evaluation model.

This owner does not construct the actual Monster isotypic equivalence.
-/

namespace Synthesis.MonsterTensorEvaluationFiniteCopies

noncomputable section

universe u

variable {k H W : Type u}
variable [Field k]
variable [AddCommGroup H] [Module k H]
variable [AddCommGroup W] [Module k W]

/-- Canonical tensor-to-finite-copies equivalence. -/
def tensorScalarsEquivFiniteCopies (n : ℕ) :
    H ⊗[k] (Fin n -> k) ≃ₗ[k] (Fin n -> H) :=
  TensorProduct.piScalarRight k k H (Fin n)

/-- Once `W` is actually recognized as `n` copies of `H`, tensor evaluation is
obtained by composing the canonical tensor/finite-copy equivalence with that
recognition. -/
def tensorScalarsEquivOfFiniteCopies {n : ℕ}
    (e : W ≃ₗ[k] (Fin n -> H)) :
    H ⊗[k] (Fin n -> k) ≃ₗ[k] W :=
  tensorScalarsEquivFiniteCopies (k := k) (H := H) n ≪≫ₗ e.symm

/-- The 90-copy specialization needed after actual Monster isotypy. -/
def tensorScalarsEquivNinety
    (e : W ≃ₗ[k] (Fin 90 -> H)) :
    H ⊗[k] (Fin 90 -> k) ≃ₗ[k] W :=
  tensorScalarsEquivOfFiniteCopies e

@[simp]
theorem tensorScalarsEquivFiniteCopies_tmul
    (n : ℕ) (x : H) (a : Fin n -> k) :
    tensorScalarsEquivFiniteCopies (k := k) (H := H) n (x ⊗ₜ a) =
      fun i => a i • x := by
  exact TensorProduct.piScalarRightHom_tmul k k H (Fin n) x a

structure Boundary where
  mathlibPiScalarRightConsumed : Bool
  tensorFiniteCopiesCompilerSourceWritten : Bool
  postIsotypyTensorEquivalenceSourceWritten : Bool
  ninetyTensorSpecializationSourceWritten : Bool
  tensorEquivalenceStillMonsterSpecificInput : Bool
  actualMonsterIsotypicEquivalencePaidHere : Bool
  actualMonsterHomCoordinateIdentificationPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  mathlibPiScalarRightConsumed := true
  tensorFiniteCopiesCompilerSourceWritten := true
  postIsotypyTensorEquivalenceSourceWritten := true
  ninetyTensorSpecializationSourceWritten := true
  tensorEquivalenceStillMonsterSpecificInput := false
  actualMonsterIsotypicEquivalencePaidHere := false
  actualMonsterHomCoordinateIdentificationPaidHere := false

end

end Synthesis.MonsterTensorEvaluationFiniteCopies
