import RequestProject.QuantumMereologyInnerProductTPS

/-!
# Operator locality relative to a tensor-product structure

For a declared global complex-linear operator A and an inner-product TPS U, this
module makes the usual local-plus-interaction decomposition exact in TPS
coordinates:

  U⁻¹ A U = (A_L ⊗ I) + (I ⊗ A_R) + V.

This is a DASHI reconstruction theorem over mathlib tensor-map operators. It is
not by itself a Hamiltonian theorem: self-adjointness, unitary dynamics,
smallness/sparsity of V, quasiclassicality, and physical subsystem identity are
all separate obligations.
-/

namespace QuantumMereology

open scoped TensorProduct

namespace OperatorLocality

variable
  {H Left Right : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Left] [InnerProductSpace ℂ Left]
  [NormedAddCommGroup Right] [InnerProductSpace ℂ Right]

/-- Pull a global operator back to the tensor coordinates selected by the TPS. -/
def pullback
    (T : BipartiteInnerProductTPS H Left Right)
    (A : H →ₗ[ℂ] H) :
    TensorProduct ℂ Left Right →ₗ[ℂ] TensorProduct ℂ Left Right :=
  T.reconstruct.symm.toLinearEquiv.toLinearMap.comp
    (A.comp T.reconstruct.toLinearEquiv.toLinearMap)

/-- An exact local-left + local-right + interaction decomposition in TPS
coordinates. -/
structure Witness
    (T : BipartiteInnerProductTPS H Left Right)
    (A : H →ₗ[ℂ] H) where
  leftLocal : Left →ₗ[ℂ] Left
  rightLocal : Right →ₗ[ℂ] Right
  interaction :
    TensorProduct ℂ Left Right →ₗ[ℂ] TensorProduct ℂ Left Right
  decomposition :
    pullback T A =
      leftLocal.rTensor Right +
      rightLocal.lTensor Left +
      interaction

/-- The decomposition gives the expected exact action on pure tensors. -/
theorem apply_tmul
    {T : BipartiteInnerProductTPS H Left Right}
    {A : H →ₗ[ℂ] H}
    (W : Witness T A)
    (x : Left)
    (y : Right) :
    pullback T A (x ⊗ₜ[ℂ] y) =
      W.leftLocal x ⊗ₜ[ℂ] y +
      x ⊗ₜ[ℂ] W.rightLocal y +
      W.interaction (x ⊗ₜ[ℂ] y) := by
  rw [W.decomposition]
  simp [LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
    add_assoc]

/-- Interaction-free is a property of a particular operator relative to a
particular TPS, not a property of the bare Hilbert carrier. -/
def InteractionFree
    {T : BipartiteInnerProductTPS H Left Right}
    {A : H →ₗ[ℂ] H}
    (W : Witness T A) : Prop :=
  W.interaction = 0

theorem interactionFree_apply_tmul
    {T : BipartiteInnerProductTPS H Left Right}
    {A : H →ₗ[ℂ] H}
    (W : Witness T A)
    (hV : InteractionFree W)
    (x : Left)
    (y : Right) :
    pullback T A (x ⊗ₜ[ℂ] y) =
      W.leftLocal x ⊗ₜ[ℂ] y +
      x ⊗ₜ[ℂ] W.rightLocal y := by
  rw [apply_tmul W x y, hV]
  simp

structure Boundary where
  operatorDecompositionImpliesSelfAdjointHamiltonian : Bool := false
  operatorDecompositionImpliesSmallInteraction : Bool := false
  operatorDecompositionSelectsPreferredTPS : Bool := false
  interactionFreeMeansPhysicalIndependence : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem decomposition_does_not_select_preferred_tps :
    canonicalBoundary.operatorDecompositionSelectsPreferredTPS = false := rfl

theorem decomposition_does_not_imply_self_adjoint_hamiltonian :
    canonicalBoundary.operatorDecompositionImpliesSelfAdjointHamiltonian = false := rfl

end OperatorLocality

def mathlibTensorOperatorSource : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "mathlib v4.28.0, LinearMap.lTensor/rTensor"
  claim := "Supplies the tensor extension operators and pure-tensor evaluation rules used in the locality decomposition."

def dashiOperatorLocalityReconstructionReceipt : AttributionReceipt where
  role := .localFormalReconstruction
  owner := "DASHI"
  claim := "Defines exact local-left + local-right + interaction decomposition relative to a declared inner-product TPS and proves its pure-tensor action; no external source is credited with this DASHI packaging theorem."

end QuantumMereology
