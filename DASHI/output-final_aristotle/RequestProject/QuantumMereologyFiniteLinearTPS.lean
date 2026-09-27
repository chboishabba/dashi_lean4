import RequestProject.QuantumMereologySelection
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite linear tensor-product structures

This is the first concrete tensor-product carrier in the quantum-mereology lane.

A bipartite linear TPS is only a complex-linear equivalence

    H_L ⊗[ℂ] H_R ≃ₗ[ℂ] H.

That is enough to derive the finite-dimensional product law for dimensions.
It is deliberately weaker than a Hilbert-space tensor decomposition: no inner
product preservation, completed Hilbert tensor product, Hamiltonian locality,
entanglement dynamics, quasiclassical preference, or physical subsystem identity
is inferred here.

The tensor-product and finrank theorems are mathlib theorem sources. The
specialisation to this DASHI TPS carrier is a new DASHI theorem.
-/

namespace QuantumMereology

open scoped TensorProduct

structure BipartiteLinearTPS
    (H Left Right : Type*)
    [AddCommGroup H] [Module ℂ H]
    [AddCommGroup Left] [Module ℂ Left]
    [AddCommGroup Right] [Module ℂ Right] where
  reconstruct : TensorProduct ℂ Left Right ≃ₗ[ℂ] H

namespace BipartiteLinearTPS

variable
  {H Left Right : Type*}
  [AddCommGroup H] [Module ℂ H]
  [AddCommGroup Left] [Module ℂ Left]
  [AddCommGroup Right] [Module ℂ Right]

/-- A concrete linear TPS forces the ambient finite dimension to factor as the
product of the two factor dimensions. -/
theorem finrank_product
    (T : BipartiteLinearTPS H Left Right) :
    Module.finrank ℂ H =
      Module.finrank ℂ Left * Module.finrank ℂ Right := by
  rw [← T.reconstruct.finrank_eq, Module.finrank_tensorProduct]

/-- The scalar factor gives the canonical degenerate bipartite presentation.
This is a structural sanity witness, not a preferred or physical decomposition. -/
noncomputable def scalarLeft (H : Type*) [AddCommGroup H] [Module ℂ H] :
    BipartiteLinearTPS H ℂ H where
  reconstruct := TensorProduct.lid ℂ H

@[simp] theorem scalarLeft_finrank
    (H : Type*) [AddCommGroup H] [Module ℂ H] :
    Module.finrank ℂ H =
      Module.finrank ℂ ℂ * Module.finrank ℂ H :=
  finrank_product (scalarLeft H)

/-! ## Promotion firewall -/

structure LinearTPSBoundary where
  linearEquivalenceIsHilbertIsometry : Bool := false
  linearTPSProvesHamiltonianLocality : Bool := false
  linearTPSDefinesPhysicalSubsystems : Bool := false
  linearTPSIsQuasiclassicallyPreferred : Bool := false
  dimensionProductSelectsUniqueTPS : Bool := false
deriving Repr, DecidableEq

def canonicalLinearTPSBoundary : LinearTPSBoundary := {}

theorem linear_equivalence_not_promoted_to_hilbert_isometry :
    canonicalLinearTPSBoundary.linearEquivalenceIsHilbertIsometry = false := rfl

theorem dimension_product_does_not_select_unique_tps :
    canonicalLinearTPSBoundary.dimensionProductSelectsUniqueTPS = false := rfl

end BipartiteLinearTPS

/-! ## Attribution receipts -/

def mathlibTensorProductTheoremSource : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "mathlib v4.28.0"
  claim := "TensorProduct.lid, LinearEquiv.finrank_eq, and Module.finrank_tensorProduct supply the machine-formal linear tensor-product and dimension facts consumed by this module."

def dashiFiniteLinearTPSTheoremReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI"
  claim := "BipartiteLinearTPS.finrank_product specialises mathlib's tensor-product finrank theorem to the DASHI finite linear TPS carrier; it does not promote the carrier to a physical Hilbert-space decomposition."

end QuantumMereology
