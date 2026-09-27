import RequestProject.QuantumMereologyFiniteLinearTPS
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Bipartite inner-product tensor-product structures

This strengthens the preceding complex-linear TPS by requiring the reconstruction
map to preserve the tensor-product inner product.

Mathlib v4.28.0 supplies the algebraic tensor product's norm and inner-product
instances and the canonical isometric tensor maps. DASHI owns the packaging and
the transport theorems below.

Important boundary: mathlib's tensor-product file explicitly treats the
algebraic tensor product and lists completion as a separate TODO in general.
This module therefore says "inner-product TPS", not "completed Hilbert TPS".
No Hamiltonian locality, decoherence, preferred factorisation, or physical
subsystem identity follows from the isometry.
-/

namespace QuantumMereology

open scoped TensorProduct

structure BipartiteInnerProductTPS
    (H Left Right : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Left] [InnerProductSpace ℂ Left]
    [NormedAddCommGroup Right] [InnerProductSpace ℂ Right] where
  reconstruct : TensorProduct ℂ Left Right ≃ₗᵢ[ℂ] H

namespace BipartiteInnerProductTPS

variable
  {H Left Right : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Left] [InnerProductSpace ℂ Left]
  [NormedAddCommGroup Right] [InnerProductSpace ℂ Right]

/-- Forgetting the metric structure yields the previously defined linear TPS. -/
def toLinearTPS
    (T : BipartiteInnerProductTPS H Left Right) :
    BipartiteLinearTPS H Left Right where
  reconstruct := T.reconstruct.toLinearEquiv

/-- Reconstruction preserves the tensor-product inner product. -/
@[simp] theorem inner_reconstruct
    (T : BipartiteInnerProductTPS H Left Right)
    (x y : TensorProduct ℂ Left Right) :
    inner ℂ (T.reconstruct x) (T.reconstruct y) = inner ℂ x y :=
  T.reconstruct.inner_map_map x y

/-- Reconstruction preserves norm. -/
@[simp] theorem norm_reconstruct
    (T : BipartiteInnerProductTPS H Left Right)
    (x : TensorProduct ℂ Left Right) :
    ‖T.reconstruct x‖ = ‖x‖ :=
  T.reconstruct.norm_map x

/-- The dimension-product theorem survives the stronger inner-product carrier. -/
theorem finrank_product
    (T : BipartiteInnerProductTPS H Left Right) :
    Module.finrank ℂ H =
      Module.finrank ℂ Left * Module.finrank ℂ Right :=
  BipartiteLinearTPS.finrank_product T.toLinearTPS

/-- Canonical scalar-left isometric presentation. It is a structural sanity
witness only, not a preferred decomposition. -/
noncomputable def scalarLeft
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    BipartiteInnerProductTPS H ℂ H where
  reconstruct := TensorProduct.lidIsometry ℂ H

structure InnerProductTPSBoundary where
  innerProductTPSIsCompletedHilbertTensorProduct : Bool := false
  innerProductTPSProvesHamiltonianLocality : Bool := false
  innerProductTPSProvesDecoherenceCriterion : Bool := false
  innerProductTPSSelectsPreferredFactorisation : Bool := false
  innerProductTPSIdentifiesPhysicalSubsystems : Bool := false
deriving Repr, DecidableEq

def canonicalInnerProductTPSBoundary : InnerProductTPSBoundary := {}

theorem metric_reconstruction_does_not_select_preferred_factorisation :
    canonicalInnerProductTPSBoundary.innerProductTPSSelectsPreferredFactorisation = false := rfl

theorem metric_reconstruction_does_not_prove_hamiltonian_locality :
    canonicalInnerProductTPSBoundary.innerProductTPSProvesHamiltonianLocality = false := rfl

end BipartiteInnerProductTPS

def mathlibInnerProductTensorTheoremSource : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "mathlib v4.28.0, Mathlib.Analysis.InnerProductSpace.TensorProduct"
  claim := "Supplies the tensor-product inner product and norm plus TensorProduct.lidIsometry and LinearIsometryEquiv inner-product preservation used by the DASHI inner-product TPS carrier."

def dashiInnerProductTPSTheoremReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI"
  claim := "BipartiteInnerProductTPS packages a tensor reconstruction as a complex linear isometric equivalence and proves its forgetful linear-TPS, inner-product, norm, and dimension transports without claiming physical preference."

end QuantumMereology
