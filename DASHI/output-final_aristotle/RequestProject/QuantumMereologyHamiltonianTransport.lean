import RequestProject.QuantumMereologyOperatorLocality
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Symmetric Hamiltonian-candidate transport through a TPS

A physical finite-dimensional Hamiltonian is represented here only at the
operator-theoretic level: a symmetric complex-linear endomorphism. The crucial
same-object theorem is that the isometric TPS coordinate change preserves
symmetry.

This module does not identify any particular operator with a measured physical
Hamiltonian and does not infer preferred factorisation from symmetry/locality.
-/

namespace QuantumMereology

open scoped TensorProduct

namespace HamiltonianTransport

variable
  {H Left Right : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Left] [InnerProductSpace ℂ Left]
  [NormedAddCommGroup Right] [InnerProductSpace ℂ Right]

/-- Symmetry/self-adjointness in the inner-product sense is invariant under the
isometric TPS coordinate change. -/
theorem pullback_isSymmetric_iff
    (T : BipartiteInnerProductTPS H Left Right)
    (A : H →ₗ[ℂ] H) :
    (OperatorLocality.pullback T A).IsSymmetric ↔ A.IsSymmetric := by
  simpa [OperatorLocality.pullback, LinearMap.comp_assoc] using
    (LinearMap.isSymmetric_linearIsometryEquiv_conj_iff
      A T.reconstruct.symm)

/-- A declared local decomposition whose global operator and all three
coordinate pieces are symmetric. This is an operator-level Hamiltonian
candidate receipt, not empirical Hamiltonian authority. -/
structure SymmetricLocalityWitness
    (T : BipartiteInnerProductTPS H Left Right)
    (A : H →ₗ[ℂ] H) where
  locality : OperatorLocality.Witness T A
  globalSymmetric : A.IsSymmetric
  leftSymmetric : locality.leftLocal.IsSymmetric
  rightSymmetric : locality.rightLocal.IsSymmetric
  interactionSymmetric : locality.interaction.IsSymmetric

/-- The same global symmetric operator is symmetric in the selected TPS
coordinates. -/
theorem pullbackSymmetric
    {T : BipartiteInnerProductTPS H Left Right}
    {A : H →ₗ[ℂ] H}
    (W : SymmetricLocalityWitness T A) :
    (OperatorLocality.pullback T A).IsSymmetric :=
  (pullback_isSymmetric_iff T A).2 W.globalSymmetric

structure Boundary where
  symmetricOperatorIsEmpiricallyMeasuredHamiltonian : Bool := false
  symmetricLocalitySelectsPreferredTPS : Bool := false
  symmetricLocalityProvesQuasiclassicalDynamics : Bool := false
  symmetricLocalityProvesSmallEntanglementGrowth : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem symmetric_locality_not_empirical_hamiltonian_authority :
    canonicalBoundary.symmetricOperatorIsEmpiricallyMeasuredHamiltonian = false := rfl

theorem symmetric_locality_does_not_select_preferred_tps :
    canonicalBoundary.symmetricLocalitySelectsPreferredTPS = false := rfl

end HamiltonianTransport

def mathlibSymmetricConjugationTheoremSource : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "mathlib v4.28.0, LinearMap.isSymmetric_linearIsometryEquiv_conj_iff"
  claim := "Supplies invariance of symmetric linear operators under linear-isometric coordinate conjugation."

def dashiHamiltonianTransportTheoremReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI"
  claim := "Specialises mathlib's symmetric-conjugation theorem to the same BipartiteInnerProductTPS used by quantum mereology and packages symmetric local-left/local-right/interaction decomposition without empirical Hamiltonian promotion."

end QuantumMereology
