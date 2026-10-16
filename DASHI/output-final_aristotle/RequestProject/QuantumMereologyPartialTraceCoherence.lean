import RequestProject.QuantumMereologyFiniteNChartedAtlas

/-!
# Finite partial-trace coherence

For a finite three-factor carrier `(A × B) × C`, tracing `C` and then `B`
must agree with first reassociating the same matrix to `A × (B × C)` and
tracing the combined environment `B × C` once.

This module proves that reusable finite-sum law directly.  It removes ordinary
product reassociation/trace order as a blocker, but it does not by itself prove
the dependent-subset coherence theorem for the heterogeneous finite atlas; that
still requires transporting arbitrary subset/complement coordinate splits to
this product law.
-/

namespace QuantumMereology
namespace PartialTraceCoherence

variable
  {A B C : Type*}
  [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- Explicit reassociation of the same finite basis carrier. -/
def reassoc : ((A × B) × C) ≃ (A × (B × C)) where
  toFun x := (x.1.1, (x.1.2, x.2))
  invFun x := ((x.1, x.2.1), x.2.2)
  left_inv x := by rcases x with ⟨⟨a, b⟩, c⟩; rfl
  right_inv x := by rcases x with ⟨a, ⟨b, c⟩⟩; rfl

/-- Reassociate a three-factor density matrix without changing its entries. -/
noncomputable def reassociated
    (rho : Matrix ((A × B) × C) ((A × B) × C) ℂ) :
    Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  Matrix.reindex reassoc reassoc rho

/-- Trace `C`, then trace `B`. -/
def iteratedTrace
    (rho : Matrix ((A × B) × C) ((A × B) × C) ℂ) :
    Matrix A A ℂ :=
  ReducedState.partialTraceRight (ReducedState.partialTraceRight rho)

/-- Reassociate once and trace the joint environment `B × C`. -/
noncomputable def jointEnvironmentTrace
    (rho : Matrix ((A × B) × C) ((A × B) × C) ℂ) :
    Matrix A A ℂ :=
  ReducedState.partialTraceRight (reassociated rho)

/-- Finite Fubini/partial-trace associativity on the exact same matrix. -/
theorem iteratedTrace_eq_jointEnvironmentTrace
    (rho : Matrix ((A × B) × C) ((A × B) × C) ℂ) :
    iteratedTrace rho = jointEnvironmentTrace rho := by
  classical
  ext i j
  simp [iteratedTrace, jointEnvironmentTrace, reassociated,
    ReducedState.partialTraceRight, Matrix.reindex_apply,
    Fintype.sum_prod_type]

/-- Density-matrix formulation: both reduction paths are genuine density
matrices and have identical matrix payloads. -/
noncomputable def jointEnvironmentDensity
    (rho : ReducedState.DensityMatrix ((A × B) × C)) :
    ReducedState.DensityMatrix A := by
  classical
  let r : ReducedState.DensityMatrix (A × (B × C)) :=
    FiniteNChartedAtlas.reindexDensity reassoc rho
  exact ReducedState.partialTraceDensityRight r

noncomputable def iteratedDensity
    (rho : ReducedState.DensityMatrix ((A × B) × C)) :
    ReducedState.DensityMatrix A :=
  ReducedState.partialTraceDensityRight
    (ReducedState.partialTraceDensityRight rho)

theorem iteratedDensity_matrix_eq_jointEnvironmentDensity
    (rho : ReducedState.DensityMatrix ((A × B) × C)) :
    (iteratedDensity rho).matrix = (jointEnvironmentDensity rho).matrix := by
  classical
  exact iteratedTrace_eq_jointEnvironmentTrace rho.matrix

structure Boundary where
  iteratedProductPartialTraceAssociativityPaid : Bool := true
  densityMatrixTwoStageReductionCoherencePaid : Bool := true
  dependentSubsetCoherenceAutomaticallyPaid : Bool := false
  physicalSubsystemIdentificationCreated : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem iterated_product_partial_trace_associativity_paid :
    canonicalBoundary.iteratedProductPartialTraceAssociativityPaid = true := rfl

theorem dependent_subset_coherence_not_automatic :
    canonicalBoundary.dependentSubsetCoherenceAutomaticallyPaid = false := rfl

/-- DASHI theorem receipt. -/
def dashiPartialTraceCoherenceReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "Proves by finite-sum expansion that tracing C and then B from one matrix on (A×B)×C equals reassociating the same matrix to A×(B×C) and tracing B×C once; lifts the equality to density-matrix reductions. This does not by itself pay arbitrary dependent-subset coherence or physical subsystem identity."

end PartialTraceCoherence
end QuantumMereology
